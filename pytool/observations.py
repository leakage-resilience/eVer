# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from __future__ import annotations

from dataclasses import dataclass, field
from itertools import combinations
from math import comb
import networkx as nx
from sage.rings.polynomial.multi_polynomial import MPolynomial
from rewrite_rules import RewriteRule
from security import is_t_non_interferent_poly, SecurityNotion
from typing import Callable, Iterable, Optional, Sequence, Set


def _frobenius_mpoly_square(p):
    """
    Efficient squaring in GF2k using frobenius endomorphism.
    """
    R = p.parent()
    d = p.dict()

    # In characteristic 2: (sum a_i x_i)^2 = sum (a_i^2) (x_i^2)

    out = {}
    for mon, coeff in d.items():
        mon2 = tuple(e << 1 for e in mon)  # multiply exponents by 2
        c2 = coeff * coeff  # coefficient square in base ring
        if c2:  # skip zeros
            out[mon2] = c2

    return R(out)


def _try_defactor_obs(obs: Observation) -> bool:
    """
    This rewrite attempts to find observations e = f * e', where f is a public factor only depending on parameter variables, i.e. no secrets, publics or randoms.
    If such a factor is found, e is substituted by e', since f is public.
    This can lead to false negatives since there might be cases where, depending on f = 0, e is secret independent whereas e' is not.
    Mutates original observation.
    """
    ov = obs.get_value()
    f = None
    success = False
    for c in ov.dict().values():
        if hasattr(c, "numerator"):
            num = c.numerator()
        else:
            num = c
        f = num if f is None else f.gcd(num)
        # early abort
        if f.is_one():
            break

    if f is not None and not f.is_one() and f != 0:
        # divide out f from the whole polynomial
        obs_defactored = ov / f
        obs.value = obs_defactored
        success = True
    return success


def _preprocess_safe_destruct(
    observations: Sequence[Observation],
    log: bool = False,
) -> bool:
    """
    Try to apply a safe destruct, in case that this reduces to a tuple of size <= t, we can return True to indicate that a different tuple covers the current one due to enumeration.
    If the tuple is large we return its safe destruct result additionally. Should no rewrite be possible we return the original observations.
    """
    current_obs_ids = set(o.get_id() for o in observations)
    if log:
        print("try to apply safe destruct rule")
    for obs in observations:
        parent_ids = set(obs.get_parents())
        if obs.get_id() in parent_ids:
            raise RuntimeError(
                "An observation is its own parent, something went very wrong. Abort verification!"
            )
        if len(parent_ids & current_obs_ids) >= len(
            parent_ids
        ) - 1 or parent_ids.issubset(current_obs_ids):
            if log:
                print(
                    f"Safe destruct successful with deferred obsset on obs {obs} with parents {parent_ids} "
                )
            return True

    # could'nt do anything
    return False


def _preprecess_FDedup(
    observations: Sequence[Observation],
    log: bool = False,
) -> bool:
    """
    This rewrite attempts to find observations s.t. obs2 = f * obs1, where f is a factor only depending on parameter variables, i.e. no secrets, publics or randoms.
    If such a factor is found, obs2 is substituted by f, since the leakage of obs1 is already captured in the rest of the tuple.
    """
    n = len(observations)
    # try all pairs of observations without considering order, i.e. try (obs1, obs2), but not (obs2, obs1)
    for i in range(n):
        obs1 = observations[i]
        for j in range(i + 1, n):
            obs2 = observations[j]
            if obs1.get_depset() != obs2.get_depset():
                continue
            # get monomial representation
            poly1 = obs1.get_value().dict()
            poly2 = obs2.get_value().dict()
            # different number of monomials means cant be e2 != e1 * f
            if len(poly1) != len(poly2):
                continue

            is_factor = True
            factor = None
            for i, (monomial1, monomial2) in enumerate(
                zip(poly1.items(), poly2.items())
            ):
                exp1, coeff1 = monomial1
                exp2, coeff2 = monomial2
                if exp1 != exp2:
                    is_factor = False
                    break
                if i == 0:
                    # not sure if monomials can have zero factors, check to be safe
                    if coeff1 == 0:
                        is_factor = False
                        break
                    # compute c2 = c1 * f
                    factor = coeff2 / coeff1
                else:
                    # check if the factor holds for all remaining monomials
                    if coeff2 / coeff1 != factor:
                        is_factor = False
                        break

            if is_factor and factor is not None:
                if log:
                    print(
                        "FDedup successful in preprocessing. Deferring tuple."
                    )
                return True

    return False


@dataclass(frozen=True)
class Location:
    """
    Represents a position in a source file or algorithm.

    Attributes:
        filename:       Path to the source file.
        lineno:         1-based line number.
        description:    Additional description.
        caller:         Location to compose with.

    Example: SourceLocation("optZenc", "1", "initalization")
                -> "initalization at line 1 of optZenc"
    """

    filename: str
    lineno: Optional[int] = None
    description: Optional[str] = None
    caller: Optional[Location] = None

    def __post_init__(self):
        if not isinstance(self.filename, str):
            raise TypeError(
                f"filename must be str, got {type(self.filename).__name__}"
            )
        if self.lineno is not None and (
            not isinstance(self.lineno, int) or self.lineno < 1
        ):
            raise TypeError("lineno must be a positive int")
        if self.description is not None and not isinstance(
            self.description, str
        ):
            raise TypeError(
                f"description must be a str, got {type(self.description).__name__}"
            )
        if self.caller is not None and not isinstance(self.caller, Location):
            raise TypeError(
                f"other must be a Location, got {type(self.caller).__name__}"
            )

    def __str__(self) -> str:
        if self.description is None:
            if self.lineno is None:
                locstr = f"{self.filename}"
            else:
                locstr = f"line {self.lineno} of {self.filename}"
        else:
            if self.lineno is None:
                locstr = f"{self.description} in {self.filename}"
            else:
                locstr = f"{self.description} at line {self.lineno} of {self.filename}"
        if self.caller is None:
            return locstr
        else:
            return f"{locstr} in {self.caller}"


@dataclass(frozen=False)
class Observation:
    """
    Encapsulates an observation within a gadget or encoding as.
    multivariate polynomial, together with its parent observations
    and source location.

    Attributes:
        value:    The MPolynomial value corresponding to the observation.
        parents:  List of indices (ints) referring to parent Observations in `ObservationGraph`.
        location: Location where this observation was generated.
    """

    value: MPolynomial
    id: int = -1
    parents: tuple[int, ...] = field(default_factory=tuple)
    location: Optional[Location] = None
    applied_rules: list[RewriteRule] = field(default_factory=list)
    depset: Set[MPolynomial] = field(
        init=False, repr=False, default_factory=set
    )

    def __post_init__(self):
        if not isinstance(self.value, MPolynomial):
            raise TypeError(
                f"value must be a sage MPolynomial, got {type(self.value).__name__}"
            )
        if not isinstance(self.parents, tuple) or not all(
            isinstance(p, int) for p in self.parents
        ):
            raise TypeError(
                f"parents must be a Tuple[int], got {type(self.parents).__name__}"
            )
        if self.location is not None and not isinstance(
            self.location, Location
        ):
            raise TypeError("location must be a Location instance")
        # compute depset once on creation
        self.depset = set(self.value.variables())

    def print(
        self,
        id: bool = True,
        value: bool = True,
        parents: bool = True,
        applied_rules: bool = True,
        loc: bool = True,
        depset: bool = False,
    ) -> str:
        lines = ["Observation("]

        if id:
            lines.append(f"  id            = {self.id},")
        if value:
            lines.append(f"  value         = {self.value},")
        if parents:
            parents_str = (
                ", ".join(str(p) for p in self.parents)
                if self.parents
                else "none"
            )
            lines.append(f"  parents       = [{parents_str}],")
        if applied_rules:
            applied_rules_str = (
                ",\n                   ".join(
                    str(r) for r in self.applied_rules
                )
                if self.applied_rules
                else "none"
            )
            lines.append(f"  applied_rules = [{applied_rules_str}],")
        if loc:
            loc_str = "none" if self.location is None else self.location
            lines.append(f"  loc           = {loc_str}")
        if depset:
            vars_strs = [str(v) for v in self.get_value().variables()]
            vars_strs.sort()
            depset_str = (
                ", ".join(str(v) for v in vars_strs) if vars_strs else "none"
            )
            lines.append(f"  depset        = {depset_str}")

        lines.append(")")
        return "\n".join(lines)

    def __str__(self) -> str:
        return self.print()

    def __eq__(self, other):
        if not isinstance(other, Observation):
            return NotImplemented
        return (
            self.value == other.value
            and self.id == other.id
            and self.parents == other.parents
            and self.location == other.location
        )

    def __hash__(self):
        if self.id != -1:
            return self.id
        else:
            raise ValueError(
                f"cannot hash Observation without unique id: {self}."
            )

    def get_id(self) -> int:
        return self.id

    def get_value(self) -> MPolynomial:
        return self.value

    def get_parents(self) -> tuple[int, ...]:
        return self.parents

    def get_location(self) -> Optional[Location]:
        return self.location

    def get_depset(self) -> Set[MPolynomial]:
        return self.depset

    def rewrite(self, value: MPolynomial, rrule: RewriteRule) -> Observation:
        """
        Apply a rewrite rule by generating a new observation equivalent to the rewrite.
        """
        return Observation(
            value,
            self.id,
            self.parents,
            self.location,
            self.applied_rules + [rrule],
        )


@dataclass(frozen=False)
class ObservationGraph:
    """
    Store a set of observations using NetworkX graphs.

    The observations are concurrently recorded as in NI terminology (shares are symbols)
    as well as PS terminology (shares are expressions over random variables and secrets).
    Each graph stores observations as node attributes with directed edges from parents to children.
    """

    ni_graph: nx.DiGraph = field(
        default_factory=nx.DiGraph
    )  # NI observations as NetworkX graph
    ps_graph: nx.DiGraph = field(
        default_factory=nx.DiGraph
    )  # PS observations as NetworkX graph
    ids: set[int] = field(default_factory=set)
    uid_ctr: int = 0

    def __get_id(self) -> int:
        uid = self.uid_ctr
        self.uid_ctr += 1
        while uid in self.ids:
            uid = self.uid_ctr
            self.uid_ctr += 1
        return uid

    def add(self, ni_obs: Observation, ps_obs: Observation):
        """Add observations to the ObservationGraph."""
        if not isinstance(ni_obs, Observation):
            raise TypeError(
                f"ni_obs must be an Observation, got {type(ni_obs).__name__}"
            )
        if not isinstance(ps_obs, Observation):
            raise TypeError(
                f"ps_obs must be an Observation, got {type(ps_obs).__name__}"
            )
        if ni_obs.get_id() != ps_obs.get_id():
            raise ValueError(
                "id of NI-Observation and PS-Observation must match."
            )
        uid = ni_obs.get_id()
        if uid in self.ids:
            raise ValueError(
                "id of Observation already associated in the ObservationGraph."
            )
        if not set(ni_obs.get_parents()).issubset(self.ids):
            raise ValueError(
                f"NI-Observation contains parents not in the ObservationGraph.\nObservation {ni_obs}\n{self}."
            )
        if not set(ps_obs.get_parents()).issubset(self.ids):
            raise ValueError(
                f"PS-Observation contains parents not in the ObservationGraph.\nObservation {ps_obs}\n{self}."
            )

        # Add nodes to NetworkX graphs with observation as attribute
        self.ni_graph.add_node(uid, observation=ni_obs)
        self.ps_graph.add_node(uid, observation=ps_obs)

        # Add edges from parents to this node
        for parent_id in ni_obs.get_parents():
            self.ni_graph.add_edge(parent_id, uid)  # parent -> child
            self.ps_graph.add_edge(parent_id, uid)  # parent -> child
        self.ids.add(uid)

    def mk_obs(
        self,
        ni_val: MPolynomial,
        ps_val: MPolynomial,
        parents: Sequence[int],
        location: Optional[Location] = None,
    ) -> tuple[Observation, Observation]:
        """Create NI- and PS-observations and add them to the ObservationGraph."""
        if not isinstance(ni_val, MPolynomial):
            raise TypeError(
                f"ni_val must be MPolynomial, got {type(ni_val).__name__}"
            )
        if not isinstance(ps_val, MPolynomial):
            raise TypeError(
                f"ps_val must be MPolynomial, got {type(ps_val).__name__}"
            )
        if not isinstance(parents, list) or not all(
            isinstance(p, int) for p in parents
        ):
            raise TypeError("parents must be a List[int]")
        if location is not None and not isinstance(location, Location):
            raise TypeError(
                f"location must be SourceLocation, got {type(location).__name__}"
            )
        uid = self.__get_id()
        if not set(parents).issubset(self.ids):
            raise ValueError(
                f"Parents {parents} not in the ObservationGraph.\n{self}."
            )
        ni_obs = Observation(ni_val, uid, tuple(parents), location)
        ps_obs = Observation(ps_val, uid, tuple(parents), location)

        # Add nodes to NetworkX graphs with observation as attribute
        self.ni_graph.add_node(uid, observation=ni_obs)
        self.ps_graph.add_node(uid, observation=ps_obs)

        # Add edges from parents to this node
        for parent_id in parents:
            self.ni_graph.add_edge(parent_id, uid)  # parent -> child
            self.ps_graph.add_edge(parent_id, uid)  # parent -> child

        self.ids.add(uid)
        return (ni_obs, ps_obs)

    def __len__(self) -> int:
        """Return the count of stored observations."""
        if (
            len(self.ni_graph.nodes)
            != len(self.ps_graph.nodes)
            != len(self.ids)
        ):
            raise ValueError("IDs, NI and PS node counts diverge.")
        return len(self.ni_graph.nodes)

    def get_ids(self) -> set[int]:
        return self.ids

    def get_ni_observation(self, id: int) -> Observation:
        """
        Return the observation corresponding to `id` encoded as in
        NI terminology (shares are symbols).
        """
        try:
            return self.ni_graph.nodes[id]["observation"]
        except KeyError:
            raise ValueError(
                f"No NI-observation with id {id} in ObservationGraph."
            )

    def get_ps_observation(self, id: int) -> Observation:
        """
        Return the observation corresponding to `id` encoded as in PS terminology
        (shares are expressions over random variables and secrets)
        """
        try:
            return self.ps_graph.nodes[id]["observation"]
        except KeyError:
            raise ValueError(
                f"No PS-observation with id {id} in ObservationGraph."
            )

    def get_observation(self, notion: SecurityNotion, id: int) -> Observation:
        """
        Return the observation corresponding to `id` encoded accordingly to `notion`.
        """
        if notion == SecurityNotion.PS:
            return self.get_ps_observation(id)
        elif notion == SecurityNotion.NI or notion == SecurityNotion.SNI:
            return self.get_ni_observation(id)
        else:
            raise NotImplementedError()

    def get_ni_observations(self) -> Iterable[tuple[int, Observation]]:
        """Return the observations encoded as in NI terminology (shares are symbols)."""
        return (
            (node_id, data["observation"])
            for node_id, data in self.ni_graph.nodes(data=True)
        )

    def get_ps_observations(self) -> Iterable[tuple[int, Observation]]:
        """
        Return the observations encoded as in PS terminology
        (shares are expressions over random variables and secrets).
        """
        return (
            (node_id, data["observation"])
            for node_id, data in self.ps_graph.nodes(data=True)
        )

    def get_observations(
        self, notion: SecurityNotion
    ) -> Iterable[tuple[int, Observation]]:
        """
        Return the observations encoded accordingly to `notion`.
        """

        if notion == SecurityNotion.PS:
            return self.get_ps_observations()
        elif notion == SecurityNotion.NI or notion == SecurityNotion.SNI:
            return self.get_ni_observations()
        else:
            raise NotImplementedError()

    def _get_graph(self, notion: SecurityNotion) -> nx.DiGraph:
        """Helper method to get the appropriate graph based on security notion."""
        if notion == SecurityNotion.PS:
            return self.ps_graph
        elif notion == SecurityNotion.NI or notion == SecurityNotion.SNI:
            return self.ni_graph
        else:
            raise NotImplementedError(f"Security notion {notion} not supported")

    def defactor_graph(self, notion: SecurityNotion, log: bool = False) -> int:
        ctr = 0
        graph = self._get_graph(notion)
        for _, data in graph.nodes(data=True):
            if _try_defactor_obs(data["observation"]):
                ctr += 1
        return ctr

    def is_descendant(
        self, descendant: int, parent: int, notion: SecurityNotion
    ) -> bool:
        """
        Check if `descendant` is a descendant of `parent` by checking if
        there is a path from parent to descendant in the graph.
        """
        if descendant not in self.ids or parent not in self.ids:
            return False
        graph = self._get_graph(notion)
        return nx.has_path(graph, parent, descendant)

    def shortest_path(
        self, descendant: int, to_id: int, notion: SecurityNotion
    ) -> list[int]:
        """
        Find the shortest path from `descendant` to to_id in the specified graph,
        assuming that `to_id` is a parent or a parent of parents of `descendant`.
        """
        if descendant not in self.ids:
            raise ValueError(
                f"Source node {descendant} not in ObservationGraph"
            )
        if to_id not in self.ids:
            raise ValueError(f"Target node {to_id} not in ObservationGraph")
        graph = self._get_graph(notion)
        try:
            path = nx.shortest_path(graph, descendant, to_id)
            return list(path)  # Ensure we return a list[int]
        except nx.NetworkXNoPath:
            return []

    def __str__(self) -> str:
        """
        Show a side-by-side listing of NI vs PS observations,
        keyed by UID.
        """
        lines = ["ObservationGraph:"]
        for id in sorted(self.ids):
            ni = self.ni_graph.nodes[id]["observation"]
            ps = self.ps_graph.nodes[id]["observation"]
            lines.append(f"  [{id}] NI: {ni}")
            lines.append(f"  [{id}] PS: {ps}")
        return "\n".join(lines)


class ObservableValue:
    """
    Datastructure to trace computations and the leaking values observable by a probing adversary.

    Operations between two ObservableValues have the following properties:
    - The observations are concurrently recorded as in NI terminology (shares are symbols)
      as well as PS terminology (shares are expressions over random variables and secrets).
    - Both the encoded and symbolic results are stored in an ObservationGraph.
    - The ObservationGraph are references, meaning that if all ObservableValues share the same ObservationGraph they will trace all performed operations.
    """

    ni_obs: Observation
    ps_obs: Observation
    obsgraph: ObservationGraph

    def __init__(
        self,
        obsgraph: ObservationGraph,
        ni_obs: Observation,
        ps_obs: Observation,
    ):
        if not isinstance(obsgraph, ObservationGraph):
            raise TypeError(
                f"obsgraph must be an ObservationGraph, got {type(obsgraph).__name__}."
            )
        if not isinstance(ni_obs, Observation) or not isinstance(
            ps_obs, Observation
        ):
            raise TypeError(
                "ni_obs and ps_obs must both be Observation instances."
            )
        if ni_obs.get_id() != ps_obs.get_id():
            raise ValueError(
                "id of NI-Observation and PS-Observation must match."
            )
        if ni_obs.get_id() not in obsgraph.get_ids():
            raise ValueError(
                f"Id {ni_obs.get_id()} of observation {ni_obs}\nnot known in {obsgraph}."
            )

        self.obsgraph = obsgraph
        self.ni_obs = ni_obs
        self.ps_obs = ps_obs

    def __add__(self, other, loc: Optional[Location] = None):
        if not isinstance(other, ObservableValue):
            raise TypeError(
                "Unsupported operand type(s) for +: 'ObservableValue' and '{}'".format(
                    type(other).__name__
                )
            )
        # compute new values
        ni_val = self.ni_obs.get_value() + other.ni_obs.get_value()
        ps_val = self.ps_obs.get_value() + other.ps_obs.get_value()
        # new parents are the two operand IDs
        parents = [self.ni_obs.get_id(), other.ni_obs.get_id()]
        # record into the graph
        ni_obs, ps_obs = self.obsgraph.mk_obs(ni_val, ps_val, parents, loc)
        return ObservableValue(self.obsgraph, ni_obs, ps_obs)

    def __iadd__(self, other, loc: Optional[Location] = None):
        result = self.__add__(other, loc)
        self.ni_obs, self.ps_obs = result.ni_obs, result.ps_obs
        return self

    def __sub__(self, other, loc: Optional[Location] = None):
        if not isinstance(other, ObservableValue):
            raise TypeError(
                "Unsupported operand type(s) for -: 'ObservableValue' and '{}'".format(
                    type(other).__name__
                )
            )
        # compute new values
        ni_val = self.ni_obs.get_value() - other.ni_obs.get_value()
        ps_val = self.ps_obs.get_value() - other.ps_obs.get_value()
        # new parents are the two operand IDs
        parents = [self.ni_obs.get_id(), other.ni_obs.get_id()]
        # record into the graph
        ni_obs, ps_obs = self.obsgraph.mk_obs(ni_val, ps_val, parents, loc)
        return ObservableValue(self.obsgraph, ni_obs, ps_obs)

    def __isub__(self, other, loc: Optional[Location] = None):
        result = self.__sub__(other, loc)
        self.ni_obs, self.ps_obs = result.ni_obs, result.ps_obs
        return self

    def __mul__(self, other, loc: Optional[Location] = None):
        if not isinstance(other, ObservableValue):
            raise TypeError(
                "Unsupported operand type(s) for -: 'ObservableValue' and '{}'".format(
                    type(other).__name__
                )
            )

        # compute new values
        ni_val = self.ni_obs.get_value() * other.ni_obs.get_value()
        ps_val = self.ps_obs.get_value() * other.ps_obs.get_value()
        # new parents are the two operand IDs
        parents = [self.ni_obs.get_id(), other.ni_obs.get_id()]
        # record into the graph
        ni_obs, ps_obs = self.obsgraph.mk_obs(ni_val, ps_val, parents, loc)
        return ObservableValue(self.obsgraph, ni_obs, ps_obs)

    def __imul__(self, other, loc: Optional[Location] = None):
        result = self.__mul__(other, loc)
        self.ni_obs, self.ps_obs = result.ni_obs, result.ps_obs
        return self

    def __truediv__(self, other, loc: Optional[Location] = None):
        if not isinstance(other, ObservableValue):
            raise TypeError(
                "Unsupported operand type(s) for /: 'ObservableValue' and '{}'".format(
                    type(other).__name__
                )
            )
        # compute new values
        ni_val = self.ni_obs.get_value() / other.ni_obs.get_value()
        ps_val = self.ps_obs.get_value() / other.ps_obs.get_value()
        # new parents are the two operand IDs
        parents = [self.ni_obs.get_id(), other.ni_obs.get_id()]
        # record into the graph
        ni_obs, ps_obs = self.obsgraph.mk_obs(ni_val, ps_val, parents, loc)
        return ObservableValue(self.obsgraph, ni_obs, ps_obs)

    def __itruediv__(self, other, loc: Optional[Location] = None):
        result = self.__truediv__(other, loc)
        self.ni_obs, self.ps_obs = result.ni_obs, result.ps_obs
        return self

    def square(self, loc: Optional[Location] = None):
        ni = self.ni_obs.get_value()
        ps = self.ps_obs.get_value()

        ni2 = ni**2
        ps2 = ps**2

        parents = [self.ni_obs.get_id()]
        ni_obs, ps_obs = self.obsgraph.mk_obs(ni2, ps2, parents, loc)
        return ObservableValue(self.obsgraph, ni_obs, ps_obs)

    def square_GF2k(self, loc: Optional[Location] = None):
        ni = self.ni_obs.get_value()
        ps = self.ps_obs.get_value()

        ni2 = _frobenius_mpoly_square(ni)
        ps2 = _frobenius_mpoly_square(ps)

        parents = [self.ni_obs.get_id()]
        ni_obs, ps_obs = self.obsgraph.mk_obs(ni2, ps2, parents, loc)
        return ObservableValue(self.obsgraph, ni_obs, ps_obs)

    def power(self, exp: int, loc: Optional[Location] = None):
        ni = self.ni_obs.get_value()
        ps = self.ps_obs.get_value()

        ni_exp = ni**exp
        ps_exp = ps**exp

        parents = [self.ni_obs.get_id()]
        ni_obs, ps_obs = self.obsgraph.mk_obs(ni_exp, ps_exp, parents, loc)
        return ObservableValue(self.obsgraph, ni_obs, ps_obs)

    def __str__(self) -> str:
        return (
            f"[uid={self.ni_obs.get_id()}]\n"
            f"  NI: {self.ni_obs.get_value()}\n"
            f"  PS: {self.ps_obs.get_value()}"
        )


class ObservationTupleManager:
    """Handle creation and enumeration of tuples of observations according to a `SecurityNotion`."""

    notion: SecurityNotion
    obsgraph: ObservationGraph
    security_order: int
    secret_vars: Sequence[Set[MPolynomial]]
    internal_observations: Set[int]
    output_observations: Set[int]

    def __init__(
        self,
        obsgraph: ObservationGraph,
        notion: SecurityNotion,
        security_order: int,
        secret_vars: Sequence[Set[MPolynomial]],
        output_observations: set[int],
    ):
        if not isinstance(obsgraph, ObservationGraph):
            raise TypeError(
                f"obsgraph must be an ObservationGraph, got {type(obsgraph).__name__}"
            )
        if not isinstance(notion, SecurityNotion):
            raise TypeError(
                f"notion must be a SecurityNotion, got {type(notion).__name__}"
            )
        if not isinstance(security_order, int) or security_order < 1:
            raise ValueError(
                f"security_order must be a non-negative int, got {security_order!r}"
            )
        if not isinstance(secret_vars, Sequence):
            raise TypeError(
                f"secret_vars must be a Sequence of Set[MPolynomial], got {type(secret_vars).__name__}"
            )
        for idx, s in enumerate(secret_vars):
            if not isinstance(s, set) or not all(
                isinstance(p, MPolynomial) for p in s
            ):
                raise TypeError(
                    f"secret_vars[{idx}] must be a Set[MPolynomial]"
                )
        if not isinstance(output_observations, set) or not all(
            isinstance(i, int) for i in output_observations
        ):
            raise TypeError("output_obs must be a set of ints")
        if not output_observations.issubset(obsgraph.get_ids()):
            raise ValueError(
                "output_obs must be a subset of obsgraph.get_ids()"
            )
        self.skipped_obs_criterion = 0
        self.skipped_obs_safe_destruct = 0
        self.skipped_obs_FDedup = 0

        self.num_defactored_obs = 0
        self.obsgraph = obsgraph
        self.notion = notion
        self.security_order = security_order
        self.secret_vars = secret_vars
        self.output_observations = output_observations
        self.internal_observations = (
            obsgraph.get_ids() - self.output_observations
        )

    def defactor_obsgraph(self, log: bool = False):
        """
        Simplify observations by eliminating common coefficient factors.
        """
        num_obs_pre = len(self.internal_observations) + len(
            self.output_observations
        )
        self.num_tups_pre_defactor = comb(
            num_obs_pre, min(self.security_order, num_obs_pre)
        )
        self.num_defactored_obs = self.obsgraph.defactor_graph(self.notion, log)
        self.filter_duplicate_observations(log)

        if log:
            print(
                f"Defactor succeeded on {self.num_defactored_obs} observations."
            )

    def __get_observation(self, id: int):
        if (
            self.notion == SecurityNotion.NI
            or self.notion == SecurityNotion.SNI
        ):
            return self.obsgraph.get_ni_observation(id)
        if self.notion == SecurityNotion.PS:
            return self.obsgraph.get_ps_observation(id)
        else:
            raise NotImplementedError()

    def filter_public_observations(self, public_vars, log: bool = False):
        """Remove observations which are constants or have variables in `public_vars` only."""
        num_filtered = 0
        seen_variables = set()
        publics = set()

        for id in self.internal_observations | self.output_observations:
            obs = self.__get_observation(id)
            obs_vars = set(obs.get_value().variables())
            if obs_vars.issubset(public_vars):
                self.internal_observations.remove(id)
                publics.add(id)
                num_filtered += 1
                continue
            else:
                seen_variables.update(obs_vars)

        if log:
            print(
                f"Ignoring {num_filtered} purely public observations from observation set; {len(self.internal_observations) + len(self.output_observations)} remain; ignoring {sorted(publics)}."
            )

        return seen_variables

    def filter_duplicate_observations(self, log: bool = False):
        """Remove duplicate observations with same value but different location."""
        num_filtered = 0
        seen_values = set()
        duplicates = set()

        for id in list(self.internal_observations):
            obs = self.__get_observation(id)
            obs_val = obs.get_value()
            if obs_val in seen_values:
                self.internal_observations.remove(id)
                duplicates.add(id)
                num_filtered += 1
                continue
            else:
                seen_values.add(obs_val)

        if log:
            print(
                f"Ignoring {num_filtered} duplicate observations from observation set; {len(self.internal_observations)} remain; ignoring {sorted(duplicates)}."
            )

    def skip_tuple(self, criterion, obstuple_idx, t, log: bool = False) -> bool:
        tup = [
            self.obsgraph.get_observation(self.notion, idx)
            for idx in obstuple_idx
        ]
        crit_res = criterion(tup, t)
        if crit_res:
            if log:
                print("Criterion already satisfied for obs tuple with obs:")
                for o in tup:
                    print(o)
            self.skipped_obs_criterion += 1
            return True
        if _preprocess_safe_destruct(tup, log):
            self.skipped_obs_safe_destruct += 1
            return True
        if _preprecess_FDedup(tup, log):
            self.skipped_obs_FDedup += 1
            return True

        # nothing worked, need to verify this tuple
        return False

    def get_num_skipped_tuples(self, log: bool = False) -> int:
        if log:
            print(
                f"Skipped {self.skipped_obs_criterion} tuples due to trivial satisfaction of criterion."
            )
            print(
                f"Skipped {self.skipped_obs_safe_destruct} tuples due to deferred enumeration with safe destruct."
            )
            print(
                f"Skipped {self.skipped_obs_FDedup} tuples due to deferred enumeration with FDedup."
            )
        return (
            self.skipped_obs_criterion
            + self.skipped_obs_safe_destruct
            + self.skipped_obs_FDedup
        )

    def obs_tuple_iter(self, log: bool = False):
        """Enumerate tuples for verification based on security notion."""
        num_obs = len(self.internal_observations) + len(
            self.output_observations
        )
        ordered = self.security_order < 4 and num_obs < 300
        num_tuples = comb(num_obs, min(self.security_order, num_obs))

        if self.notion == SecurityNotion.NI or self.notion == SecurityNotion.PS:
            observations = (
                sorted(self.internal_observations | self.output_observations)
                if ordered
                else (self.internal_observations | self.output_observations)
            )
            criterion = self.continuation_criterion()

            def gen():
                for obs_tuple in combinations(
                    observations, min(self.security_order, num_obs)
                ):
                    # Reuse your skipping logic
                    if self.skip_tuple(criterion, obs_tuple, 0, log):
                        continue
                    yield obs_tuple

            return num_tuples, gen()

        elif self.notion == SecurityNotion.SNI:
            # For SNI, we need an iterator that yields tuples with expressions and their local_t value for simulation checking
            all_observations = (
                self.internal_observations | self.output_observations
            )
            observations = (
                sorted(all_observations) if ordered else all_observations
            )
            criterion = self.continuation_criterion()

            # compute the observations on demand using a generator only over iterators
            def sni_tuple_generator():
                """Generator that yields (obs_tuple, local_t) pairs for SNI verification."""
                # use an iterator over tuple combinations
                for obs_tuple in combinations(
                    observations, min(self.security_order, num_obs)
                ):
                    # lazily compute local_t by summing up internal_observations
                    local_t = sum(
                        1
                        for obs_id in obs_tuple
                        if obs_id in self.internal_observations
                    )
                    if self.skip_tuple(criterion, obs_tuple, local_t, log):
                        continue
                    yield (obs_tuple, local_t)

            return (
                num_tuples,
                sni_tuple_generator(),
            )  # call the generator to return an iterator over SNI (obs,t) tuples
        else:
            raise NotImplementedError()

    def continuation_criterion(
        self,
    ) -> Callable[[Sequence[Observation], int], bool]:
        """Returns a function to check whether a tuple of observation satisfies the security notion of this handler."""
        if self.notion == SecurityNotion.NI:
            return lambda obs, _: is_t_non_interferent_poly(
                self.security_order,
                self.secret_vars,
                map(lambda x: x.get_depset(), obs),
            )
        elif self.notion == SecurityNotion.SNI:
            return lambda obs, local_t: is_t_non_interferent_poly(
                local_t, self.secret_vars, map(lambda x: x.get_depset(), obs)
            )
        elif self.notion == SecurityNotion.PS:
            # probing security can be interpreted as using the PS encoded values and the secret variables and showing t=0 NI, meaning indep of secrets for all secrets.
            return lambda obs, _: is_t_non_interferent_poly(
                0, self.secret_vars, map(lambda x: x.get_depset(), obs)
            )
        else:
            raise NotImplementedError()


def mk_obsval(
    obsgraph: ObservationGraph,
    ps_val: MPolynomial,
    ni_val: MPolynomial,
    parents: list[int] = [],
    location: Optional[Location] = None,
) -> ObservableValue:
    ni_obs, ps_obs = obsgraph.mk_obs(ni_val, ps_val, parents, location)
    return ObservableValue(obsgraph, ni_obs, ps_obs)
