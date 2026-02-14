# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from abc import ABC, abstractmethod
import time
import os

from typing import (
    Optional,
    Self,
    Sequence,
    Set,
    TypeVar,
    Generic,
    Any,
    cast,
)
from sage.all import GF, save, load
from sage.rings.ring import CommutativeRing
from ever import verify_security
from sage.rings.polynomial.multi_polynomial import MPolynomial
from observations import Location, ObservationGraph
from security import SecurityNotion
from encoding import Encoding, PolyEnc


# Generic gadget interface
EncType = TypeVar("EncType", bound=Encoding)


class Gadget(ABC, Generic[EncType]):
    def __init__(
        self,
        inputs: Sequence[EncType],
        location: Optional[Location],
        **parameters: Any,
    ):
        """
        inputs: a sequence (e.g., list) of share-vectors, each a sequence of expressions.
        parameters: any extra parameters for adapting the behavior.
        """
        self.inputs = inputs

    @classmethod
    @abstractmethod
    def with_defaults(cls, d: int, k: int, e: int, F) -> Self:
        """Create an instance with default values. Must be implemented by subclasses."""
        pass

    def output(self) -> EncType:
        """
        Return the shares of the sole gadget's output.
        Currently assuming single encoded output, not multiple encoded outputs.
        """
        raise NotImplementedError

    def secret_vars_encoded(self) -> Sequence[Set[MPolynomial]]:
        """
        Return the variables in the gadget which are defined to be secret,
        i.e., with unspecified distribution, with regard to secret values contained in the encoding.
        """
        return [set(i.secrets) for i in self.inputs]

    def secret_vars_symbolic(self) -> Sequence[Set[MPolynomial]]:
        """
        Return the variables in the gadget which are defined to be secret,
        i.e., with unspecified distribution, with regard to secret values contained in the symbolic representation.
        """
        return [set(cast(PolyEnc, i).symbolic_shares) for i in self.inputs]

    def public_vars(self) -> Set[MPolynomial]:
        """
        Return the variables in the gadget which are defined to be public,
        i.e., with unspecified distribution but independent of random and secret variables.
        """
        # By default, no public variables are defined.
        return set()

    def parameter_vars(self) -> Set[MPolynomial]:
        """
        Return the variables used in the gadget and encoding, e.g. support points for polynomial masking and L vector for IPEnc
        """
        return self.output().parameter_vars()

    def random_vars(self) -> Set[MPolynomial]:
        """
        Return the variables in the gadget which are defined to be randomness,
        i.e., uniformly, independently and identically distributed random variables.
        """
        return set()

    def name(self) -> str:
        """Return the name of this gadget."""
        return self.__class__.__name__

    def obsgraph(self) -> ObservationGraph:
        return self.output().obsgraph

    def serialize(self, d: int, k: int = 1, e: int = 0) -> None:
        """
        Serialize this gadget to a file.
        """
        # compute gadgets directory next to this file
        base = os.path.dirname(__file__)
        gadgets_dir = os.path.join(base, "gadgets")
        os.makedirs(gadgets_dir, exist_ok=True)

        fn = f"{self.name()}_d{d}_k{k}_e{e}_{self.inputs[0].field}.sobj"
        path = os.path.join(gadgets_dir, fn)

        save(self, path)
        print(f"Gadget {self.name()} saved to {path}")

    def functional_correctness(self) -> bool:
        t0 = time.perf_counter()
        decoded = self.output().decode()
        print(f"decoded {decoded}")
        print(f"secrets {self.output().secrets}")
        for i, (r, o) in enumerate(zip(list(self.output().secrets), decoded)):
            if not r == o:
                raise AssertionError(
                    f"Symbolic check for {self.name()} failed on component {i}:\n  {r} != {o}"
                )
        print(
            f"✔ Symbolic check for {self.name()} passed in {time.perf_counter() - t0:.3f}s"
        )
        return True

    def verify_t_PS(
        self,
        t: int,
        num_worker: int = 1,
        continue_on_fail: bool = False,
        max_memory_mb: int = 1024,
        timeout: int = 3600,
        log: bool = False,
    ) -> bool:
        """
        Verify that the gadget satisfies the t-probing security notion.
        """

        print(
            "\n=========================================================================================="
        )
        print(
            f"Verifying {self.name()} for t={t} PS security notion with {num_worker} workers"
        )

        if t >= self.output().n:
            print(
                f"Gadget deemed trivially insecure since t={t} >= n={self.output().n} number of shares."
            )
            return False
        obsgraph = self.obsgraph()
        svars = self.secret_vars_encoded()
        pvars = self.public_vars()
        # for probing security we also need to correctly declare the randomness from the initial encoding as random variables here
        rvars = self.random_vars() | {
            r for i in self.inputs for r in i.ps_random_vars()
        }
        paravars = self.parameter_vars()
        equality_constraints = self.output().get_constraint_equalities()
        inequality_constraints = self.output().get_constraint_inequalities()
        groebner = self.output().compute_groebner_ideal()
        S = self.output().base_ring
        K = S.fraction_field()
        R = self.output().variable_ring
        R_ns = {name: R.gen(i) for i, name in enumerate(R.variable_names())}
        R_ns.update(
            {
                name: K(S.gen(i))  # <-- wrap the S‐generator in K()
                for i, name in enumerate(S.variable_names())
            }
        )
        res = verify_security(
            self.output(),
            (equality_constraints, inequality_constraints),
            groebner,
            SecurityNotion.PS,
            t,
            S,
            R,
            R_ns,
            svars,
            pvars,
            rvars,
            paravars,
            obsgraph,
            output_observations=set(),
            num_processes=num_worker,
            log=log,
            continue_on_fail=continue_on_fail,
            max_memory_mb=max_memory_mb,
            timeout_seconds=timeout,
        )
        print(
            "==========================================================================================\n"
        )
        return res

    def verify_t_NI(
        self,
        t: int,
        num_worker: int = 1,
        continue_on_fail: bool = False,
        max_memory_mb: int = 1024,
        timeout: int = 3600,
        log: bool = False,
    ) -> bool:
        """
        Verify that the gadget satisfies the t-NI security notion.
        """
        print(
            "\n=========================================================================================="
        )
        print(
            f"Verifying {self.name()} for t={t} NI security notion with {num_worker} workers"
        )
        if t >= self.output().n:
            print(
                f"Gadget deemed trivially insecure since t={t} >= n={self.output().n} number of shares."
            )
            return False
        obsgraph = self.obsgraph()
        svars = self.secret_vars_symbolic()
        pvars = self.public_vars()
        rvars = self.random_vars()
        paravars = self.parameter_vars()
        equality_constraints = self.output().get_constraint_equalities()
        inequality_constraints = self.output().get_constraint_inequalities()
        groebner = self.output().compute_groebner_ideal()
        S = self.output().base_ring
        K = S.fraction_field()
        R = self.output().variable_ring
        R_ns = {name: R.gen(i) for i, name in enumerate(R.variable_names())}
        R_ns.update(
            {
                name: K(S.gen(i))  # <-- wrap the S‐generator in K()
                for i, name in enumerate(S.variable_names())
            }
        )
        res = verify_security(
            self.output(),
            (equality_constraints, inequality_constraints),
            groebner,
            SecurityNotion.NI,
            t,
            S,
            R,
            R_ns,
            svars,
            pvars,
            rvars,
            paravars,
            obsgraph,
            output_observations=set(),
            num_processes=num_worker,
            continue_on_fail=continue_on_fail,
            max_memory_mb=max_memory_mb,
            timeout_seconds=timeout,
            log=log,
        )
        print(
            "==========================================================================================\n"
        )
        return res

    def verify_t_SNI(
        self,
        t: int,
        num_worker: int = 1,
        continue_on_fail: bool = False,
        max_memory_mb: int = 1024,
        timeout: int = 3600,
        log: bool = False,
    ) -> bool:
        """
        Verify that the gadget satisfies the t-SNI security notion.
        """
        print(
            "\n=========================================================================================="
        )
        print(
            f"Verifying {self.name()} for t={t} SNI security notion with {num_worker} workers"
        )
        if t >= self.output().n:
            print(
                f"Gadget deemed trivially insecure since t={t} >= n={self.output().n} number of shares."
            )
            return False
        obsgraph = self.obsgraph()
        svars = self.secret_vars_symbolic()
        svars_flat = set()
        for s in svars:
            svars_flat |= s
        pvars = self.public_vars()
        rvars = self.random_vars()
        suppvars = self.parameter_vars()
        equality_constraints = self.output().get_constraint_equalities()
        inequality_constraints = self.output().get_constraint_inequalities()
        groebner = self.output().compute_groebner_ideal()
        S = self.output().base_ring
        K = S.fraction_field()
        R = self.output().variable_ring
        R_ns = {name: R.gen(i) for i, name in enumerate(R.variable_names())}
        R_ns.update(
            {name: K(S.gen(i)) for i, name in enumerate(S.variable_names())}
        )

        output_observations = set(
            i.ni_obs.get_id() for i in self.output().sharing
        )

        res = verify_security(
            self.output(),
            (equality_constraints, inequality_constraints),
            groebner,
            SecurityNotion.SNI,
            t,
            S,
            R,
            R_ns,
            svars,
            pvars,
            rvars,
            suppvars,
            obsgraph,
            output_observations=output_observations,
            num_processes=num_worker,
            continue_on_fail=continue_on_fail,
            max_memory_mb=max_memory_mb,
            timeout_seconds=timeout,
            log=log,
        )
        print(
            "==========================================================================================\n"
        )
        return res

    def verify(
        self,
        snotion: SecurityNotion,
        t: int,
        num_worker: int = 1,
        continue_on_fail: bool = False,
        max_memory_mb: int = 1024,
        timeout: int = 3600,
        log: bool = False,
    ) -> bool:
        match snotion:
            case SecurityNotion.PS:
                return self.verify_t_PS(
                    t, num_worker, continue_on_fail, max_memory_mb, timeout, log
                )
            case SecurityNotion.NI:
                return self.verify_t_NI(
                    t, num_worker, continue_on_fail, max_memory_mb, timeout, log
                )
            case SecurityNotion.SNI:
                return self.verify_t_SNI(
                    t, num_worker, continue_on_fail, max_memory_mb, timeout, log
                )
            case _:
                raise ValueError(
                    f"Unknown security notion {snotion} to verify against."
                )

    @classmethod
    def from_file(
        cls, d: int, k: int = 1, e: int = 0, field: CommutativeRing = GF(2**8)
    ) -> Self:
        """
        Load back a gadget previously serialized via `serialize()`.
        """
        base = os.path.dirname(__file__)
        gadgets_dir = os.path.join(base, "gadgets")
        fn = f"{cls.__name__}_d{d}_k{k}_e{e}_{field}.sobj"
        path = os.path.join(gadgets_dir, fn)

        if not os.path.exists(path):
            raise FileNotFoundError(
                f"Gadget at {path} does not exist. Please generate it by running `python3 generate_polymasking_gadgets.py` for you desired parameters or initialize the gadget manually."
            )
        obj = load(path)
        # skip strict isinstance; at least check name()
        if obj.name() != cls.__name__:
            raise TypeError(f"Loaded {obj.name()}, expected {cls.__name__}")
        return obj
