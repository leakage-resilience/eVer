# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
import sys
import time

from itertools import count
from typing import Dict, List, Optional, Self, Sequence, Set, Tuple, Type
from contextlib import contextmanager
from sage.all import GF, Matrix
from sage.rings.ring import CommutativeRing
from sage.symbolic.expression import Expression
from sage.rings.fraction_field_element import FractionFieldElement
from sage.rings.polynomial.multi_polynomial import MPolynomial
from copy import copy
from observations import Location, ObservableValue, ObservationGraph, mk_obsval
from gadget import Gadget
from encoding import PolyEnc
from gen_parameter_vars import (
    gen_A_tilde_3D,
    generate_lambda_hat_non_packed,
    generate_lambda_hat_packed,
    generate_M_enc_for_degree_d_FOWZ25,
    generate_vandermonde,
)
from polyring import gen_rings_for_gadgets
from utils import mk_loc_factory, to_obsval_factory


def setup_polyencs(
    d: int,
    e: int,
    n: int,
    k: int,
    F: CommutativeRing,
    prefixes: Sequence[str],
    max_randoms: int = 1000,  # interestingly, blowing up the ring with many unused variables seems to have no significant effect on performance
) -> Tuple[
    Dict[str, PolyEnc],
    count,  # random‐counter
]:
    """
    Build one PolyEnc per name in `prefixes`, and return them plus:
      - support_points, secret_support_points,
      - the shared random-counter, and
      - the shared ObservationGraph.
    """
    # symbolic names
    supp_names = [f"alpha_{i}" for i in range(n)]
    if k == 1:
        # shamir secret sharing uses the evaluation point constant 0 for its secret, we therefore allocate no variables here
        secret_names = []
    else:
        secret_names = [f"alpha_{i}" for i in range(n, n + k)]

    # per‐prefix variable names
    secret_vars: List[str] = []
    symbolic_shares: List[str] = []
    for p in prefixes:
        secret_vars += [f"{p}{i}" for i in range(k)]
        symbolic_shares += [f"{p.upper()}{i}" for i in range(n)]

    # 1) build rings
    base_ring, ring = gen_rings_for_gadgets(
        F,
        supp_names + secret_names,
        secret_vars + symbolic_shares,
        max_randoms=max_randoms,
    )

    # 2) coerce support points into the fraction‐field
    support_points = [base_ring(s) for s in supp_names]
    # TODO: make this convention parametric
    secret_support_points = (
        [base_ring(s) for s in secret_names] if k > 1 else [base_ring(0)]
    )

    # 3) shared log & counter
    rc = count()
    obsgraph = ObservationGraph()

    # 4) make each PolyEnc
    encs: Dict[str, PolyEnc] = {}
    for p in prefixes:
        f_secrets = [ring(f"{p}{i}") for i in range(k)]
        f_sym_shares = [ring(f"{p.upper()}{i}") for i in range(n)]
        encs[p] = PolyEnc(
            d=d,
            e=e,
            n=n,
            obsgraph=obsgraph,
            secrets=f_secrets,
            field=F,
            base_ring=base_ring,
            variable_ring=ring,
            support_points=support_points,
            secret_support_points=secret_support_points,
            symbolic_shares=f_sym_shares,
            rc_count=rc,
        )

    return encs, rc


def make_f_encodings(d, e, n, k, field):
    encs, rc = setup_polyencs(
        d=d, e=e, n=n, k=k, F=field, prefixes=["f"], max_randoms=100
    )
    return encs["f"], rc


def make_f_g_encodings(d, e, n, k, field):
    encs, rc = setup_polyencs(
        d=d, e=e, n=n, k=k, F=field, prefixes=["f", "g"], max_randoms=100
    )
    return encs["f"], encs["g"], rc


def make_h_encodings(d, e, n, k, field):
    # create 4 encodings used for h, h1, h2, h3 in Comp gadget
    encs, rc = setup_polyencs(
        d=d,
        e=e,
        n=n,
        k=k,
        F=field,
        prefixes=["h0", "h1", "h2", "h3"],
        max_randoms=100,
    )
    return encs["h0"], encs["h1"], encs["h2"], encs["h3"], rc


class SWPolyAddGadget(Gadget[PolyEnc]):
    """
    Sharewise addition of two polynomial encodings.
    """

    def __init__(self, f: PolyEnc, g: PolyEnc, callloc: Optional[Location]):
        if not isinstance(f, PolyEnc) or not isinstance(g, PolyEnc):
            raise TypeError(f"{self.name()} requires two PolyEnc inputs.")
        if f.field != g.field:
            raise ValueError("Fields differ between the two encodings.")
        if f.k != g.k:
            raise ValueError(
                f"Number of encoded secrets mismatch k: {f.k} != {g.k}"
            )
        if f.e != g.e:
            raise ValueError(f"Redundancy mismatch e: = {f.e} != {g.e}")
        if f.support_points != g.support_points:
            print(f"Support-points: {f.support_points} != {g.support_points}")
            raise ValueError(
                f"Support-points  {f.support_points} do not match {g.support_points}."
            )
        super().__init__([f, g], callloc)

        new_sharing = [
            fi.__add__(
                gi,
                loc=Location(
                    "SWPolyAdd",
                    2,
                    f"addition of shares with index[{i}]",
                    callloc,
                ),
            )
            for i, (fi, gi) in enumerate(zip(f.sharing, g.sharing))
        ]
        new_secrets = [si + ti for si, ti in zip(f.secrets, g.secrets)]
        self.output_enc = f.copy(
            sharing=new_sharing,
            secrets=new_secrets,
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, G_enc, _ = make_f_g_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, g=G_enc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc


class SWPolySubGadget(Gadget[PolyEnc]):
    """
    Sharewise subtraction of two polynomial encodings.
    """

    def __init__(self, f: PolyEnc, g: PolyEnc, callloc: Optional[Location]):
        if not isinstance(f, PolyEnc) or not isinstance(g, PolyEnc):
            raise TypeError(f"{self.name()} requires two PolyEnc inputs.")
        if f.field != g.field:
            raise ValueError("Fields differ between the two encodings.")
        if f.k != g.k:
            raise ValueError(
                f"Number of encoded secrets mismatch k: {f.k} != {g.k}"
            )
        if f.e != g.e:
            raise ValueError(f"Redundancy mismatch e: = {f.e} != {g.e}")
        if f.support_points != g.support_points:
            print(f"Support-points: {f.support_points} != {g.support_points}")
            raise ValueError(
                f"Support-points  {f.support_points} do not match {g.support_points}."
            )
        super().__init__([f, g], callloc)

        new_sharing = [
            fi.__sub__(
                gi,
                loc=Location(
                    "SWPolySub",
                    2,
                    f"subtraction of shares with index[{i}]",
                    callloc,
                ),
            )
            for i, (fi, gi) in enumerate(zip(f.sharing, g.sharing))
        ]
        new_secrets = [si - ti for si, ti in zip(f.secrets, g.secrets)]
        self.output_enc = f.copy(
            sharing=new_sharing,
            secrets=new_secrets,
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, G_enc, _ = make_f_g_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, g=G_enc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc


class SWPolyMulGadget(Gadget[PolyEnc]):
    """
    Sharewise multiplication of two polynomial encodings.
    """

    def __init__(self, f: PolyEnc, g: PolyEnc, callloc: Optional[Location]):
        if not isinstance(f, PolyEnc) or not isinstance(g, PolyEnc):
            raise TypeError(f"{self.name()} requires two PolyEnc inputs.")
        if f.field != g.field:
            raise ValueError("Fields differ between the two encodings.")
        if f.k != g.k:
            raise ValueError(
                f"Number of encoded secrets mismatch k: {f.k} != {g.k}"
            )
        if f.e != g.e:
            raise ValueError(f"Redundancy mismatch e: = {f.e} != {g.e}")
        if f.support_points != g.support_points:
            print(f"Support-points: {f.support_points} != {g.support_points}")
            raise ValueError(
                f"Support-points  {f.support_points} do not match {g.support_points}."
            )
        super().__init__([f, g], callloc)

        new_sharing = [
            fi.__mul__(
                gi,
                loc=Location(
                    "SWPolyMult",
                    2,
                    f"multiplication of shares with index[{i}]",
                    callloc,
                ),
            )
            for i, (fi, gi) in enumerate(zip(f.sharing, g.sharing))
        ]
        new_secrets = [si * ti for si, ti in zip(f.secrets, g.secrets)]
        self.output_enc = f.copy(
            sharing=new_sharing,
            secrets=new_secrets,
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, G_enc, _ = make_f_g_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, g=G_enc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc


class FOWZ25Zenc(Gadget[PolyEnc]):
    """
    Polynomial zero-encoding from https://eprint.iacr.org/2025/035.pdf.
    """

    def __init__(
        self,
        f: PolyEnc,  # this is only used as a dummy encoding for var access, not impacting the computations
        d: int,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert f.k > 0, "k must be at least 1"
        assert f.k <= d, "k must be less than or equal to d"
        super().__init__([f], callloc)

        M_enc = None
        if f.k == 1:
            M_enc = generate_M_enc_for_degree_d_FOWZ25(
                f.base_ring,
                list(f.secret_support_points),
                list(f.support_points),
                len(f.support_points),
                f.k,
                d,
            )
        else:
            M_enc = generate_M_enc_for_degree_d_FOWZ25(
                f.base_ring,
                list(f.secret_support_points),
                list(f.support_points),
                len(f.support_points),
                f.k,
                d,
            )

        # generate the randomn variables used for the zero encoding
        self.randoms = set()
        for _ in range(d + 1 - f.k):
            name = f"R_{next(rc)}"
            R_i_poly = f.variable_ring(name)
            self.randoms.add(R_i_poly)

        # generate observations on random variables
        rands = [
            mk_obsval(
                f.obsgraph,
                r,
                r,
                location=Location(
                    "Zenc", 6, description=f"random {r}", caller=callloc
                ),
            )
            for r in self.randoms
        ]

        M_enc_obs = []
        for i in range(M_enc.nrows()):
            row = []
            for j in range(f.k, M_enc.ncols()):
                val = f.variable_ring(M_enc[i, j])
                obs_val = mk_obsval(
                    f.obsgraph,
                    val,
                    val,
                    location=Location(
                        "Zenc",
                        6,
                        description=f"M_enc[{i},{j}] = {val}",
                        caller=callloc,
                    ),
                )
                row.append(obs_val)
            M_enc_obs.append(row)

        zero = mk_obsval(
            f.obsgraph, f.variable_ring.zero(), f.variable_ring.zero()
        )
        shares = []
        for i in range(f.n):
            sum = copy(
                zero
            )  # needs a copy since zero is a list and lists are call by reference and therefore altering sum alters zero
            for j, r in enumerate(rands):
                sum += (M_enc_obs[i][j]).__mul__(
                    r,
                    loc=Location(
                        "Zenc", 2, f"M_enc[{i}][{j}] * rand {r}", callloc
                    ),
                )
            shares.append(sum)

        self.output_enc = f.copy(
            sharing=shares,
            secrets=[f.variable_ring.zero() for _ in range(f.k)],
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, rc = make_f_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, d=d, rc=rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms


class FOWZ25SZenc(Gadget[PolyEnc]):
    """
    Polynomial sum zero-encoding from https://eprint.iacr.org/2025/035.pdf.
    """

    def __init__(
        self,
        f: PolyEnc,  # this is only used as a dummy encoding for var access, not impacting the computations
        d: int,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert f.k > 0, "k must be at least 1"
        assert f.k <= d, "k must be less than or equal to d"
        super().__init__([f], callloc)

        randoms = set()
        szenc = FOWZ25Zenc(
            f,
            d,
            rc,
            callloc=Location(
                "SZenc", lineno=3, description="Zenc[0]", caller=callloc
            ),
        )
        randoms.update(szenc.random_vars())

        for i in range(1, d - f.k + 1):
            temp_zenc = FOWZ25Zenc(
                f,
                d,
                rc,
                callloc=Location(
                    "SZenc", lineno=3, description=f"Zenc[{i}]", caller=callloc
                ),
            )
            randoms.update(temp_zenc.random_vars())
            szenc = SWPolyAddGadget(
                szenc.output(),
                temp_zenc.output(),
                callloc=Location(
                    "SZenc", lineno=4, description="+", caller=callloc
                ),
            )

        self.randoms = randoms
        self.output_enc = szenc.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, rc = make_f_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, d=d, rc=rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return set(self.randoms)


class FOWZ25Refresh(Gadget[PolyEnc]):
    def __init__(
        self, f: PolyEnc, d: int, rc: count, callloc: Optional[Location]
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert d > 0, "d must be at least 1"
        assert f.k > 0, "k must be at least 1"
        assert f.k <= d, "k must be less than or equal to d"
        super().__init__([f], callloc)

        self.randoms = set()

        szenc = FOWZ25SZenc(
            f,
            d,
            rc,
            callloc=Location("Refresh: generate szenc", caller=callloc),
        )
        self.randoms.update(szenc.random_vars())

        sw_add = SWPolyAddGadget(
            f,
            szenc.output(),
            callloc=Location("Refresh: g = f + szenc", caller=callloc),
        )

        self.output_enc = sw_add.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, rc = make_f_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, d=d, rc=rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms


class OptZenc(Gadget[PolyEnc]):
    """
    Optimized zero-encoding of a polynomial encoding.
    """

    def __init__(
        self,
        f: PolyEnc,  # this is only used as a dummy encoding for var access, not impacting the computations
        d: int,
        offset: int,
        A_tilde: list[list[list[Expression]]],
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert f.k > 0, "k must be at least 1"
        super().__init__([f], callloc)

        G = [
            mk_obsval(
                f.obsgraph,
                f.variable_ring.zero(),
                f.variable_ring.zero(),
                location=Location(
                    "OptZenc",
                    lineno=2,
                    description="initalization",
                    caller=callloc,
                ),
            )
            for _ in range(f.n)
        ]

        self.randoms = set()
        for i in range(offset, d - f.k + 1):
            R_i = f"R_{next(rc)}"
            R_i_poly = f.variable_ring(R_i)
            G[i] = mk_obsval(
                f.obsgraph,
                R_i_poly,
                R_i_poly,
                location=Location(
                    "OptZenc", lineno=3, description="sampling", caller=callloc
                ),
            )
            self.randoms.add(R_i_poly)

        for i in range(d + 1 - f.k, f.n):
            for j in range(offset, d - f.k + 1):
                val = f.variable_ring(A_tilde[d - 1][i][j])
                obsval = mk_obsval(
                    f.obsgraph,
                    val,
                    val,
                    location=Location(
                        "OptZenc",
                        lineno=6,
                        description="A-tilde_opt",
                        caller=callloc,
                    ),
                )
                mulval = obsval.__mul__(
                    G[j],
                    loc=Location(
                        "OptZenc", lineno=6, description="*", caller=callloc
                    ),
                )
                G[i].__iadd__(
                    mulval,
                    loc=Location(
                        "OptZenc", lineno=6, description="+", caller=callloc
                    ),
                )

        self.output_enc = f.copy(
            sharing=G,
            secrets=[f.variable_ring.zero() for _ in range(f.k)],
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, _, rc = make_f_g_encodings(d, e, n, k, F)
        support_points = F_enc.support_points
        secret_support_points = F_enc.secret_support_points
        base_ring = F_enc.base_ring
        # A_tilde
        if k == 1:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, [base_ring.zero()], support_points
            )
        else:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, secret_support_points, support_points
            )

        instance = cls(F_enc, d, 0, a_tilde, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms


class OptSZenc(Gadget[PolyEnc]):
    def __init__(
        self,
        f: PolyEnc,
        d: int,
        A_tilde: list[list[list[Expression]]],
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert d > 0, "d must be at least 1"
        assert f.k > 0, "k must be at least 1"
        super().__init__([f], callloc)

        # perform the optimized zero-encoding
        self.randoms = set()
        szenc = OptZenc(
            f,
            d,
            0,
            A_tilde,
            rc,
            callloc=Location(
                "OptSZenc",
                lineno=3,
                description="G[0] <- optZenc",
                caller=callloc,
            ),
        )
        self.randoms.update(szenc.random_vars())

        for i in range(1, d - f.k + 1):
            temp_zenc = OptZenc(
                f,
                d,
                i,
                A_tilde,
                rc,
                callloc=Location(
                    "OptSZenc",
                    lineno=3,
                    description=f"G[{i}] <- optZenc",
                    caller=callloc,
                ),
            )
            self.randoms.update(temp_zenc.random_vars())
            szenc = SWPolyAddGadget(
                szenc.output(),
                temp_zenc.output(),
                callloc=Location(
                    "OptSZenc", lineno=4, description="+", caller=callloc
                ),
            )

        self.output_enc = szenc.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, _, rc = make_f_g_encodings(d, e, n, k, F)
        support_points = F_enc.support_points
        secret_support_points = F_enc.secret_support_points
        base_ring = F_enc.base_ring
        # A_tilde
        if k == 1:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, [base_ring.zero()], support_points
            )
        else:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, secret_support_points, support_points
            )

        instance = cls(F_enc, d, a_tilde, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms


class OptRefresh(Gadget[PolyEnc]):
    def __init__(
        self,
        f: PolyEnc,
        d: int,
        A_tilde: list[list[list[Expression]]],
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert d > 0, "d must be at least 1"
        assert f.k > 0, "k must be at least 1"
        assert f.k <= d, "k must be less than or equal to d"
        super().__init__([f], callloc)

        self.randoms = set()

        szenc = OptSZenc(
            f,
            d,
            A_tilde,
            rc,
            callloc=Location("OptRefresh: generate sZenc", caller=callloc),
        )
        self.randoms.update(szenc.random_vars())

        sw_add = SWPolyAddGadget(
            szenc.output(),
            f,
            callloc=Location("OptRefresh: g = f + sZenc", caller=callloc),
        )

        self.output_enc = sw_add.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, rc = make_f_encodings(d, e, n, k, F)
        support_points = F_enc.support_points
        secret_support_points = F_enc.secret_support_points
        base_ring = F_enc.base_ring
        # A_tilde
        if k == 1:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, [base_ring.zero()], support_points
            )
        else:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, secret_support_points, support_points
            )

        instance = cls(F_enc, d, a_tilde, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms


class ZencSFRES18(Gadget[PolyEnc]):
    """
    Polynomial zero-encoding from https://eprint.iacr.org/2025/035.pdf.
    """

    def __init__(
        self,
        f: PolyEnc,  # this is only used as a dummy encoding for var access, not impacting the computations
        d: int,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert f.k == 1, (
            "SFRES18 zero encoding only works for shamir secret sharing"
        )
        assert len(f.support_points) == f.n
        super().__init__([f], callloc)

        zero = mk_obsval(
            f.obsgraph, f.variable_ring.zero(), f.variable_ring.zero()
        )
        # Store the randoms before generating encoding
        self.randoms = []
        alphas = copy(f.support_points)
        G = []
        for _ in range(d):
            name = f"R_{next(rc)}"
            R_i_poly = f.variable_ring(name)
            self.randoms.append(R_i_poly)

        obs_rands = [
            mk_obsval(
                f.obsgraph,
                r,
                r,
                location=Location(
                    "ZencSFRES18", 6, description="randoms", caller=callloc
                ),
            )
            for r in self.randoms
        ]

        for i, alpha in enumerate(alphas):
            sum = zero
            for k, r in enumerate(obs_rands, start=1):
                sum = sum.__add__(
                    r.__mul__(
                        mk_obsval(
                            f.obsgraph,
                            alpha**k,
                            alpha**k,
                            location=Location(
                                "ZencSFRES18",
                                6,
                                description="alpha^k",
                                caller=callloc,
                            ),
                        )
                    ),
                    loc=Location(
                        "ZencSFRES18", 14, description=f"r_{k} * alpha_{i}^{k} "
                    ),
                )
            G.append(sum)

        self.output_enc = f.copy(
            sharing=G,
            secrets=[f.variable_ring.zero() for _ in range(f.k)],
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        assert k == 1, (
            f"RefreshSFRES18 currently only supported for k == 1, but got {k}."
        )
        n = d + e + 1

        F_enc, rc = make_f_encodings(d, e, n, k, F)
        instance = cls(F_enc, d, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return set(self.randoms)


class RefreshSFRES18(Gadget[PolyEnc]):
    def __init__(
        self, f: PolyEnc, d: int, rc: count, callloc: Optional[Location]
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc inputs.")
        assert f.n > 1, (
            "n must be at least 2 to have a valid encoding in our setting"
        )
        assert d > 0, "d must be at least 1"
        assert f.k == 1, "SFRES18 Refresh only works for k = 1 encoded secrets"
        super().__init__([f], callloc)

        # perform the optimized zero-encoding
        self.randoms = set()

        zenc = ZencSFRES18(
            f,
            d,
            rc,
            callloc=Location("RefreshSFRES18: generate Zenc", caller=callloc),
        )
        self.randoms.update(zenc.random_vars())

        sw_add = SWPolyAddGadget(
            zenc.output(),
            f,
            callloc=Location("RefreshSFRES18: g = f + Zenc", caller=callloc),
        )

        self.output_enc = sw_add.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        assert k == 1, f"RefreshSFRES18 only supports k == 1, but got {k}."
        n = d + e + 1

        F_enc, rc = make_f_encodings(d, e, n, k, F)
        instance = cls(F_enc, d, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms


class SWComp(Gadget[PolyEnc]):
    """
    SWComp is a gadget that compresses four polynomial encodings H0, H1, H2, and H3 into a single polynomial encoding.
    The gadget is used in the LAOLA multiplication algorithm.
    """

    def __init__(
        self,
        H0: PolyEnc,
        H1: PolyEnc,
        H2: PolyEnc,
        H3: PolyEnc,
        d: int,
        A_tilde: list[list[list[FractionFieldElement]]],
        rc: count,
        callloc: Optional[Location],
    ):
        assert (
            isinstance(H0, PolyEnc)
            and isinstance(H1, PolyEnc)
            and isinstance(H2, PolyEnc)
            and isinstance(H3, PolyEnc)
        ), f"{self.name()} requires four PolyEnc inputs."
        assert H0.field == H1.field == H2.field == H3.field, (
            "Fields differ between the four encodings."
        )
        assert H0.k == H1.k == H2.k == H3.k, (
            f"Number of encoded secrets mismatch k: {H0.k} != {H1.k} != {H2.k} != {H3.k}"
        )
        assert H0.e == H1.e == H2.e == H3.e, (
            f"Redundancy mismatch e: = {H0.e} != {H1.e} != {H2.e} != {H3.e}"
        )
        assert (
            H0.support_points
            == H1.support_points
            == H2.support_points
            == H3.support_points
        ), "Support-points do not match."
        super().__init__([H0, H1, H2, H3], callloc)

        self.randoms = set()
        res = OptSZenc(
            H0,
            d,
            A_tilde,
            rc,
            callloc=Location("SWComp", lineno=1, caller=callloc),
        )
        self.randoms.update(res.randoms)
        res = SWPolyAddGadget(
            res.output(),
            H0,
            callloc=Location(
                "SWComp", lineno=2, description="optSZenc + H0", caller=callloc
            ),
        )
        res = SWPolyAddGadget(
            res.output(),
            H1,
            callloc=Location(
                "SWComp",
                lineno=2,
                description="(optSZenc + H0) + H1",
                caller=callloc,
            ),
        )
        res = SWPolyAddGadget(
            res.output(),
            H2,
            callloc=Location(
                "SWComp",
                lineno=2,
                description="((optSZenc + H0) + H1) + H2",
                caller=callloc,
            ),
        )
        res = SWPolyAddGadget(
            res.output(),
            H3,
            callloc=Location(
                "SWComp",
                lineno=2,
                description="(((optSZenc + H0) + H1) + H2) + H3",
                caller=callloc,
            ),
        )

        self.output_enc = H0.copy(
            sharing=res.output().sharing,
            secrets=[
                h0 + h1 + h2 + h3
                for (h0, h1, h2, h3) in zip(
                    H0.secrets, H1.secrets, H2.secrets, H3.secrets
                )
            ],
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1

        F_enc, _, rc = make_f_g_encodings(d, e, n, k, F)
        support_points = F_enc.support_points
        secret_support_points = F_enc.secret_support_points
        base_ring = F_enc.base_ring

        # A_tilde
        if k == 1:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, [base_ring.zero()], support_points
            )
        else:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, secret_support_points, support_points
            )

        H0, H1, H2, H3, rc = make_h_encodings(d, e, n, k, F)
        instance = cls(H0, H1, H2, H3, d, a_tilde, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms


class PolySquare(Gadget[PolyEnc]):
    """
    Linear squaring of all shares, only works correctly in GF(2)^k.
    """

    def __init__(
        self,
        f: PolyEnc,
        callloc: Optional[Location],
        is_GF2k: Optional[bool] = False,
    ):
        if not isinstance(f, PolyEnc):
            raise TypeError(f"{self.name()} requires PolyEnc input.")
        super().__init__([f], callloc)
        if is_GF2k:
            new_sharing = [
                fi.square_GF2k(
                    loc=Location(
                        "PolySquare",
                        2,
                        f"squaring of shares with index[{i}]",
                        callloc,
                    ),
                )
                for i, fi in enumerate(f.sharing)
            ]
        else:
            new_sharing = [
                fi.__mul__(
                    fi,
                    loc=Location(
                        "PolySquare",
                        2,
                        f"squaring of shares with index[{i}]",
                        callloc,
                    ),
                )
                for i, fi in enumerate(f.sharing)
            ]
        new_secrets = [si**2 for si in f.secrets]
        self.output_enc = f.copy(
            sharing=new_sharing,
            secrets=new_secrets,
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        F_enc, _ = make_f_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc


class LaolaMultGadget(Gadget[PolyEnc]):
    """
    LAOLA multiplication of two polynomial encodings.
    """

    def __init__(
        self,
        f: PolyEnc,
        g: PolyEnc,
        d: int,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc) or not isinstance(g, PolyEnc):
            raise TypeError("LaolaMultGadget requires two PolyEnc inputs.")
        if f.field != g.field:
            raise ValueError("Fields differ between the two encodings.")
        if f.k != g.k:
            raise ValueError(
                f"Number of encoded secrets mismatch k: {f.k} != {g.k}"
            )
        if f.e != g.e:
            raise ValueError(f"Redundancy mismatch e: = {f.e} != {g.e}")
        if f.support_points != g.support_points:
            raise ValueError("Support-points do not match.")
        # if f.k > 1 and f.k > d // 2:
        #     raise ValueError(f"Degree {d} is too low for k={f.k}.")
        super().__init__([f, g], callloc)

        n = f.n
        self.k = k = f.k
        self.randoms = set()

        if k == 1:
            lambda_hat = generate_lambda_hat_non_packed(
                f.base_ring, list(f.support_points), d
            )
            A_tilde = gen_A_tilde_3D(
                f.base_ring,
                n,
                d,
                k,
                [f.base_ring.zero()],
                list(f.support_points),
            )
        else:
            lambda_hat = generate_lambda_hat_packed(
                f.base_ring,
                list(f.secret_support_points),
                list(f.support_points),
                d,
                (d // 2),
            )
            A_tilde = gen_A_tilde_3D(
                f.base_ring,
                n,
                d,
                k,
                list(f.secret_support_points),
                list(f.support_points),
            )

        f_p, f_pp, rands_f = self._split_red(
            f,
            d,
            (d + 1) // 2,
            lambda_hat,
            A_tilde,
            rc,
            callloc=Location("LaOlaMult", lineno=1, caller=callloc),
        )
        g_p, g_pp, rands_g = self._split_red(
            g,
            d,
            d // 2,
            lambda_hat,
            A_tilde,
            rc,
            callloc=Location("LaOlaMult", lineno=2, caller=callloc),
        )
        self.randoms.update(rands_f)
        self.randoms.update(rands_g)
        H0 = SWPolyMulGadget(
            f_p, g_p, callloc=Location("LaOlaMult", lineno=3, caller=callloc)
        ).output()
        H1 = SWPolyMulGadget(
            f_p, g_pp, callloc=Location("LaOlaMult", lineno=4, caller=callloc)
        ).output()
        H2 = SWPolyMulGadget(
            f_pp, g_p, callloc=Location("LaOlaMult", lineno=5, caller=callloc)
        ).output()
        H3 = SWPolyMulGadget(
            f_pp, g_pp, callloc=Location("LaOlaMult", lineno=6, caller=callloc)
        ).output()
        res = SWComp(
            H0,
            H1,
            H2,
            H3,
            d,
            A_tilde,
            rc,
            callloc=Location("LaOlaMult", lineno=7, caller=callloc),
        )
        self.randoms.update(res.randoms)
        res_enc = res.output()

        self.output_enc = f.copy(
            sharing=res_enc.sharing,
            secrets=[f_i * g_i for f_i, g_i in zip(f.secrets, g.secrets)],
        )

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        # assert k == 1 or k > d // 2, (
        #     f"Skipped LaolaMultGadget for k={k} and d={d} (k must be <= d//2)"
        # )

        n = d + e + 1

        F_enc, G_enc, rc = make_f_g_encodings(d, e, n, k, F)
        instance = cls(F_enc, G_enc, d, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[MPolynomial]:
        return self.randoms

    def _split_red(
        self,
        f: PolyEnc,
        global_d: int,
        d_prime: int,
        lambda_hat: list[list[MPolynomial]],
        A_tilde: list[list[list[MPolynomial]]],
        rc: count,
        callloc: Optional[Location],
    ) -> tuple[PolyEnc, PolyEnc, set[MPolynomial]]:
        """
        SplitRed is a function that splits a polynomial encoding F into two parts F' and F'' such that deg(F) = deg(F') = deg(F''), F = F' + F'' and deg(F' + F'') = deg(F)/2.
        The function is used in the LAOLA multiplication algorithm.
        """
        n = f.n
        ceil_n = (n + 1) // 2
        floor_n = n // 2
        randoms = set()
        R_zero = f.variable_ring.zero()

        if d_prime == global_d:
            zero_sharing = f.copy(
                sharing=[
                    mk_obsval(
                        f.obsgraph,
                        f.variable_ring.zero(),
                        f.variable_ring.zero(),
                    )
                    for _ in range(n)
                ],
                secrets=[f.variable_ring.zero() for _ in range(f.k)],
            )
            return f, zero_sharing, randoms
        # initialize dummy encodings
        g_hat: list[PolyEnc] = [
            f.copy(
                sharing=[
                    mk_obsval(
                        f.obsgraph,
                        R_zero,
                        R_zero,
                        location=Location(
                            "SplitRed",
                            description=f"init g-hat[{i}]",
                            caller=callloc,
                        ),
                    )
                    for i in range(n)
                ],
                secrets=[R_zero for _ in range(f.k)],
            )
            for _ in range(n)
        ]  # FIXME: adjust range to avoid double assignment
        g: list[PolyEnc] = [
            f.copy(
                sharing=[
                    mk_obsval(
                        f.obsgraph,
                        R_zero,
                        R_zero,
                        location=Location(
                            "SplitRed",
                            description=f"init g[{i}]",
                            caller=callloc,
                        ),
                    )
                    for i in range(n)
                ],
                secrets=[R_zero for _ in range(f.k)],
            )
            for _ in range(n)
        ]
        # dummy_zero_enc = PolyEnc(shares=[SR(0) for _ in range(n)], secrets=[SR(0) for _ in range(f.k)])

        # 1) build full degree zero encodings
        for j in range(ceil_n):
            degree = (
                (global_d - j) if (j < (global_d + 1 - self.k)) else global_d
            )
            lineno = 4 if (j < (global_d + 1 - self.k)) else 6
            zenc = OptZenc(
                f,
                degree,
                0,
                A_tilde,
                rc,
                callloc=Location(
                    "SplitRed",
                    lineno=lineno,
                    description=f"g-hat[{j}] <- optZenc",
                    caller=callloc,
                ),
            )
            randoms.update(zenc.randoms)
            g_hat[j] = zenc.output()

        # this is the assumed unnecessary ZENC that is still in the algorithm
        for j in range(floor_n):
            g[j] = g_hat[j]

        # 3) if n is odd, do the extra add-back at j=half-1
        if n % 2 == 1:
            # TODO: description
            g[floor_n - 1] = SWPolyAddGadget(
                g[floor_n - 1],
                g_hat[ceil_n - 1],
                callloc=Location("SplitRed", lineno=14, caller=callloc),
            ).output()

        # 4) first-half contributions to Fp
        # TODO: Location
        Fp_cal: list[list[ObservableValue]] = [
            [mk_obsval(f.obsgraph, R_zero, R_zero) for _ in range(n)]
            for _ in range(n)
        ]
        F_cal: list[list[ObservableValue]] = [
            [mk_obsval(f.obsgraph, R_zero, R_zero) for _ in range(n)]
            for _ in range(n)
        ]
        Fp: list[ObservableValue] = [
            mk_obsval(f.obsgraph, R_zero, R_zero) for _ in range(n)
        ]

        for j in range(floor_n):
            for i in range(n):
                val = f.variable_ring(lambda_hat[i][j])
                # TODO: Location
                Fp_cal[j][i] = mk_obsval(f.obsgraph, val, val) * f.sharing[j]

                # TODO: description
                F_cal[j][i] = (
                    g[j]
                    .sharing[i]
                    .__add__(
                        Fp_cal[j][i],
                        loc=Location("SplitRed", lineno=19, caller=callloc),
                    )
                )
                # TODO: description
                Fp[i].__iadd__(
                    F_cal[j][i],
                    loc=Location("SplitRed", lineno=21, caller=callloc),
                )

        dummy_secrets = [
            R_zero for _ in range(f.k)
        ]  # These are dummy secrets since this is a 1 input to  2 output gadget and both outputs contain specific parts of the secrets

        Fp_enc = f.copy(
            sharing=Fp,
            secrets=dummy_secrets,
        )

        # 5) build G[j][i] for the second half

        for j in range(ceil_n):
            idx = j + floor_n
            if d_prime == 0:
                zeros = f.copy(
                    sharing=[
                        mk_obsval(
                            f.obsgraph,
                            f.variable_ring.zero(),
                            f.variable_ring.zero(),
                        )
                        for _ in range(n)
                    ],
                    secrets=[f.variable_ring.zero() for _ in range(f.k)],
                )
                g[idx] = SWPolySubGadget(
                    zeros,
                    g_hat[j],
                    callloc=Location("SplitRed", lineno=27, caller=callloc),
                ).output()
            else:
                degree = (
                    (d_prime - j) if (j < (d_prime - self.k + 1)) else (d_prime)
                )
                lineno = 24 if (j < (d_prime - self.k + 1)) else 26
                if degree > 0:
                    # TODO: description
                    zenc = OptZenc(
                        f,
                        degree,
                        0,
                        A_tilde,
                        rc,
                        callloc=Location(
                            "SplitRed", lineno=lineno, caller=callloc
                        ),
                    )
                    randoms.update(zenc.randoms)
                    g[idx] = SWPolySubGadget(
                        zenc.output_enc,
                        g_hat[j],
                        callloc=Location("SplitRed", lineno=27, caller=callloc),
                    ).output()
                else:
                    zeros = f.copy(
                        sharing=[
                            mk_obsval(
                                f.obsgraph,
                                f.variable_ring.zero(),
                                f.variable_ring.zero(),
                            )
                            for _ in range(n)
                        ],
                        secrets=[f.variable_ring.zero() for _ in range(f.k)],
                    )
                    g[idx] = SWPolySubGadget(
                        zeros,
                        g_hat[j],
                        callloc=Location("SplitRed", lineno=27, caller=callloc),
                    ).output()

        # 6) accumulate into outputs Fp and Fpp
        Fpp: list[ObservableValue] = [
            mk_obsval(f.obsgraph, R_zero, R_zero) for _ in range(n)
        ]

        for j in range(floor_n, n):
            for i in range(n):
                val = f.variable_ring(lambda_hat[i][j])
                # TODO: Location
                Fp_cal[j][i] = mk_obsval(f.obsgraph, val, val) * f.sharing[j]

                F_cal[j][i] = (
                    g[j]
                    .sharing[i]
                    .__add__(
                        Fp_cal[j][i],
                        loc=Location("SplitRed", lineno=32, caller=callloc),
                    )
                )

                Fpp[i].__iadd__(
                    F_cal[j][i],
                    loc=Location("SplitRed", lineno=34, caller=callloc),
                )

        Fpp_enc = f.copy(
            sharing=Fpp,
            secrets=dummy_secrets,
        )
        return Fp_enc, Fpp_enc, randoms


class BgwMultGadget(Gadget[PolyEnc]):
    """
    BGW multiplication of two polynomial encodings.
    """

    def __init__(
        self,
        f: PolyEnc,
        g: PolyEnc,
        d: int,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(f, PolyEnc) or not isinstance(g, PolyEnc):
            raise TypeError("BgwMultGadget requires two PolyEnc inputs.")
        if f.field != g.field:
            raise ValueError("Fields differ between the two encodings.")
        if f.k != g.k:
            raise ValueError(
                f"Number of encoded secrets mismatch k: {f.k} != {g.k}"
            )
        if f.e != g.e:
            raise ValueError(f"Redundancy mismatch e: = {f.e} != {g.e}")
        if f.support_points != g.support_points:
            raise ValueError("Support-points do not match.")
        if f.k > 1 and f.k > d:
            raise ValueError(f"Degree {d} is too low for k={f.k}.")
        super().__init__([f, g], callloc)

        self.f = f
        self.g = g
        self.d = d  # FIXME: this looks inconsistent
        self.n = f.n
        self.k = f.k
        self.e = f.e
        self.randoms = set()

        if self.n != 2 * d + self.e + 1:
            raise ValueError(
                f"n should be equal to 2d+e+1, but got n={self.n}, d={self.d}, e={self.e} and hence {self.n} != {2 * self.d + self.e + 1}"
            )
        if self.d != f.d or self.d != g.d:
            raise ValueError(
                f"Degree mismatch between encodings f (d={f.d}), g (d={g.d}), and the specified desired degree {d}"
            )

        # in Shamir's secret sharing (for k=1 only) the secret support point is fixed to zero.
        # the convention is to use shamir for k=1 and packed otherwise, #TODO: make this parametric to the BGWMultGadget
        self.a_tilde = gen_A_tilde_3D(
            f.base_ring,
            self.n,
            self.d,
            self.k,
            list(f.secret_support_points),
            list(self.f.support_points),
        )

        lambda_degred = self.lambda_hat_gen()

        # Step 1: share-wise multiplication
        Q = SWPolyMulGadget(
            f,
            g,
            callloc=Location(
                "BgwMult",
                description="share-wise multiplication",
                lineno=2,
                caller=callloc,
            ),
        )
        self.randoms.update(Q.random_vars())
        Q_enc = Q.output()

        # Step 2: generate zero-encodings
        Y: list[PolyEnc] = []

        for j in range(self.n):
            zenc_degree = self.d - j if j < self.d + 1 - self.k else self.d
            zenc = OptZenc(
                f=self.f,
                d=zenc_degree,
                offset=0,
                A_tilde=self.a_tilde,
                rc=rc,
                callloc=Location(
                    "BgwMult",
                    description=f"generate zero-encodings (using OptZenc) of degree {zenc_degree}",
                    lineno=5,
                    caller=callloc,
                ),
            )
            Y.append(zenc.output())
            self.randoms.update(zenc.random_vars())

        # # Step 3: Degree reduction
        H: list[ObservableValue] = []
        for row in range(self.n):
            H_i = mk_obsval(
                self.f.obsgraph,
                self.f.base_ring.zero(),
                self.f.base_ring.zero(),
            )
            for col in range(self.n):
                val = mk_obsval(
                    self.f.obsgraph,
                    self.f.variable_ring(lambda_degred[row, col]),
                    self.f.variable_ring(lambda_degred[row, col]),
                )
                h_ij = val.__mul__(
                    Q_enc.sharing[col],
                    loc=Location(
                        "BgwMult",
                        description="degree reduction: multiply with lambda matrix (multiply two entries)",
                        lineno=8,
                        caller=callloc,
                    ),
                )
                h_ij = h_ij.__add__(
                    Y[col].sharing[row],
                    loc=Location(
                        "BgwMult",
                        description="degree reduction: add zero-encoding",
                        lineno=8,
                        caller=callloc,
                    ),
                )
                H_i = H_i.__add__(
                    h_ij,
                    loc=Location(
                        "BgwMult",
                        description="degree reduction: multiply with lambda matrix (sum one col*row)",
                        lineno=9,
                        caller=callloc,
                    ),
                )
            H.append(H_i)

        self.output_enc = self.f.copy(
            sharing=H,
            secrets=[f_i * g_i for f_i, g_i in zip(f.secrets, g.secrets)],
        )

    @classmethod
    def with_defaults(
        cls: Type[Self], d: int, k: int, e: int, F: CommutativeRing
    ) -> Self:
        n = 2 * d + e + 1

        F_enc, G_enc, rc = make_f_g_encodings(d, e, n, k, F)
        instance = cls(F_enc, G_enc, d, rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set[Expression]:
        return self.randoms

    def lambda_hat_gen(self) -> Matrix:
        """
        Generate the lambda_hat matrix for the degree reduction step.
        The lambda_hat matrix is used to reduce the degree of the polynomial encodings.
        """

        # GENERATE UNMASK
        # Step 1: Vandermonde of u (dimension: 2d+1 x 2d+1)
        van_U = generate_vandermonde(
            self.f.base_ring,
            self.f.secret_support_points + self.f.support_points,
            2 * self.d + 1,
            2 * self.d + 1,
        )
        # Step 2: Vandermonde of x (dimension: n x n)
        van_X = generate_vandermonde(
            self.f.base_ring, self.f.support_points, self.n, self.n
        )
        # Step 3: invert Step 2
        van_X_inv = van_X.inverse()
        # Step 4: take upper (2d+1 x n) submatrix of it
        van_X_upper = van_X_inv[: 2 * self.d + 1, :]
        # Step 5: multiply step 1 and step 4, call this unmask
        unmask = van_U * van_X_upper

        # GENERATE MASK
        # Step 6: Vandermonde of x (dimension: n x n)
        van_X = generate_vandermonde(
            self.f.base_ring, self.f.support_points, self.n, self.n
        )
        # Step 7: take upper (n x d+1) submatrix of it
        van_X_upper = van_X[: self.n, : self.d + 1]
        # Step 8: Vandermonde of u, only first d+1 rows (dimension: d+1 x d+1)
        van_U = generate_vandermonde(
            self.f.base_ring,
            self.f.secret_support_points + self.f.support_points,
            self.d + 1,
            self.d + 1,
        )
        # Step 9: invert Step 8
        van_U_inv = van_U.inverse()
        # Step 10: multiply step 7 and step 9, call this mask
        mask = van_X_upper * van_U_inv

        combined = mask * unmask.submatrix(0, 0, self.d + 1, self.n)
        return combined


class PolyAESSbox(Gadget[PolyEnc]):
    """
    AES Sbox using Poly masking from https://eprint.iacr.org/2017/1047.pdf.
    """

    def __init__(
        self,
        f: PolyEnc,
        rc: count,
        callloc: Optional[Location],
    ):
        assert isinstance(f, PolyEnc), f"{self.name()} requires PolyEnc input."
        super().__init__([f], callloc)
        d = f.d
        to_obsval = to_obsval_factory(f)
        self.randoms = set()
        mk_loc = mk_loc_factory("PolySbox", callloc)
        f2 = PolySquare(f, mk_loc(1, "f2 = f * f"), is_GF2k=True)
        f3 = LaolaMultGadget(f2.output(), f, d, rc, mk_loc(4, "f3 = f2 * f"))
        self.randoms.update(f3.randoms)
        f6 = PolySquare(f3.output(), mk_loc(2, "f6 = f3 * f3"), is_GF2k=True)
        f12 = PolySquare(f6.output(), mk_loc(2, "f12 = f6 * f6"), is_GF2k=True)
        f15 = LaolaMultGadget(
            f3.output(), f12.output(), d, rc, mk_loc(4, "f15 = f3 * f12")
        )
        self.randoms.update(f15.randoms)
        f30 = PolySquare(
            f15.output(), mk_loc(2, "f30 = f15 * f15"), is_GF2k=True
        )
        f60 = PolySquare(
            f30.output(), mk_loc(2, "f60 = f30 * f30"), is_GF2k=True
        )
        f120 = PolySquare(
            f60.output(), mk_loc(2, "f120 = f60 * f60"), is_GF2k=True
        )
        f240 = PolySquare(
            f120.output(), mk_loc(2, "f240 = f120 * f120"), is_GF2k=True
        )
        f252 = LaolaMultGadget(
            f240.output(), f12.output(), d, rc, mk_loc(4, "f252 = f240 * f12")
        )
        self.randoms.update(f252.randoms)
        f254 = LaolaMultGadget(
            f2.output(), f252.output(), d, rc, mk_loc(4, "f254 = f2 * f252")
        )
        self.randoms.update(f254.randoms)

        # generate sharings of constant values to perform addition and multiplication with constants
        enc_63 = f.copy(
            # sharing=[to_obsval(f.variable_ring(f.field(0x63)))]+
            sharing=[
                to_obsval(f.variable_ring(f.field(0x63))) for _ in range(f.n)
            ],
            secrets=[f.field(0x63) for _ in range(f.k)],
        )
        enc_05 = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0x05))) for _ in range(f.n)
            ],
            secrets=[f.field(0x05) for _ in range(f.k)],
        )
        enc_09 = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0x09))) for _ in range(f.n)
            ],
            secrets=[f.field(0x09) for _ in range(f.k)],
        )
        enc_f9 = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0xF9))) for _ in range(f.n)
            ],
            secrets=[f.field(0xF9) for _ in range(f.k)],
        )
        enc_25 = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0x25))) for _ in range(f.n)
            ],
            secrets=[f.field(0x25) for _ in range(f.k)],
        )
        enc_f4 = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0xF4))) for _ in range(f.n)
            ],
            secrets=[f.field(0xF4) for _ in range(f.k)],
        )
        enc_01 = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0x01))) for _ in range(f.n)
            ],
            secrets=[f.field(0x01) for _ in range(f.k)],
        )
        enc_b5 = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0xB5))) for _ in range(f.n)
            ],
            secrets=[f.field(0xB5) for _ in range(f.k)],
        )
        enc_8f = f.copy(
            sharing=[
                to_obsval(f.variable_ring(f.field(0x8F))) for _ in range(f.n)
            ],
            secrets=[f.field(0x8F) for _ in range(f.k)],
        )

        res = enc_63
        tmp = SWPolyMulGadget(f254.output(), enc_05, mk_loc(12, "f254 * 0x05"))
        res = SWPolyAddGadget(
            res, tmp.output(), mk_loc(13, "res += f254 * 0x05")
        )

        x = PolySquare(
            f254.output(), mk_loc(14, "x2 = f254 * f254"), is_GF2k=True
        )
        tmp = SWPolyMulGadget(x.output(), enc_09, mk_loc(15, "x2 * 0x09"))
        res = SWPolyAddGadget(
            res.output(), tmp.output(), mk_loc(16, "res += x2 * 0x09")
        )

        x = PolySquare(x.output(), mk_loc(17, "x4 = x2 * x2"), is_GF2k=True)
        tmp = SWPolyMulGadget(x.output(), enc_f9, mk_loc(18, "x4 * 0xf9"))
        res = SWPolyAddGadget(
            res.output(), tmp.output(), mk_loc(19, "res += x4 * 0xf9")
        )

        x = PolySquare(x.output(), mk_loc(20, "x8 = x4 * x4"), is_GF2k=True)
        tmp = SWPolyMulGadget(x.output(), enc_25, mk_loc(21, "x8 * 0x25"))
        res = SWPolyAddGadget(
            res.output(), tmp.output(), mk_loc(22, "res += x8 * 0x25")
        )

        x = PolySquare(x.output(), mk_loc(23, "x16 = x8 * x8"), is_GF2k=True)
        tmp = SWPolyMulGadget(x.output(), enc_f4, mk_loc(24, "x16 * 0xf4"))
        res = SWPolyAddGadget(
            res.output(), tmp.output(), mk_loc(25, "res += x16 * 0xf4")
        )

        x = PolySquare(x.output(), mk_loc(26, "x32 = x16 * x16"), is_GF2k=True)
        tmp = SWPolyMulGadget(x.output(), enc_01, mk_loc(27, "x32 * 0x01"))
        res = SWPolyAddGadget(
            res.output(), tmp.output(), mk_loc(28, "res += x32 * 0x01")
        )

        x = PolySquare(x.output(), mk_loc(29, "x64 = x32 * x32"), is_GF2k=True)
        tmp = SWPolyMulGadget(x.output(), enc_b5, mk_loc(30, "x64 * 0xb5"))
        res = SWPolyAddGadget(
            res.output(), tmp.output(), mk_loc(31, "res += x64 * 0xb5")
        )

        x = PolySquare(x.output(), mk_loc(32, "x128 = x64 * x64"), is_GF2k=True)
        tmp = SWPolyMulGadget(x.output(), enc_8f, mk_loc(33, "x128 * 0x8f"))
        res = SWPolyAddGadget(
            res.output(), tmp.output(), mk_loc(34, "res += x128 * 0x8f")
        )
        self.output_enc = res.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1

        F_enc, rc = make_f_encodings(d, e, n, k, F)
        instance = cls(f=F_enc, rc=rc, callloc=None)

        return instance

    def output(self) -> PolyEnc:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


def functional_correctness_benchmarks(
    d: int, e: int, k: int, F: CommutativeRing
):
    """
    Run functional correctness benchmarks for the gadgets.
    """

    print(
        f"\n=== Running functional correctness checks with d={d}, e={e}, k={k} ==="
    )
    start = time.perf_counter()
    n = d + e + 1

    sw_add_f_g = SWPolyAddGadget.from_file(d, k, e, F)
    sw_add_f_g.functional_correctness()

    sw_sub_f_g = SWPolySubGadget.from_file(d, k, e, F)
    sw_sub_f_g.functional_correctness()

    FOWZ25_zenc = FOWZ25Zenc.from_file(d, k, e, F)
    FOWZ25_zenc.functional_correctness()

    FOWZ25_szenc = FOWZ25SZenc.from_file(d, k, e, F)
    FOWZ25_szenc.functional_correctness()

    refresh = FOWZ25Refresh.from_file(d, k, e, F)
    refresh.functional_correctness()

    opt_zenc = OptZenc.from_file(d, k, e, F)
    opt_zenc.functional_correctness()

    opt_szenc = OptSZenc.from_file(d, k, e, F)
    opt_szenc.functional_correctness()

    opt_refresh = OptRefresh.from_file(d, k, e, F)
    opt_refresh.functional_correctness()

    refresh_sfres18 = RefreshSFRES18.from_file(d, k, e, F)
    refresh_sfres18.functional_correctness()

    if 2 * d + 1 <= n:
        sw_mul_f_g = SWPolyMulGadget.from_file(d, k, e, F)
        sw_mul_f_g.functional_correctness()
    else:
        print(
            f"Skipping multiplication tests for d={d}, e={e}, k={k} as resulting degree {2 * d} is too high for trivial reconstruction using {n} shares. TODO: implement a degree reduction mechanism."
        )

    if k > 1 and k > d // 2:
        print(
            f"Skipping LaolaMultGadget for k={k} and d={d} (k must be <= d//2)"
        )
    else:
        laola_mult = LaolaMultGadget.from_file(d, k, e, F)
        laola_mult.functional_correctness()

    elapsed = time.perf_counter() - start
    print(f"Execution time: {elapsed} seconds")


def verify_gadgets_NI(
    F: CommutativeRing,
    k: int,
    d: int,
    e: int,
    log: bool = False,
    num_processes: int = 1,
):
    print(f"\n=== Running t-NI security checks with d={d}, e={e}, k={k} ===")
    start = time.perf_counter()

    # Define expected results for each gadget
    expected_results = {
        "SWPolyAddGadget": True,  # Should be t-NI secure
        "SWPolySubGadget": True,  # Should be t-NI secure
        "SWPolyMulGadget": True,  # Should be t-NI secure
        "Refresh": True,  # Should be t-NI secure
        "OptRefresh": True,  # Should be t-NI secure
        "RefreshSFRES18": True,  # Should be t-NI secure
        "LaolaMultGadget": True,  # Should be t-NI secure
    }

    results = {}

    # Test each gadget and track results
    try:
        sw_add_f_g = SWPolyAddGadget.from_file(d, k, e, F)
        results["SWPolyAddGadget"] = sw_add_f_g.verify_t_NI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["SWPolyAddGadget"] = f"ERROR: {exc}"

    try:
        sw_sub_f_g = SWPolySubGadget.from_file(d, k, e, F)
        results["SWPolySubGadget"] = sw_sub_f_g.verify_t_NI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["SWPolySubGadget"] = f"ERROR: {exc}"

    try:
        sw_mul_f_g = SWPolyMulGadget.from_file(d, k, e, F)
        results["SWPolyMulGadget"] = sw_mul_f_g.verify_t_NI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["SWPolyMulGadget"] = f"ERROR: {exc}"

    try:
        old_refresh = FOWZ25Refresh.from_file(d, k, e, F)
        results["Refresh"] = old_refresh.verify_t_NI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["Refresh"] = f"ERROR: {exc}"

    try:
        opt_refresh = OptRefresh.from_file(d, k, e, F)
        results["OptRefresh"] = opt_refresh.verify_t_NI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["OptRefresh"] = f"ERROR: {exc}"

    try:
        refresh_sfres18 = RefreshSFRES18.from_file(d, k, e, F)
        results["RefreshSFRES18"] = refresh_sfres18.verify_t_NI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["RefreshSFRES18"] = f"ERROR: {exc}"

    if k > 1 and k > d // 2:
        print(
            f"Skipping LaolaMultGadget for k={k} and d={d} (k must be <= d//2)"
        )
        results["LaolaMultGadget"] = "SKIPPED: k > d//2"
    else:
        try:
            laola_mult = LaolaMultGadget.from_file(d, k, e, F)
            results["LaolaMultGadget"] = laola_mult.verify_t_NI(
                d, num_worker=num_processes, log=log
            )
        except Exception as exc:
            results["LaolaMultGadget"] = f"ERROR: {exc}"

    # Print result comparison
    print("\n=== Verification Results Summary ===")
    print(f"Parameters: d={d}, e={e}, k={k}")
    print(f"{'Gadget':<20} {'Expected':<10} {'Actual':<10} {'Match?':<10}")
    print("-" * 50)

    all_match = True
    for gadget, expected in expected_results.items():
        if gadget in results:
            actual = results[gadget]
            if isinstance(actual, bool):
                matches = actual == expected
                if not matches:
                    all_match = False
                print(
                    f"{gadget:<20} {str(expected):<10} {str(actual):<10} {'✓' if matches else '✗'}"
                )
            else:
                print(f"{gadget:<20} {str(expected):<10} {actual:<10} {'?'}")
                all_match = False

    print("\nOverall test result: " + ("PASS" if all_match else "FAIL"))

    elapsed = time.perf_counter() - start
    print(f"Execution time for t-NI checks: {elapsed:.3f} seconds")
    return results


def verify_gadgets_SNI(
    F: CommutativeRing,
    k: int,
    d: int,
    e: int,
    log: bool = False,
    num_processes: int = 1,
):
    print(f"\n=== Running t-SNI security checks with d={d}, e={e}, k={k} ===")
    start = time.perf_counter()

    # Define expected results for each gadget
    expected_results = {
        "SWPolyAddGadget": False,  # Not t-SNI secure
        "SWPolySubGadget": False,  # Not t-SNI secure
        "SWPolyMulGadget": False,  # Not t-SNI secure
        "Refresh": True,  # Should be t-SNI secure
        "OptRefresh": True,  # Should be t-SNI secure
        "RefreshSFRES18": False,  # Should not be t-SNI secure, at least due to counterexample with d=t=3 and prime field
        # unknown whether it is t-SNI for d = t < 3
        "LaolaMultGadget": True,  # Should be t-SNI secure
    }

    results = {}

    # Test each gadget and track results
    try:
        sw_add_f_g = SWPolyAddGadget.from_file(d, k, e, F)
        results["SWPolyAddGadget"] = sw_add_f_g.verify_t_SNI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["SWPolyAddGadget"] = f"ERROR: {exc}"

    try:
        sw_sub_f_g = SWPolySubGadget.from_file(d, k, e, F)
        results["SWPolySubGadget"] = sw_sub_f_g.verify_t_SNI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["SWPolySubGadget"] = f"ERROR: {exc}"

    try:
        sw_mul_f_g = SWPolyMulGadget.from_file(d, k, e, F)
        results["SWPolyMulGadget"] = sw_mul_f_g.verify_t_SNI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["SWPolyMulGadget"] = f"ERROR: {exc}"

    try:
        old_refresh = FOWZ25Refresh.from_file(d, k, e, F)
        results["Refresh"] = old_refresh.verify_t_SNI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["Refresh"] = f"ERROR: {exc}"

    try:
        opt_refresh = OptRefresh.from_file(d, k, e, F)
        results["OptRefresh"] = opt_refresh.verify_t_SNI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["OptRefresh"] = f"ERROR: {exc}"

    try:
        refresh_sfres18 = RefreshSFRES18.from_file(d, k, e, F)
        results["RefreshSFRES18"] = refresh_sfres18.verify_t_SNI(
            d, num_worker=num_processes, log=log
        )
    except Exception as exc:
        results["RefreshSFRES18"] = f"ERROR: {exc}"

    if k > 1 and k > d // 2:
        print(
            f"Skipping LaolaMultGadget for k={k} and d={d} (k must be <= d//2)"
        )
        results["LaolaMultGadget"] = "SKIPPED: k > d//2"
    else:
        try:
            laola_mult = LaolaMultGadget.from_file(d, k, e, F)
            results["LaolaMultGadget"] = laola_mult.verify_t_SNI(
                d, num_worker=num_processes, log=log
            )
        except Exception as exc:
            results["LaolaMultGadget"] = f"ERROR: {exc}"

    # Print result comparison
    print("\n=== Verification Results Summary ===")
    print(f"Parameters: d={d}, e={e}, k={k}")
    print(f"{'Gadget':<20} {'Expected':<10} {'Actual':<10} {'Match?':<10}")
    print("-" * 50)

    all_match = True
    for gadget, expected in expected_results.items():
        if gadget in results:
            actual = results[gadget]
            if isinstance(actual, bool):
                matches = actual == expected
                if not matches:
                    all_match = False
                print(
                    f"{gadget:<20} {str(expected):<10} {str(actual):<10} {'✓' if matches else '✗'}"
                )
            else:
                print(f"{gadget:<20} {str(expected):<10} {actual:<10} {'?'}")
                all_match = False

    print("\nOverall test result: " + ("PASS" if all_match else "FAIL"))

    elapsed = time.perf_counter() - start
    print(f"Execution time for t-SNI checks: {elapsed:.3f} seconds")
    return results


if __name__ == "__main__":

    @contextmanager
    def tee_stdout(file_path):
        """Context manager that writes stdout to both terminal and file."""

        class TeeOutput:
            def __init__(self, file, original_stdout):
                self.file = file
                self.original_stdout = original_stdout

            def write(self, message):
                self.file.write(message)
                self.original_stdout.write(message)

            def flush(self):
                self.file.flush()
                self.original_stdout.flush()

        original_stdout = sys.stdout
        try:
            with open(file_path, "w") as f:
                sys.stdout = TeeOutput(f, original_stdout)
                yield
        finally:
            sys.stdout = original_stdout

    F = GF(2**8)
    # F = GF(7)
    num_func_tests = 1

    min_k, max_k = 1, 1
    min_e, max_e = 0, 2
    min_d, max_d = 1, 3
    with tee_stdout("functional_gadget_benchmarks.log"):
        for k in range(min_k, max_k + 1):
            for d in range(min_d, max_d + 1):  # d > 0 and k <= d
                for e in range(min_e, max_e + 1):  # e >= 0
                    if (
                        k > d
                    ):  # k must be less than or equal to d, cant encode more secrets than degree
                        continue
                    # functional_correctness_benchmarks(d, e, k, F)
                    # verify_gadgets_NI(
                    #    F=F,
                    #    k=k,
                    #    d=d,
                    #    e=e,
                    #    log=False,
                    #    num_processes=1
                    # )

                    verify_gadgets_NI(
                        F=F,
                        k=k,
                        d=d,
                        e=e,
                        log=False,
                        num_processes=64 if d > 1 else 16,
                    )
