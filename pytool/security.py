# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from sage.all import GF, var, PolynomialRing
from sage.rings.polynomial.multi_polynomial import MPolynomial
from sage.symbolic.expression import Expression
from typing import Iterable, Sequence, Set
from enum import Enum, auto


class SecurityNotion(Enum):
    """
    Represents the type of security notion used in the verification.

    PS: t-probing security notion, i.e., all t-tuples are independent of secret variables.
    NI: t-non-interference security notion, i.e., all t-tuples can be simulated using at most t many shares of each input.
    SNI: t-strong non-interference security notion, i.e., all t-tuples can be simulated using at most t_internal many shares of each input.
    """

    PS = auto()
    NI = auto()
    SNI = auto()

    def __str__(self):
        if self == SecurityNotion.PS:
            return "Probing Security"
        elif self == SecurityNotion.NI:
            return "Non-Interference"
        elif self == SecurityNotion.SNI:
            return "Strong Non-Interference"
        else:
            return f"Unknown({self.name})"


def is_t_non_interferent(
    t: int, secret_vars: Sequence[Set[Expression]], exprs: Sequence[Expression]
) -> bool:
    """
    Checks whether the combined system of expressions `exprs`
    depends on at most `t` variables of *each* of the given
    secret-variable sets in `secret_vars`.

    Parameters
    ----------
    t : int
        The maximum allowed number of secret variables that
        may influence the expressions.
    secret_vars : Sequence[Set[Expr]]
        A list of “secret” variable sets.  For each set in here,
        it is checked that at most `t` of its symbols appear in `exprs`.
    exprs : Sequence[Expr]
        The Sympy expressions whose dependency is checked.

    Returns
    -------
    bool
        True iff, for *every* set in `secret_vars`, the total number
        of its symbols that actually occur in `exprs` is ≤ `t`.
        False as soon as any set has > `t` symbols in common.
    """
    # 1) Collect all symbols appearing in any of the expressions.
    all_syms: Set[Expression] = set().union(*(e.variables() for e in exprs))

    # 2) For each secret-set, check intersection size ≤ t.
    for sv in secret_vars:
        # intersect the smaller set into the larger for a slight speedup
        if len(sv) < len(all_syms):
            common = sv & all_syms
        else:
            common = all_syms & sv

        if len(common) > t:
            print(
                f"Non-interference violated: {len(common)} > {t} secret vars in common: {common}"
            )
            return False

    # 3) Check passed for all sets.
    return True


def test_is_t_non_interferent_ex1():
    x, y, z, w = var("x y z w")
    exprs = [x + y, z * 2]
    secret_sets = [{x, y, w}, {z, w}]
    assert is_t_non_interferent(2, secret_sets, exprs)
    assert not (is_t_non_interferent(1, secret_sets, exprs))


def test_is_t_non_interferent_ex2():
    x, y, z, w, a = var("x y z w a")
    exprs = [x + y + a, w**1 + z**2]
    secret_sets = [{x, y, w}, {z, a, w}]
    assert not (is_t_non_interferent(2, secret_sets, exprs))


### TODO: hardcore optimized version for performance increase
def is_t_non_interferent_poly(
    t: int,
    secret_vars: Sequence[Set[MPolynomial]],
    depsets: Iterable[Set[MPolynomial]],
    log: bool = False,
) -> bool:
    """
    Checks whether the `depsets` of a combined system of expressions
    depends on at most `t` variables of *each* of the given
    secret-variable sets in `secret_vars`.

    Parameters
    ----------
    t : int
        The maximum allowed number of secret variables that
        may influence the expressions.
    secret_vars : Sequence[Set[MPolynomial]]
        A list of “secret” variable sets.  For each set in here,
        it is checked that at most `t` of its symbols appear in `exprs`.
    depsets : Iterable[Set[MPolynomial]]
        One depset per expression to be checked.

    Returns
    -------
    bool
        True iff, for *every* set in `secret_vars`, the total number
        of its symbols that actually occur in `depsets` is ≤ `t`.
        False as soon as any set has > `t` symbols in common.
    """
    # 1) Collect all symbols appearing in any of the expressions.
    all_syms: Set[MPolynomial] = set().union(*(d for d in depsets))

    # 2) For each secret-set, check intersection size ≤ t.
    for sv in secret_vars:
        # intersect the smaller set into the larger for a slight speedup
        if len(sv) < len(all_syms):
            common = sv & all_syms
        else:
            common = all_syms & sv

        if len(common) > t:
            if log:
                print(
                    f"Non-interference violated: {len(common)} > {t} secret vars in common: {common}"
                )
            return False

    # 3) Check passed for all sets.
    return True


def test_is_t_non_interferent_poly_ex1_gf256():
    F = GF(2**8, name="a")
    R = PolynomialRing(F, names=("x", "y", "z", "w"))
    x, y, z, w = R.gens()

    exprs = [x + y, R(2) * w, z**2]

    secret_sets = [{x, y, w}, {z, w}]

    assert is_t_non_interferent_poly(2, secret_sets, exprs)
    assert not is_t_non_interferent_poly(1, secret_sets, exprs)


def test_is_t_non_interferent_poly_ex2_gf256():
    F = GF(2**8, name="a")
    R = PolynomialRing(F, names=("x", "y", "z", "w"))
    x, y, z, w = R.gens()

    exprs = [x + y, R(1) * w, z**2]

    secret_sets = [{x, y, w}, {z, w}]

    assert not is_t_non_interferent_poly(2, secret_sets, exprs)


def test_is_t_non_interferent_poly_ex3_gf256():
    F = GF(2**8, name="a")
    R = PolynomialRing(F, names=("x", "y", "z", "w", "a"))
    x, y, z, w, a_ = R.gens()

    exprs = [x + y + a_, R(1) * w, z**2]

    secret_sets = [{x, y, w}, {z, a_, w}]

    assert not is_t_non_interferent_poly(2, secret_sets, exprs)
