# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
import psutil
import sys
import time
import traceback
import tqdm
import itertools
from functools import cmp_to_key
from observations import Observation, ObservationGraph, ObservationTupleManager
from polyring import (
    _roots_cache_sanitize_constraints,
    has_full_row_rank_cached,
    has_no_roots_cached,
    prepare_cache,
    print_full_rank_cache_stats,
    print_roots_cache_stats,
)
from math import comb
from multiprocessing import cpu_count, Pool, Manager
from encoding import Encoding
from rewrite_rules import (
    FDedup,
    Destruct,
    ExpOtp,
    Permute,
    RewriteRule,
)
from security import SecurityNotion
from sage.all import Matrix
from sage.rings.ring import CommutativeRing
from sage.rings.polynomial.multi_polynomial import MPolynomial
from timeout import timeout
from typing import Dict, Optional, Sequence, Set, Callable, Tuple, Any

# Cache results of factorization to speed up repeated calls
_manager = Manager()
_worker_globals: dict[str, Any] = {}


def __rnd_matrix(
    R: CommutativeRing,
    R_gens_to_idx: dict,
    observations: Sequence[Observation],
    random_vars: Set[MPolynomial],
    secret_vars: Sequence[Set[MPolynomial]],
    log: bool = False,
) -> tuple[
    Matrix,
    list[MPolynomial],
    list[bool],
    list[bool],
    Dict[Observation, list[MPolynomial]],
]:
    """
    Collect the coefficients of random variables in `observations` into a Matrix.
    Ignore any randoms that
      • occur in a monomial with more than one random, or
      • occur to exponent > 1 in any monomial.
    Rows correspond to observations,
    columns correspond to random_vars satisfying above criteria,
    Entry (i,j) = coefficient.
    """
    K = R.base_ring()

    # map each random variable to a column index
    sorted_rvs = sorted(random_vars, key=str)
    rv_to_col = {rv: idx for idx, rv in enumerate(sorted_rvs)}
    m = len(observations)
    n = len(rv_to_col)
    M = Matrix(K, m, n, lambda i, j: K.zero())
    residues = [False] * m
    rnd_product = [False] * m

    # Pre-build a lookup list of mappings to assosciate random variables and secrets with their indices
    rv_idx_list = []
    for rv in random_vars:
        idx = R_gens_to_idx.get(rv)
        if idx is not None:
            rv_idx_list.append((rv, idx))

    secret_idx = []
    for group in secret_vars:
        for s in group:
            idx = R_gens_to_idx.get(s)
            if idx is not None:
                secret_idx.append(idx)

    secret_dep_coeffs = {obs: [] for obs in observations}
    # mark bad & collect
    bad = set()
    seen = set()
    for i, obs in enumerate(observations):
        obs_sec_list = secret_dep_coeffs[obs]
        for exp_tup, coeff in obs.get_value().dict().items():
            if coeff.is_zero():
                continue

            secret_dep = any(exp_tup[idx] != 0 for idx in secret_idx)

            # build {rv: exponent} for those random variables that actually appear
            rv_exponents = {}
            for rv, idx in rv_idx_list:
                exp = exp_tup[idx]
                if exp != 0:
                    rv_exponents[rv] = exp

            if log:
                print(
                    f"monomial {exp_tup} with exponents of random variables: {rv_exponents}"
                )

            if not rv_exponents:
                if secret_dep:
                    obs_sec_list.append(coeff)
                residues[i] = True
                continue

            if len(rv_exponents) > 1 or sum(exp_tup) > 1:
                # ban all involved randoms
                residues[i] = True
                rnd_product[i] = (
                    True  # observation i has at least one product of random variables.
                )
                bad |= rv_exponents.keys()
                if secret_dep:
                    obs_sec_list.append(coeff)
                if log:
                    print(
                        f"observed combinations of random variables or random variable with exponent != 1 {rv_exponents.items()}"
                    )
            else:  # univariate monomial with exponent 1
                rv = next(iter(rv_exponents.keys()))
                j = rv_to_col[rv]
                if log:
                    print(f"setting coefficient M[{i}, {j}] = {coeff}.")
                seen.add(rv)
                M[i, j] = coeff

    # mark all unseen random variables (with zero columns) as bad
    bad.update(random_vars - seen)
    # drop the bad columns
    bad_cols = sorted(rv_to_col[rv] for rv in bad)
    if bad_cols:
        M = M.delete_columns(bad_cols)

    r_vec = [rv for rv in sorted_rvs if rv not in bad]
    return M, r_vec, residues, rnd_product, secret_dep_coeffs


def __unreduced_echelon_and_mapping(
    constraints_hash: str,
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    M: Matrix,
    log: bool = False,
):
    """
    Compute an (unreduced) row-echelon form of M over a field (or fraction field)
    without ever dividing a pivot row by its pivot.  Returns
       • U : the echelon-form matrix
       • pivots : list of ((row, col), pivot_value) taken from the original M
    """

    U = M[:, :]

    m, n = U.nrows(), U.ncols()
    Urow_to_Mrow = list(range(m))
    pivots = []
    r = 0
    for c in range(n):
        # find a non‐zero in column c at or below row r
        pivot_row = None
        for i in range(r, m):
            p = U[i, c]
            # Note: this check is equivalent to the determinant's pivots checked later FOR THIS PARTICULAR IMPLEMENTATION of gaussian elimination but not necessarily in general
            if p != 0 and (
                p.numerator() == 1
                or has_no_roots_cached(
                    constraints_hash, groebner, S, p.numerator(), log=log
                )
            ):
                if log:
                    print(f"checked absence of roots in numerator of pivot {p}")
                pivot_row = i
                break
        if pivot_row is None:
            continue  # no pivot in this column

        # swap it up into row r
        U.swap_rows(r, pivot_row)
        Urow_to_Mrow[r], Urow_to_Mrow[pivot_row] = (
            Urow_to_Mrow[pivot_row],
            Urow_to_Mrow[r],
        )

        # select the pivot element
        p = U[r, c]
        # record the pivot position and its value
        pivots.append(((r, c), p))

        # eliminate all entries below the pivot
        for i in range(r + 1, m):
            if U[i, c] != 0:
                U[i, :] = U[i, :] - U[i, c] * U[r, :] / p
        r += 1
        if r == m:
            break

    return U, pivots, Urow_to_Mrow


def __apply_safe_destruct_rule(
    observations: list[Observation],
    observations_clean: list[Observation],
    obsgraph: ObservationGraph,
    security_notion: SecurityNotion,
    initial_len: int,
    log: bool = False,
) -> Optional[Tuple[list[Observation], ...]]:
    """
    Try to apply a safe destruct, in case that this reduces to a tuple of size <= t, we can return `None` to indicate that a different tuple covers the current one due to enumeration.
    If the tuple is large we return its safe destruct result additionally. Should no rewrite be possible we return the original observations.
    """
    current_obs_ids = set(o.get_id() for o in observations)
    if log:
        print("try to apply safe destruct rule")
    for obs in observations:
        parent_ids = set(obs.get_parents())
        if not parent_ids:
            continue
        if obs.get_id() in parent_ids:
            raise RuntimeError(
                "An observation is its own parent, something went very wrong. Abort verification!"
            )
        if len(parent_ids & current_obs_ids) >= len(
            parent_ids
        ) - 1 or parent_ids.issubset(current_obs_ids):
            if len(observations) <= initial_len:
                if log:
                    print(
                        f"Safe destruct successfull with defered obsset on obs {obs} with parents {parent_ids} "
                    )
                return None
            nondestr_obs = [
                o for o in observations if o.get_id() != obs.get_id()
            ]
            destr_obs = []
            for p in parent_ids:
                if p in current_obs_ids:
                    continue
                pobs = obsgraph.get_observation(security_notion, p)
                pobs_rules: list[RewriteRule] = [
                    rrule
                    for rrule in obs.applied_rules
                    if isinstance(rrule, Destruct)
                ]
                pobs = Observation(
                    pobs.get_value(),
                    pobs.get_id(),
                    pobs.get_parents(),
                    pobs.get_location(),
                    pobs_rules,
                )
                destr_obs.append(
                    pobs.rewrite(
                        pobs.get_value(),
                        rrule=Destruct(obs.get_id(), pobs.get_id(), safe=False),
                    )
                )
            if (
                len(__apply_deduplicate_rule(destr_obs + nondestr_obs, log))
                <= initial_len
            ):
                return None
            return destr_obs + nondestr_obs, destr_obs + nondestr_obs
    # couldnt do anything
    return observations, observations_clean


def __apply_destruct_rule(
    M_row_has_rndprod: list[bool],
    observations: Sequence[Observation],
    observations_clean: Sequence[Observation],
    obsgraph: ObservationGraph,
    security_notion: SecurityNotion,
    secret_vars: Sequence[Set[MPolynomial]],
    log: bool = False,
) -> Optional[Tuple[list[Observation], ...]]:
    """
    Try to apply a destruct on a single observation based on heuristics. Should no rewrite be possible we return `None`.
    """
    current_obs_ids = set(o.get_id() for o in observations_clean)
    obs_prod = [
        obs
        for obsidx, obs in enumerate(observations)
        if M_row_has_rndprod[obsidx]
    ]
    secret_vars: Set[MPolynomial] = set().union(*(s for s in secret_vars))

    # def common_ancestor_and_distance(id_a: int, id_b: int):
    #     ancestors_a = {id_a: 0}
    #     ancestors_b = {id_b: 0}
    #     worklist_a = {id_a}
    #     worklist_b = {id_b}
    #     while bool(worklist_a) or bool(worklist_b):
    #         tmp = set()
    #         for id in worklist_a:
    #             id_parents = obsgraph.get_observation(
    #                 security_notion, id
    #             ).get_parents()
    #             tmp.update(set(id_parents))
    #             distance_to_id = ancestors_a[id]
    #             for parent in id_parents:
    #                 ancestors_a[parent] = distance_to_id + 1
    #                 if parent in ancestors_b.keys():
    #                     return (parent, distance_to_id + 1, ancestors_b[parent])

    #         worklist_a = tmp

    #         tmp = set()
    #         for id in worklist_b:
    #             id_parents = obsgraph.get_observation(
    #                 security_notion, id
    #             ).get_parents()
    #             tmp.update(set(id_parents))
    #             distance_to_id = ancestors_b[id]
    #             for parent in id_parents:
    #                 ancestors_b[parent] = distance_to_id + 1
    #                 if parent in ancestors_a.keys():
    #                     return (parent, ancestors_a[parent], distance_to_id + 1)

    #         worklist_b = tmp
    #     return None

    # def cmp_obs(a: Observation, b: Observation) -> int:
    #     # return <0 if a before b, 0 if equal, >0 if a after b
    #     res = common_ancestor_and_distance(a.get_id(), b.get_id())
    #     if res is not None:
    #         common_ancestor, dist_a, dist_b = res
    #         print(
    #             f"common ancestor of a.id={a.get_id()} with dist_a {dist_a}, b.id={b.get_id()} with dist_b {dist_b} is {common_ancestor}"
    #         )
    #         if dist_a > dist_b:
    #             return -1
    #         elif dist_b > dist_a:
    #             return 1
    #     dep_set_a = a.get_depset() & secret_vars
    #     dep_set_b = b.get_depset() & secret_vars
    #     if len(dep_set_a) == len(dep_set_b):
    #         return (b.get_id() > a.get_id()) - (b.get_id() < a.get_id())
    #     else:
    #         return (len(dep_set_b) > len(dep_set_a)) - (
    #             len(dep_set_b) < len(dep_set_a)
    #         )

    def cmp_obs(a: Observation, b: Observation) -> int:
        # return <0 if a before b, 0 if equal, >0 if a after b
        if obsgraph.is_descendant(a.get_id(), b.get_id(), security_notion):
            return -1
        elif obsgraph.is_descendant(b.get_id(), a.get_id(), security_notion):
            return 1
        else:
            dep_set_a = a.get_depset() & secret_vars
            dep_set_b = b.get_depset() & secret_vars
            if len(dep_set_a) == len(dep_set_b):
                return (b.get_id() > a.get_id()) - (b.get_id() < a.get_id())
            return (len(dep_set_b) > len(dep_set_a)) - (
                len(dep_set_b) < len(dep_set_a)
            )

    obs_prod.sort(key=cmp_to_key(cmp_obs), reverse=False)

    for obs in obs_prod:
        parent_ids = set(obs.get_parents())
        if not parent_ids:
            continue
        if obs.get_id() in parent_ids:
            raise RuntimeError(
                "An observation is its own parent, something went very wrong. Abort verification!"
            )

        # reset applied rules (except destruct) by using the clean observations
        nondestr_obs = [
            o for o in observations_clean if o.get_id() != obs.get_id()
        ]
        destr_obs = []
        for p in parent_ids:
            if p in current_obs_ids:
                continue
            pobs = obsgraph.get_observation(security_notion, p)
            pobs_rules: list[RewriteRule] = [
                rrule
                for rrule in obs.applied_rules
                if isinstance(rrule, Destruct)
            ]
            pobs = Observation(
                pobs.get_value(),
                pobs.get_id(),
                pobs.get_parents(),
                pobs.get_location(),
                pobs_rules,
            )
            destr_obs.append(
                pobs.rewrite(
                    pobs.get_value(),
                    rrule=Destruct(obs.get_id(), pobs.get_id(), safe=False),
                )
            )
        if log:
            new_obs_str = "\n".join(
                obs.print(
                    id=True,
                    value=False,
                    parents=True,
                    applied_rules=True,
                    loc=True,
                    depset=True,
                )
                for obs in destr_obs
            )
            print(f"Applying destruct rule on {obs} ->\n{new_obs_str}.")
        observations_new = nondestr_obs + destr_obs
        observations_clean_new = [o for o in observations_new]
        return (observations_new, observations_clean_new)
    # destruct is unsuccessfull, return None
    return None


def __apply_deduplicate_rule(
    observations: Sequence[Observation], log: bool = False
) -> list[Observation]:
    seen: set[MPolynomial] = set()
    unique: list[Observation] = []
    has_duplicates = False
    for obs in observations:
        # Important: compare the expression instead of the whole Observation to capture rewriting
        if obs.get_value() not in seen:
            seen.add(obs.get_value())
            unique.append(obs)
        else:
            has_duplicates = True

    if has_duplicates and log:
        print("Removed duplicate entries from observations.")

    return unique


def __apply_factor_deduplicate_rule(
    R: CommutativeRing,
    observations: Sequence[Observation],
    initial_len: int,
    log: bool = False,
) -> Optional[list[Observation]]:
    """
    This rewrite attempts to find observations s.t. obs2 = f * obs1, where obs1 is contained in the `observations` and f is a factor only depending on parameter variables, i.e. no secrets, publics or randoms.
    If such a factor is found, obs2 is substituted by f, since the leakage of obs1 is already captured in the rest of the tuple. Note that a successful application on a set <= initial_len defers the tuple due to enumeration.
    """
    factored_obs = False
    obs_defactored = list(observations)
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
                    print(f"obs 1: {obs1}")
                    print(f"obs 2: {obs2}")
                    print(f"factor: {factor}")
                obs_defactored[j] = obs2.rewrite(
                    R(factor), FDedup(R(factor), obs2.get_value())
                )
                factored_obs = True

    if factored_obs and n <= initial_len and log:
        print(
            "FDedup successfull and len(obs) <= initial length, defering tuple."
        )
        return None

    return obs_defactored


def __elim_lin_dep_obs(
    S: CommutativeRing,
    M: Matrix,
    E: Matrix,
    map_E_row_to_M_row,
    perm_obs: list[Observation],
    r_vec: list[MPolynomial],
    sec_dep_coeffs: Dict[Observation, list[MPolynomial]],
    log: bool = False,
):
    del_col: Set[int] = set()
    keep_row: list[int] = []
    E_row_is_lin_dep = [False for _ in range(E.nrows())]
    for i in range(E.nrows()):
        if all(E[i, j] == S.zero() for j in range(E.ncols())):
            E_row_is_lin_dep[i] = True

    M_row_is_lin_dep = [False for _ in range(M.nrows())]
    for i, entry in enumerate(E_row_is_lin_dep):
        M_row_is_lin_dep[map_E_row_to_M_row[i]] = entry

    for i, lin_dep in enumerate(M_row_is_lin_dep):
        if not lin_dep:
            keep_row.append(i)
            continue
        if log:
            print(
                f"row {i} of {M} with entries \n{M[i, :]} \n is linearly dependent an removed."
            )
        for j in range(M.ncols()):
            if M[i, j] != S(0):
                del_col.add(j)

    keep_col: list[int] = [i for i in range(len(r_vec)) if i not in del_col]
    r_vec_pruned = [r_vec[i] for i in keep_col]
    perm_obs_pruned = [perm_obs[i] for i in keep_row]
    elim_obs = [perm_obs[i] for i in range(len(perm_obs)) if i not in keep_row]
    # produce per-observation secret-dependency mapping for the pruned observations
    sec_dep_coeffs_pruned_map: Dict[Observation, list[MPolynomial]] = {
        obs: (
            sec_dep_coeffs.get(obs, list()) if obs in sec_dep_coeffs else list()
        )
        for obs in perm_obs_pruned
    }
    M_pruned = Matrix(
        S.fraction_field(), [[M[i, j] for j in keep_col] for i in keep_row]
    )
    if log:
        for e in elim_obs:
            print(f"obs {e} is lin dep and eliminated.")
    return (
        M_pruned,
        perm_obs_pruned,
        elim_obs,
        r_vec_pruned,
        sec_dep_coeffs_pruned_map,
    )


def __elim_secret_indep_obs(
    S: CommutativeRing,
    M: Matrix,
    perm_obs: list[Observation],
    r_vec: list[MPolynomial],
    sec_dep_coeffs: Dict[Observation, list[MPolynomial]],
):
    """
    Eliminate residue free observations and their associated randoms from the matrix `M`, `perm_obs`, `r_vec` and `sec_dep_coeffs`.
    - `S`: Ring the MPolynomials live in.
    - `M`: Matrix containing the coeffs of linear randoms for each observation.
    - `M_row_has_residue`: A list indicating which observations have a residue, i.e. are secret dependent.
    - `perm_obs`: Considered observations.
    - `sec_dep_coeffs`: Map from each observation to its secret coefficients.
    """
    del_col: Set[int] = set()
    keep_row: list[int] = []
    for i, obs in enumerate(perm_obs):
        if not len(sec_dep_coeffs.get(obs, list())) == 0:
            keep_row.append(i)
            continue
        for j in range(M.ncols()):
            if M[i, j] != S(0):
                del_col.add(j)
    keep_col: list[int] = [i for i in range(len(r_vec)) if i not in del_col]
    r_vec_pruned = [r_vec[i] for i in keep_col]
    perm_obs_pruned = [perm_obs[i] for i in keep_row]
    elim_obs = [perm_obs[i] for i in range(len(perm_obs)) if i not in keep_row]
    # produce per-observation secret-dependency mapping for the pruned observations
    sec_dep_coeffs_pruned_map: Dict[Observation, list[MPolynomial]] = {
        obs: (sec_dep_coeffs.get(obs, []) if obs in sec_dep_coeffs else [])
        for obs in perm_obs_pruned
    }
    M_pruned = Matrix(
        S.fraction_field(), [[M[i, j] for j in keep_col] for i in keep_row]
    )

    return (
        M_pruned,
        perm_obs_pruned,
        elim_obs,
        r_vec_pruned,
        sec_dep_coeffs_pruned_map,
    )


def __try_abstract_permute_rule(
    constraints: Tuple[Sequence[MPolynomial], ...],
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    M: Matrix,
    perm_obs: list[Observation],
    rands: list[MPolynomial],
    secret_dep_coeffs: Set[MPolynomial],
    log: bool = False,
) -> Optional[list[Observation]]:
    """
    Try to perform the abstact permute rule, which attempts to find |obs| many jointly non-vanishing randoms to perform a rewrite to full independence.
    In addition to the usual constraints, this rule also factors in that amongst all coefficient of secret monomials, there must be at least one non-vanishing coeff, otherwise the tuple would be indep by default.
    """
    if M.nrows() > M.ncols() or len(rands) < len(perm_obs):
        print(f"M has dims {M.nrows()} x {M.ncols()} with matrix: \n {M}")
        if log:
            print(
                "not enough randoms to perform an abstract permute in all associated observations"
            )
        return None
    if not has_full_row_rank_cached(
        constraints, groebner, S, M, secret_dep_coeffs, log
    ):
        if log:
            print("__try_abstract_permute: matrix does not have full rank")
        return None
    if log:
        print("__try_abstract_permute: matrix has full rank")
    rewritten_obs = []
    rewrite_rands = rands[: len(perm_obs)]
    for r, obs in zip(rands, perm_obs):
        rewritten_obs.append(
            obs.rewrite(
                r,
                rrule=Permute(
                    rewrite_rands, this_rv=r, this_expr=obs.get_value()
                ),
            )
        )
    return rewritten_obs


def __try_abstract_permute_all_subsets(
    constraints: Tuple[Sequence[MPolynomial], ...],
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    M: Matrix,
    perm_obs: list[Observation],
    r_vec: list[MPolynomial],
    sec_dep_coeffs_map: Dict[Observation, list[MPolynomial]],
    log: bool = False,
) -> Optional[list[Observation]]:
    """
    Try permutes on sub-combinations of the candidate rows.
    Start with larger subsets first to (hopefully) rewrite more obs.
    This tries all sensible combinations of rows, it can be expensive.
    For each selection an abstract permute invocation is performed.
    If abstract permute yields rewritten rows, integrate them into the full perm_obs and return the full list.
    If none succeed, return the original perm_obs_pruned unchanged.
    """

    (
        M,
        perm_obs,
        elim_obs,
        r_vec,
        sec_dep_coeffs_map,
    ) = __elim_secret_indep_obs(
        S,
        M,
        perm_obs,
        r_vec,
        sec_dep_coeffs_map,
    )
    m = M.nrows()
    n = M.ncols()

    if m == 0 or n == 0:
        if log:
            print(
                f"not enough rows={m} or cols={n} to try APerm for matrix M:\n{M}\nwith obs:"
            )
            for o in perm_obs:
                print(o)
        return None

    # precompute for each row which columns are non-zero
    row_nonzero_cols = [
        set(j for j in range(n) if M[i, j] != 0) for i in range(m)
    ]

    # limit maximum subset size to available randoms, permute cant target more
    max_selected_rows = min(len(r_vec), m)

    # try larger rewrites first, on failure try smaller subsets
    for k in range(max_selected_rows, 0, -1):
        if log:
            print(f"Trying subsets of size {k} (rows {m} x cols {n}).")
        for subset_rows in itertools.combinations(range(m), k):
            subset_rows_set = set(subset_rows)
            # removed rows are those not selected
            removed_rows = set(range(m)) - subset_rows_set
            # forbidden columns = union of non-zero columns in removed rows
            forbidden_cols = (
                set().union(*(row_nonzero_cols[r] for r in removed_rows))
                if removed_rows
                else set()
            )
            allowed_cols = [c for c in range(n) if c not in forbidden_cols]
            if len(allowed_cols) < k:
                # not enough usable randoms for this subset
                if log:
                    print(
                        f"Subset {subset_rows} skipped: only {len(allowed_cols)} usable randoms < {k}."
                    )
                continue
            # build submatrix restricted to selected rows and allowed columns
            M_sub = Matrix(
                M.base_ring(),
                [[M[r, c] for c in allowed_cols] for r in subset_rows],
            )
            # build list of perm_obs for selected rows (preserve order of rows_idx)
            perm_obs_subset = [perm_obs[r] for r in subset_rows]
            # allowed random symbols
            rands_allowed = [r_vec[c] for c in allowed_cols]
            # secret dependent coeffs only for selected observations
            sec_deps_subset = (
                set().union(
                    *(
                        sec_dep_coeffs_map.get(obs, set())
                        for obs in perm_obs_subset
                    )
                )
                if perm_obs_subset
                else set()
            )

            # call existing rule on the restricted instance
            res = __try_abstract_permute_rule(
                constraints,
                groebner,
                S,
                M_sub,
                perm_obs_subset,
                rands_allowed,
                sec_deps_subset,
                log,
            )
            # __try_abstract_permute_rule returns rewritten list if it changed, otherwise original perm_obs_subset
            if res is not None:
                # integrate rewritten rows back into full perm_obs_pruned
                new_perm_obs = list(perm_obs)
                for idx_pos, row_idx in enumerate(subset_rows):
                    new_perm_obs[row_idx] = res[idx_pos]
                if log:
                    print(
                        f"Abstract permute succeeded for subset {subset_rows}."
                    )
                return new_perm_obs + elim_obs

    if log:
        print("No sub-combination succeeded for abstract permute.")
    return None


def __rewrite_until_indep(
    constraints: Tuple[
        Sequence[MPolynomial], ...
    ],  # masking scheme specific constraints which are used in groebner basis checking
    constraints_hash: str,
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    R: CommutativeRing,
    R_gens_to_idx: dict,
    R_namespace,
    security_notion: SecurityNotion,
    obsgraph: ObservationGraph,
    observations_clean: list[
        Observation
    ],  # obstuple without term rewrites but destructs
    observations: list[Observation],  # working copy
    secret_vars: Sequence[Set[MPolynomial]],
    public_vars: Set[MPolynomial],
    random_vars: Set[MPolynomial],
    initial_tup_size: int,  # add initial tuple size for checks with FDedup
    skip_aperm: bool,  # if no parameter vars are present no abstract permute is necessary
    criterion: Callable[[Sequence[Observation]], bool],
    log: bool = False,
) -> bool:
    if log:
        print(
            f"__rewrite_until_permute processing {len(observations)} observations:"
        )
        for obs in observations:
            print(
                f"{obs.print(id=True, value=True, parents=True, applied_rules=True, loc=True, depset=True)}"
            )
        sys.stdout.flush()

    if criterion(observations):
        if log:
            print("Observation set satisfies notion without further rewriting.")
        return True

    # construct the matrix of coefficients for all randoms which have non-linear factors only
    M, r_vec, M_row_has_residue, M_row_has_rndprod, secret_dep_coeffs = (
        __rnd_matrix(
            R, R_gens_to_idx, observations, random_vars, secret_vars, log=False
        )
    )
    assert M.nrows() == len(observations)
    # enumerate rows that have all zero entries, i.e., that are independent of all random variables used for searching permutes
    rows_indep_of_perm_rands = [
        i
        for i in range(M.nrows())
        if all(M[i, j] == 0 for j in range(M.ncols()))
    ]

    # partition observations into independent and dependent ones and only perform permute across dependent observations
    perm_observations: list[
        Observation
    ] = []  # observations which are considered for searching permutes
    non_perm_observations: list[
        Observation
    ] = []  # observations not considered for searching permutes
    for row in range(M.nrows()):
        if row in rows_indep_of_perm_rands:
            non_perm_observations.append(observations[row])
        else:
            perm_observations.append(observations[row])
    # delete all non-candidate rows from M and residues
    M = M.delete_rows(rows_indep_of_perm_rands)
    M_row_has_residue = [
        v
        for i, v in enumerate(M_row_has_residue)
        if i not in rows_indep_of_perm_rands
    ]

    if log:
        print(
            f"Random variable matrix is\n{M}\nx {r_vec}\n with residues\n{M_row_has_residue}\nand non-permute-candidate observations\n{non_perm_observations}."
        )

    if len(r_vec) > 0:
        # Compute unreduced row echelon form (zeros below pivots but pivot values kept as in M)
        E, gaussian_pivots, map_E_row_to_M_row = (
            __unreduced_echelon_and_mapping(constraints_hash, groebner, S, M)
        )

        if log:
            print(f"Random variable matrix in row echelon is\n{E}\nx {r_vec}")

        n, m = E.nrows(), E.ncols()
        pivots = []
        cols = []
        rows = []
        for (r, c), piv in gaussian_pivots:
            pivots.append(piv)
            cols.append(c)
            rows.append(r)

        if log:
            print(f"rows = {rows}")
            print(f"cols = {cols}")
            print(f"pivots = {pivots}")
            sys.stdout.flush()

        assert len(set(cols)) == len(cols), (
            f"duplicate entries in pivot columns: {list(zip(rows, cols))}."
        )
        assert len(set(rows)) == len(rows), (
            f"duplicate entries in pivot rows: {list(zip(rows, cols))}."
        )

        # compute a closed subset of pairs of rows and random variables such that all observations dependening on one of the random variables are within the rows.
        p_pairs = dict(zip(cols, rows))
        p_rows = set(
            row
            for row in range(n)
            if any(M[map_E_row_to_M_row[row], rv] != 0 for rv in p_pairs.keys())
        )
        while not p_rows.issubset(set(p_pairs.values())):
            for rv in list(p_pairs.keys()):
                if log:
                    print(
                        f"processing {rv} with p_pairs={p_pairs}\nand p_rows={p_rows}."
                    )
                if any(
                    row not in p_pairs.values()
                    and M[map_E_row_to_M_row[row], rv] != 0
                    for row in range(n)
                ):
                    # rv occurs in a row not in p_row, remove this rv from p_cols and recompute p_rows
                    if log:
                        print(
                            f"random variable {r_vec[rv]} has dependencies to observations in rows {[row for row in range(n) if row not in p_pairs.values() and M[map_E_row_to_M_row[row], rv] != 0]} which are not permute eligible rows in p_rows."
                        )
                    row = p_pairs.pop(rv)
                    p_rows = set(
                        row
                        for row in range(n)
                        if any(
                            M[map_E_row_to_M_row[row], rv] != 0
                            for rv in p_pairs.keys()
                        )
                    )

        # check if there are observations in the subset of pairs that have residues or non-permute randoms that will be eliminated in case of rule application
        non_permute_rvs = set(range(m)) - set(p_pairs.keys())
        p_eliminates = any(
            M_row_has_residue[map_E_row_to_M_row[row]]
            or any(
                M[map_E_row_to_M_row[row], col] != 0 for col in non_permute_rvs
            )
            for row in p_rows
        )

        if log:
            print(f"p_rows = {p_rows}")
            print(f"p_pairs = {p_pairs}")
            print(f"p_eliminates = {p_eliminates}")

        if p_eliminates:
            if log:
                print(
                    "Checking determinant of permute-eligible terms is non-zero by examining individual pivots."
                )
            if all(
                has_no_roots_cached(
                    constraints_hash,
                    groebner,
                    S,
                    E[row, col].numerator(),
                    log=log,
                )
                for col, row in p_pairs.items()
            ):
                if log:
                    print(
                        f"Applying permute with random variables {[r_vec[col] for col in p_pairs.keys()]} since pivots are individually root-free."
                    )
                rvars: list[MPolynomial] = [
                    r_vec[col] for col in p_pairs.keys()
                ]
                for col, row in p_pairs.items():
                    if log:
                        print(
                            f"Replacing permute observation with index {map_E_row_to_M_row[row]} by {r_vec[col]}."
                        )
                    perm_observations[map_E_row_to_M_row[row]] = (
                        perm_observations[map_E_row_to_M_row[row]].rewrite(
                            r_vec[col],
                            rrule=Permute(
                                rvars,
                                this_rv=r_vec[col],
                                this_expr=perm_observations[
                                    map_E_row_to_M_row[row]
                                ].get_value(),
                            ),
                        )
                    )
                return __rewrite_until_indep(
                    constraints,
                    constraints_hash,
                    groebner,
                    S,
                    R,
                    R_gens_to_idx,
                    R_namespace,
                    security_notion,
                    obsgraph,
                    observations_clean,
                    perm_observations + non_perm_observations,
                    secret_vars,
                    public_vars,
                    random_vars,
                    initial_tup_size,
                    skip_aperm,
                    criterion,
                    log=log,
                )
            elif log:
                print(
                    f"Cannot apply permute since one pivot in {pivots} has roots and hence the random variable matrix is not invertible."
                )
        elif log and len(p_pairs) == 0:
            print(
                "Cannot apply permute as there is no closed subset of permute-eligible random variables for permute-eligible terms."
            )
        elif log:
            print("Not applying permute since no terms would be eliminated.")

        ## Try to apply abstract permute ##
        # prune observations with no residue, and only retain secret dependent coeffs that belong to those observations
        if not skip_aperm:
            # remove observations from consideration that have linearly dependent obs, also mark their randoms as bad so that they cant be used
            (
                M_pruned,
                perm_obs_pruned,
                elim_obs,
                r_vec_pruned,
                sec_dep_coeffs_pruned,
            ) = __elim_lin_dep_obs(
                S,
                M,
                E,
                map_E_row_to_M_row,
                perm_observations,
                r_vec,
                secret_dep_coeffs,
                log,
            )
            new_perm_obs = __try_abstract_permute_all_subsets(
                constraints,
                groebner,
                S,
                M_pruned,
                perm_obs_pruned,
                r_vec_pruned,
                sec_dep_coeffs_pruned,
                log,
            )
            if new_perm_obs is not None:
                return __rewrite_until_indep(
                    constraints,
                    constraints_hash,
                    groebner,
                    S,
                    R,
                    R_gens_to_idx,
                    R_namespace,
                    security_notion,
                    obsgraph,
                    observations_clean,
                    new_perm_obs + elim_obs + non_perm_observations,
                    secret_vars,
                    public_vars,
                    random_vars,
                    initial_tup_size,
                    skip_aperm,
                    criterion,
                    log=log,
                )

        # try to apply expanding OTP on observations which are linearly dependent on a common random variable
        for col in cols:
            # perform an expanding OTP by picking the residue e' belonging to the pivot and rewrite r -> (r - e')/pivot in all affected observations after checking pivot is root-free.
            rv = r_vec[col]
            E_rows_dep_on_rv = [
                i for i in range(n) if M[map_E_row_to_M_row[i], col] != 0
            ]
            if any(
                sum(M[map_E_row_to_M_row[r], j] != 0 for j in range(m)) == 1
                for r in E_rows_dep_on_rv
            ):
                if log:
                    print(
                        f"Not applying expanding OTP in random variable {rv} one term is already reduced to it."
                    )
                continue
            pivot = None
            row = None
            for r in sorted(
                E_rows_dep_on_rv,
                key=lambda r: sum(
                    M[map_E_row_to_M_row[r], j] != 0 for j in range(m)
                ),
                reverse=True,
            ):
                if has_no_roots_cached(
                    constraints_hash,
                    groebner,
                    S,
                    M[map_E_row_to_M_row[r], col],
                    log=log,
                ):
                    row = r
                    pivot = M[map_E_row_to_M_row[r], col]
                    break
            if pivot is not None and row is not None:
                expr = (
                    rv
                    - (
                        perm_observations[map_E_row_to_M_row[row]].get_value()
                        - rv * pivot
                    )
                ) / pivot
                if log:
                    print(f"applying expanding OTP[{rv} -> {expr}].")
                for row in E_rows_dep_on_rv:
                    obs_expr = perm_observations[
                        map_E_row_to_M_row[row]
                    ].get_value()
                    obs_expr_new = obs_expr.subs({rv: expr})
                    if log:
                        print(
                            f"replacing variable {rv} by {expr} in observation {obs_expr}\nyielding {obs_expr_new}."
                        )
                    perm_observations[map_E_row_to_M_row[row]] = (
                        perm_observations[map_E_row_to_M_row[row]].rewrite(
                            obs_expr_new, rrule=ExpOtp(rv, expr)
                        )
                    )
                return __rewrite_until_indep(
                    constraints,
                    constraints_hash,
                    groebner,
                    S,
                    R,
                    R_gens_to_idx,
                    R_namespace,
                    security_notion,
                    obsgraph,
                    observations_clean,
                    perm_observations + non_perm_observations,
                    secret_vars,
                    public_vars,
                    random_vars,
                    initial_tup_size,
                    skip_aperm,
                    criterion,
                    log=log,
                )

            elif log:
                print(
                    f"Not applying expanding OTP in random variable {rv} as none of the dependent observations without residue has root-free coefficients."
                )
        # try to apply destruct rule since none of above rules was triggered
        # search for an observation that still has non-linear randoms despite all the rules applied so far
        destr_obs_res = __apply_destruct_rule(
            M_row_has_rndprod,
            observations,
            observations_clean,
            obsgraph,
            security_notion,
            secret_vars,
            log,
        )
        # if destruct returned None it failed and verification cannot continue
        if destr_obs_res is None:
            return False
        # if it doesn't fail we feed its results into an attempt of safe destruct
        observations, observations_clean = destr_obs_res
        safe_destr_obs_res = __apply_safe_destruct_rule(
            observations,
            observations_clean,
            obsgraph,
            security_notion,
            initial_tup_size,
            log,
        )
        # if a safe destruct on initial_tup_size elements is possible we can mark this tuple as secure since it is handled elsewhere
        if safe_destr_obs_res is None:
            return True
        # otherwise we use its result and try to defactor its observations
        observations, observations_clean = safe_destr_obs_res
        defactored_obs = __apply_factor_deduplicate_rule(
            R, observations, initial_tup_size, log
        )
        # again, if a factor dedup on initial_tup_size elements is possible we can mark this tuple as secure since it is handled elsewhere
        if defactored_obs is None:
            return True
        # try verification again with resulting obs
        return __rewrite_until_indep(
            constraints,
            constraints_hash,
            groebner,
            S,
            R,
            R_gens_to_idx,
            R_namespace,
            security_notion,
            obsgraph,
            observations_clean,
            defactored_obs,
            secret_vars,
            public_vars,
            random_vars,
            initial_tup_size,
            skip_aperm,
            criterion,
            log=log,
        )

    else:
        # try to apply destruct rule since none of above rules was triggered
        # search for an observation that still has non-linear randoms despite all the rules applied so far
        destr_obs_res = __apply_destruct_rule(
            M_row_has_rndprod,
            observations,
            observations_clean,
            obsgraph,
            security_notion,
            secret_vars,
            log,
        )
        # if destruct returned None it failed and verification cannot continue
        if destr_obs_res is None:
            return False
        # if it doesnt fail we feed its results into an attempt of safe destruct
        observations, observations_clean = destr_obs_res
        safe_destr_obs_res = __apply_safe_destruct_rule(
            observations,
            observations_clean,
            obsgraph,
            security_notion,
            initial_tup_size,
            log,
        )
        # if a safe destruct on initial_tup_size elements is possible we can mark this tuple as secure since it is handled elsewhere
        if safe_destr_obs_res is None:
            return True
        # otherwise we use its result and try to defactor its observations
        observations, observations_clean = safe_destr_obs_res
        defactored_obs = __apply_factor_deduplicate_rule(
            R, observations, initial_tup_size, log
        )
        # again, if a factor dedup on initial_tup_size elements is possible we can mark this tuple as secure since it is handled elsewhere
        if defactored_obs is None:
            return True
        # try verification again with resulting obs
        return __rewrite_until_indep(
            constraints,
            constraints_hash,
            groebner,
            S,
            R,
            R_gens_to_idx,
            R_namespace,
            security_notion,
            obsgraph,
            observations_clean,
            defactored_obs,
            secret_vars,
            public_vars,
            random_vars,
            initial_tup_size,
            skip_aperm,
            criterion,
            log=log,
        )


def verify_observation_tuple(
    constraints: Tuple[
        Sequence[MPolynomial], ...
    ],  # masking scheme specific constraints which are used in groebner basis checking
    constraints_hash: str,
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    R: CommutativeRing,
    R_gens_to_idx: dict,
    R_namespace: dict,
    observationgraph: ObservationGraph,
    secret_vars: Sequence[Set[MPolynomial]],
    public_vars: Set[MPolynomial],
    random_vars: Set[MPolynomial],
    security_notion: SecurityNotion,
    criterion: Callable[[Sequence[Observation], int], bool],
    threshold: int,
    observations_idx: Sequence[int],
    skip_aperm: bool,
    log: bool = False,
) -> Tuple[bool, Any]:
    """
    Entrypoint for the verification procedure of one observation tuple, where the tuple
    consists of indices in the `observationgraph`.

    Returns the verification result and the checked tuple of indices.
    """
    try:
        if log:
            print(f"Verifying tuple {observations_idx} for t = {threshold}.")
            sys.stdout.flush()

        # Important: create independent copies to avoid mutating the shared observation in the Observationgraph
        observations = [
            observationgraph.get_observation(security_notion, idx)
            for idx in observations_idx
        ]
        observations_clean = [
            observationgraph.get_observation(security_notion, idx)
            for idx in observations_idx
        ]
        initial_tuple_size = len(observations)
        ok = __rewrite_until_indep(
            constraints,
            constraints_hash,
            groebner,
            S,
            R,
            R_gens_to_idx,
            R_namespace,
            security_notion,
            observationgraph,
            observations_clean,
            observations,
            secret_vars,
            public_vars,
            random_vars,
            initial_tuple_size,
            skip_aperm,
            criterion=lambda x: criterion(x, threshold),
            log=log,
        )

        if log:
            result = "✓ passed" if ok else "✗ FAILED"
            print(f"{result} tuple: {observations_idx}.")
        return ok, observations_idx
    except Exception:
        traceback.print_exc()
        return False, observations_idx


def _init_worker(
    constraints: Tuple[
        Sequence[MPolynomial], ...
    ],  # masking scheme specific constraints which are used in groebner basis checking
    constraints_hash: str,
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    R: CommutativeRing,
    R_gens_to_idx: dict,
    R_namespace: dict,
    secret_vars: Sequence[Set[MPolynomial]],
    public_vars: Set[MPolynomial],
    random_vars: Set[MPolynomial],
    security_notion: SecurityNotion,
    criterion: Callable[[Sequence[Observation], int], bool],
    obsgraph: ObservationGraph,
    threshold: int,
    skip_aperm: bool,
    log: bool,
):
    """
    Store the heavy objects in globals within each worker, so that each task only pickles and communicates small objects.
    """
    _worker_globals["constraints"] = constraints
    _worker_globals["constraints_hash"] = constraints_hash
    _worker_globals["groebner"] = groebner
    _worker_globals["S"] = S
    _worker_globals["R"] = R
    _worker_globals["R_gens_to_idx"] = R_gens_to_idx
    _worker_globals["R_namespace"] = R_namespace
    _worker_globals["obsgraph"] = obsgraph
    _worker_globals["secret_vars"] = secret_vars
    _worker_globals["public_vars"] = public_vars
    _worker_globals["random_vars"] = random_vars
    _worker_globals["security_notion"] = security_notion
    _worker_globals["criterion"] = criterion
    _worker_globals["threshold"] = threshold
    _worker_globals["skip_aperm"] = skip_aperm
    _worker_globals["log"] = log


def _process_task(obs_task: Tuple[int, ...]) -> tuple[bool, Tuple[int, ...]]:
    """
    Wrapper for multi-processing.

    Given a tuple of observation indices, unpack the globals, and call the actual verification routine.
    """
    # unpack based on task type and security notion
    if (
        isinstance(obs_task, tuple)
        and len(obs_task) == 2
        and _worker_globals["security_notion"] == SecurityNotion.SNI
    ):
        # SNI case: (obs_tuple, local_t)
        obs_idxtpl, local_t = obs_task
        threshold = local_t
    else:
        # PS,NI case: simple tuple of observation indices
        obs_idxtpl = obs_task
        threshold = _worker_globals["threshold"]
    return verify_observation_tuple(
        _worker_globals["constraints"],
        _worker_globals["constraints_hash"],
        _worker_globals["groebner"],
        _worker_globals["S"],
        _worker_globals["R"],
        _worker_globals["R_gens_to_idx"],
        _worker_globals["R_namespace"],
        _worker_globals["obsgraph"],
        _worker_globals["secret_vars"],
        _worker_globals["public_vars"],
        _worker_globals["random_vars"],
        _worker_globals["security_notion"],
        _worker_globals["criterion"],
        threshold,
        obs_idxtpl,
        _worker_globals["skip_aperm"],
        _worker_globals["log"],
    )


def verify_security(
    enc: Encoding,
    constraints: Tuple[
        Sequence[MPolynomial], ...
    ],  # masking scheme specific constraints which are used in groebner basis checking
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    security_notion: SecurityNotion,
    security_order: int,
    S: CommutativeRing,  # base ring over parameter vars
    R: CommutativeRing,  # polynomial ring over fraction field of S with variables in secrets, randoms, publics
    R_namespace: dict[
        str, MPolynomial
    ],  # mapping from variable names to symbols in R
    secret_vars: Sequence[Set[MPolynomial]],
    public_vars: Set[MPolynomial],
    random_vars: Set[MPolynomial],
    parameter_vars: Set[MPolynomial],
    obsgraph: ObservationGraph,
    output_observations: Set[int],
    continue_on_fail: bool = False,
    num_processes: Optional[int] = None,
    timeout_seconds: int = 3600,
    max_memory_mb: int = 1024,
    log: bool = False,
) -> bool:
    """
    Verifies a formal security notion `security_notion` by applying algebraic
    and probabilistic rewrites on tuples of observations in the ObservationGraph
    `obsgraph` to eliminate syntactic occurrences of `secret_vars`.

    `parameter_vars` are symbols, e.g., alpha_i for polynomial evaluation,
    corresponding to parameters that are not under adversarial control and
    hence not public variables but rather parameters subject to constraints.
    """
    start = time.perf_counter()
    # 0) lots of well-formedness checking
    all_secrets = set()
    for sv in secret_vars:
        ssv = set(sv)
        if len(ssv) != len(sv):
            raise ValueError(f"duplicate definition of secrets in {sv}.")
        elif not all_secrets.isdisjoint(ssv):
            raise ValueError(
                f"duplicate definition of secrets {all_secrets & ssv}, occurs multiple times in encoding: {secret_vars}."
            )
        else:
            all_secrets.update(ssv)
    assert isinstance(security_order, int) and security_order > 0, (
        f"t must be a positive integer, got {security_order}."
    )
    if any(not isinstance(s, MPolynomial) for s in all_secrets):
        raise ValueError(f"recieved non-symbol secret {all_secrets}.")
    if any(not isinstance(s, MPolynomial) for s in random_vars):
        raise ValueError(f"Random variables must be symbols: {random_vars}.")
    if not all_secrets.isdisjoint(public_vars):
        raise ValueError(
            f"Variables incorrectly labled as secret and public: {all_secrets & public_vars}"
        )
    if not all_secrets.isdisjoint(random_vars):
        raise ValueError(
            f"Variables incorrectly labled as secret and random: {all_secrets & random_vars}"
        )
    if not public_vars.isdisjoint(random_vars):
        raise ValueError(
            f"Variables incorrectly labled as public and random: {public_vars & random_vars}"
        )
    nonpublicsyms = all_secrets | random_vars
    parameter_vars_set = set(parameter_vars)
    if not parameter_vars_set.isdisjoint(nonpublicsyms | public_vars):
        raise ValueError(
            f"Parameter vars incorrectly labled as secret, public, or random: {parameter_vars_set & (nonpublicsyms | public_vars)}"
        )

    # TODO: sanity check output_observations
    assert set(R.variable_names()).isdisjoint(set(S.variable_names())), (
        f"Inconsistent definition of rings with common generators \n{set(R.variable_names()) & set(S.variable_names())}."
    )

    if log:
        print(
            f"checking {security_notion} on {len(obsgraph)} observations in\n{obsgraph}.\n"
        )

    global_security_order = security_order
    constraints_hash = _roots_cache_sanitize_constraints(constraints)
    # if no parameter vars are present no abstract permute is necessary. only affects additive masking at the moment
    skip_aperm = len(parameter_vars) == 0

    # 1) Filter out purely public observations (no secrets or randomness)
    tplMgr = ObservationTupleManager(
        obsgraph,
        security_notion,
        security_order,
        secret_vars,
        output_observations,
    )
    occured_variables = tplMgr.filter_public_observations(
        public_vars | parameter_vars_set, log=log
    )
    # 1b) Remove duplicate observations to reduce count of tuples
    tplMgr.filter_duplicate_observations(log=log)
    tplMgr.defactor_obsgraph(log)
    num_tuples_total = tplMgr.num_tups_pre_defactor
    print(f"{num_tuples_total} total tuples to verify.")

    # 2) Confirm all variables are labeled either public, secret, parameter or random.
    untyped_vars = (
        occured_variables
        - all_secrets
        - random_vars
        - public_vars
        - parameter_vars_set
    )
    if untyped_vars:
        raise ValueError(
            f"Missing security labels for variables: {untyped_vars}"
        )

    # 2b) Convert the Expression-Symbols to Polynomials-Symbols as produced by poly_equation.variables()
    sgens = [set(s for s in sv if s in occured_variables) for sv in secret_vars]
    pgens = set(p for p in public_vars if p in occured_variables)
    rgens = set(r for r in random_vars if r in occured_variables)
    R_gens_to_idx = {g: i for i, g in enumerate(R.gens())}

    prepare_cache(enc, constraints, S, list(parameter_vars))

    # Build tuples based on security notion
    num_reduced_tuples, obs_tuple_iter = tplMgr.obs_tuple_iter()  # log)
    elim_through_defac_dedup = num_tuples_total - num_reduced_tuples
    print(f"{num_reduced_tuples} observation tuples after defactor + Dedup.")
    print(
        f"{elim_through_defac_dedup} tuples eliminated through defactor + Dedup."
    )
    print()
    num_completed_tups = 0
    nprocs = min(1, cpu_count() - 1) if num_processes is None else num_processes
    num_failed = 0
    failed_tuples = []
    global _manager
    if nprocs > 1:
        chunksize = (
            1
            if security_order < 3
            else min(100, max(1, num_tuples_total // (nprocs * 1)))
        )

        try:
            # Disable logging of workers when multi-processing is on
            log_workers = False
            criterion = tplMgr.continuation_criterion()
            with Pool(
                processes=nprocs,
                initializer=_init_worker,
                initargs=(
                    constraints,
                    constraints_hash,
                    groebner,
                    S,
                    R,
                    R_gens_to_idx,
                    R_namespace,
                    sgens,
                    pgens,
                    rgens,
                    security_notion,
                    criterion,
                    obsgraph,
                    security_order,
                    skip_aperm,
                    log_workers,
                ),
            ) as pool:
                # Create progress bar with total count and task description
                progress_bar = tqdm.tqdm(
                    total=num_tuples_total,
                    desc=f"Verifying {security_order}-{security_notion} tuples",
                    unit="tuple",
                )
                update_every = max(1, num_tuples_total // 300)  #
                since_last = 0

                try:
                    setup_time = time.perf_counter() - start
                    with timeout(
                        seconds=timeout_seconds - setup_time,
                        exception=TimeoutError,
                    ):
                        for ok, obs_idxtpl in pool.imap_unordered(
                            _process_task, obs_tuple_iter, chunksize=chunksize
                        ):
                            # memory check (unchanged)
                            current_process = psutil.Process()
                            total_memory_mb = (
                                current_process.memory_info().rss / 1024 / 1024
                            )

                            # count progress locally
                            num_completed_tups += 1
                            since_last += 1

                            # only refresh tqdm every 1% (or at the very end)
                            if (
                                since_last >= update_every
                                or num_completed_tups == num_tuples_total
                            ):
                                progress_bar.set_description(
                                    f"Verifying {security_order}-{security_notion} tuples ({total_memory_mb:.1f}/{max_memory_mb} MB)"
                                )
                                progress_bar.update(since_last)
                                since_last = 0

                            if total_memory_mb > max_memory_mb:
                                print(
                                    f"Total memory limit exceeded: {total_memory_mb:.1f} MB > {max_memory_mb} MB"
                                )
                                pool.terminate()
                                raise MemoryError(
                                    f"Verification exceeded maximum memory limit with {total_memory_mb} MB out of {max_memory_mb} MB."
                                )

                            if not ok:
                                num_failed += 1
                                failed_tuples.append(obs_idxtpl)
                                if log:
                                    print(
                                        f"✗ FAILED (t={security_order}) with tuple {obs_idxtpl}."
                                    )
                                if not continue_on_fail:
                                    # Cancel remaining tasks gracefully # naaah, just kill it all!
                                    pool.terminate()  # Stop accepting new tasks
                                    break  # Exit the loop
                except TimeoutError:
                    pool.terminate()
                    elapsed = time.perf_counter() - start
                    raise TimeoutError(
                        f"Verification timeout after {elapsed:.1f}s with {num_completed_tups} out of {num_tuples_total} completed ({(num_completed_tups * 100) / num_tuples_total:.1f}%)."
                    )
                finally:
                    # Ensure the progress bar is closed properly
                    progress_bar.close()

        except Exception as e:
            print(f"Error during parallel verification: {e}")
            traceback.print_exc()
            raise
    else:
        progress_bar = tqdm.tqdm(
            total=num_tuples_total, desc="Verification progress", unit="tuple"
        )
        # single-threaded
        criterion = tplMgr.continuation_criterion()
        # debug a specific tuple, e.g., for failing cases
        # obs_tuple_iter = [((539, 551), 1)]  # SNI
        # obs_tuple_iter = [(121, 377)]  # NI
        for i, obs_idxtpl in enumerate(obs_tuple_iter):
            # Check timeout
            elapsed = time.perf_counter() - start
            pct = num_completed_tups / num_tuples_total * 100
            if elapsed > timeout_seconds:
                progress_bar.close()
                raise TimeoutError(
                    f"Verification timeout after {elapsed:.1f}s with {num_completed_tups} out of {num_tuples_total} completed ({pct:.1f}%)."
                )

            # when verifying SNI obs_tuple_iter returns a tuple of (obs_idxtpl, security_order) and needs to be disassembled prior to verification
            if (
                isinstance(obs_idxtpl, tuple)
                and security_notion == SecurityNotion.SNI
            ):
                obs_idxtpl, security_order = obs_idxtpl
                # criterion is set later in verify_observation_tuple

            progress_bar.update(1)
            if log:
                print(
                    f"({num_completed_tups}/{num_tuples_total}, {pct:.1f}% in {elapsed:.3f}) t_tuple {obs_idxtpl}."
                )
            ok, _ = verify_observation_tuple(
                constraints,
                constraints_hash,
                groebner,
                S,
                R,
                R_gens_to_idx,
                R_namespace,
                obsgraph,
                sgens,
                pgens,
                rgens,
                security_notion,
                criterion,
                security_order,
                obs_idxtpl,
                skip_aperm,
                log=log,
            )
            num_completed_tups += 1
            if not ok:
                num_failed += 1
                failed_tuples.append(obs_idxtpl)
                print(
                    f"\n✗ FAILED (t={security_order}) with {num_completed_tups - 1}-th tuple {obs_idxtpl}"
                )
                if not continue_on_fail:
                    break
    skipped_tuples = tplMgr.get_num_skipped_tuples(log)
    if log:
        print(f"Skipped {skipped_tuples} many obs tuples in preprocessing.")
        print(
            f"Verified {num_completed_tups} tuples for a total of {num_completed_tups + skipped_tuples}."
        )
    n = len(obsgraph)
    k = min(global_security_order, n)
    if num_failed == 0:
        elapsed = time.perf_counter() - start
        assert (
            elim_through_defac_dedup + num_completed_tups + skipped_tuples
            == num_tuples_total
        ), (
            f"mismatch: verified {elim_through_defac_dedup + num_completed_tups + skipped_tuples} of {num_tuples_total} tuples."
        )
        print(
            f"\n✔ All comb({n}, {k})={comb(n, k)} tuples verified for t={global_security_order} with security notion {security_notion} in {elapsed:.3f}s"
        )
        print_roots_cache_stats()
        print_full_rank_cache_stats()
        return True
    else:
        print(
            f"\n✗ Verification failed for {num_failed} tuples out of comb({n}, {k})={comb(n, k)} tuples for security notion {security_notion} with t={global_security_order}."
        )
        print("Failed tuples:")
        obss = set()
        for obs_idxtpl in sorted(failed_tuples):
            obss.update(id for id in obs_idxtpl)
            print(f"    {obs_idxtpl}")
        print(f"with {len(obss)} involved observations:")
        for obs_idx in sorted(obss):
            obss = obsgraph.get_observation(security_notion, obs_idx)
            print(f"{obss.print(applied_rules=False)}")
        print_roots_cache_stats()
        print_full_rank_cache_stats()
        sys.stdout.flush()
        return False
