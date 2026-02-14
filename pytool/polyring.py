# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from functools import reduce
import diskcache
import os
import sys
import time
import hashlib
from multiprocessing import Value
from sage.all import PolynomialRing, sage_eval, Matrix
from sage.rings.ring import CommutativeRing
from sage.rings.polynomial.multi_polynomial import MPolynomial
from sage.symbolic.expression import Expression
from typing import Sequence, Set, Tuple
from sage.rings.polynomial.term_order import TermOrder

# base folder for all ring‐specific caches
_DB_BASE_DIR = os.path.join(os.getcwd(), ".ever_roots_cache")
os.makedirs(_DB_BASE_DIR, exist_ok=True)
_FULL_RANK_BASE_DIR = os.path.join(os.getcwd(), ".ever_full_rank_cache")
os.makedirs(_FULL_RANK_BASE_DIR, exist_ok=True)

# in‐memory map from ring‐ID → Cache object
_roots_cache_map: dict[str, diskcache.Cache] = {}
_full_rank_cache_map: dict[str, diskcache.Cache] = {}

# shared cache‐stats via atomic Values, visible to all workers
_ROOTS_CACHE_HITS = Value("l", 0)
_ROOTS_CACHE_MISSES = Value("l", 0)
_FULL_RANK_CACHE_HITS = Value("l", 0)
_FULL_RANK_CACHE_MISSES = Value("l", 0)


def clear_all_caches():
    global _DB_BASE_DIR, _FULL_RANK_BASE_DIR
    import shutil

    _roots_cache_map.clear()
    _full_rank_cache_map.clear()
    _ROOTS_CACHE_HITS.value = 0
    _ROOTS_CACHE_MISSES.value = 0
    _FULL_RANK_CACHE_HITS.value = 0
    _FULL_RANK_CACHE_MISSES.value = 0
    shutil.rmtree(_DB_BASE_DIR, ignore_errors=True)
    shutil.rmtree(_FULL_RANK_BASE_DIR, ignore_errors=True)
    _DB_BASE_DIR = os.path.join(os.getcwd(), ".ever_roots_cache")
    os.makedirs(_DB_BASE_DIR, exist_ok=True)
    _FULL_RANK_BASE_DIR = os.path.join(os.getcwd(), ".ever_full_rank_cache")
    os.makedirs(_FULL_RANK_BASE_DIR, exist_ok=True)
    assert _roots_cache_map.keys() == set(), (
        "roots cache map not cleared properly"
    )
    assert _full_rank_cache_map.keys() == set(), (
        "full rank cache map not cleared properly"
    )


def print_roots_cache_stats():
    print(
        f"[diskcache] root cache hits={_ROOTS_CACHE_HITS.value}, misses={_ROOTS_CACHE_MISSES.value}"
    )


def print_full_rank_cache_stats():
    print(
        f"[diskcache] full rank cache hits={_FULL_RANK_CACHE_HITS.value}, misses={_FULL_RANK_CACHE_MISSES.value}"
    )


def _roots_cache_sanitize_ring_id(S: CommutativeRing) -> str:
    # turn S’s repr into a filesystem‐safe directory name
    ring_id = (
        str(S).strip().replace(" ", "_").replace("/", "_").replace("\n", "_")
    )
    return hashlib.sha256(ring_id.encode()).hexdigest()[:16]


def _roots_cache_sanitize_constraints(
    constraints: Tuple[Sequence[MPolynomial], ...],
) -> str:
    eq, ineq = constraints
    # sorting very expensive here, use lists and generate constraints deterministically
    eq_str = "".join(sorted(str(c) for c in eq))
    ineq_str = "".join(sorted(str(c) for c in ineq))
    constraints_str = eq_str + ineq_str
    return hashlib.sha256(constraints_str.encode()).hexdigest()[:16]


def _format_matrix(M: Matrix) -> str:
    rows, cols = M.nrows(), M.ncols()
    entries = ";".join(str(M[i, j]) for i in range(rows) for j in range(cols))
    return f"{rows}x{cols}:{entries}"


def _format_sec_coeffs(sec_coeffs: Set[MPolynomial]) -> str:
    sec_coeffs_str = "".join(sorted(str(c) for c in sec_coeffs))
    return sec_coeffs_str


def _get_roots_cache(S: CommutativeRing) -> diskcache.Cache:
    rid = _roots_cache_sanitize_ring_id(S)
    if rid not in _roots_cache_map:
        path = os.path.join(_DB_BASE_DIR, rid)
        os.makedirs(path, exist_ok=True)
        _roots_cache_map[rid] = diskcache.Cache(path)
    return _roots_cache_map[rid]


def _get_full_rank_cache(
    constraints: Tuple[Sequence[MPolynomial], ...], S: CommutativeRing
) -> diskcache.Cache:
    rid = _roots_cache_sanitize_ring_id(S)
    conid = _roots_cache_sanitize_constraints(constraints)
    id = rid + conid
    if id not in _full_rank_cache_map:
        path = os.path.join(_FULL_RANK_BASE_DIR, id)
        os.makedirs(path, exist_ok=True)
        _full_rank_cache_map[id] = diskcache.Cache(path)
    return _full_rank_cache_map[id]


def gen_rings_for_gadgets(
    field: CommutativeRing,
    base_gens: Sequence[str],
    gens: Sequence[str],
    max_randoms: int = 0,
    termorder=None,
) -> tuple[CommutativeRing, CommutativeRing]:
    """
    Generate polynomial rings for gadgets, i.e. for the encoders and decoders.

    Parameters
    ----------
    field : Sage field
        The base field, e.g. GF(p**k).
    base_gens : list of str
        Names for generators of the fraction field acting as base for R.
    gens : list of str
        Names for generators of the polynomial ring R.
    max_randoms : int
        Maximum number of random variables to be generated.

    Returns
    -------
    S : PolynomialRing
        The base polynomial ring over the finite field.
    R : PolynomialRing
        The target polynomial ring over the fraction field K.
    """
    # Extract names
    randoms = [f"R_{i}" for i in range(max_randoms)]
    S_names = sorted(base_gens)
    # use a dummy variable to force into MPolynomialRing instead of UnivariatePolynomialRing
    if len(S_names) <= 1:
        S_names.append("dummy_var")
    R_names = sorted(list(gens) + randoms)

    # Build base polynomial ring and fraction field
    to = termorder if termorder is not None else "degrevlex"
    S = PolynomialRing(field, S_names, order=to)
    K = S.fraction_field()

    # Build target polynomial ring
    # Note, this ring is not type libsingular (C implementation), since libsingular does not support fraction fields.
    # this is suboptimal since the arithmetic over these expressions is in python and not in C.
    R = PolynomialRing(K, R_names, order="degrevlex")

    # Map names to generators for evaluation
    R_ns = {name: R.gen(i) for i, name in enumerate(R.variable_names())}
    R_ns.update(
        {
            name: K(S.gen(i))  # <-- wrap the S‐generator in K()
            for i, name in enumerate(S.variable_names())
        }
    )

    return (S, R)


def gen_rings_for_coerce_expr_to_poly(
    field: CommutativeRing,
    base_gens: Sequence[Expression],
    gens: Sequence[Expression],
):
    # Extract names
    S_names = sorted(map(str, base_gens))
    R_names = sorted(map(str, gens))

    # Build base polynomial ring and fraction field
    S = PolynomialRing(field, S_names, order="degrevlex")
    K = S.fraction_field()

    # Build target polynomial ring
    R = PolynomialRing(K, R_names, order="degrevlex")

    # Map names to generators for evaluation
    R_ns = {name: R.gen(i) for i, name in enumerate(R.variable_names())}
    R_ns.update(
        {
            name: K(S.gen(i))  # <-- wrap the S‐generator in K()
            for i, name in enumerate(S.variable_names())
        }
    )
    return (S, K, R, R_ns)


def coerce_expr_to_poly(
    tgt_ring: CommutativeRing, namespace, expr: Expression, log: bool = False
) -> MPolynomial:
    """
    Coerce a Sage symbolic expression into a polynomial in a multivariate polynomial ring with generators defined in `namespace`.
    """
    if log:
        print(f"coerce_expr_to_poly processing {expr}")

    poly_expr = sage_eval(str(expr), locals=namespace)
    assert poly_expr.parent() == tgt_ring, (
        f"coercion of expression {expr} to polynomial {poly_expr} in target ring\n{tgt_ring}\nfailed, coerced expression lies in\n{poly_expr.parent()}"
    )
    return poly_expr


def has_full_row_rank(
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    M: Matrix,
    sec_dep_coeffs: Set[MPolynomial],
) -> bool:
    """
    Check if a Matrix has full row rank under the given constraints, using a Groebner basis check.
    """
    if not sec_dep_coeffs:
        # no secret dependet coeffs should be impossible, if this is the case then the observations should have been deemed indep earlier.
        raise ValueError(
            "matrix being checked has no secret coefficients, something is wrong"
        )
    S_ext, basis = groebner
    orig = list(S_ext.gens())
    row_rank_vars_names = [f"M_{i}_row_rank_var" for i in range(M.nrows())]
    u_names = [f"u_{i}" for i in range(M.nrows())]
    lin_cert_names = [f"certificate_{i}" for i in range(len(sec_dep_coeffs))]
    aux = row_rank_vars_names + u_names + lin_cert_names

    to = TermOrder("degrevlex", len(orig)) + TermOrder("lex", len(aux))
    S_blk = PolynomialRing(
        S_ext.base_ring(), [str(v) for v in orig] + aux, order=to
    )

    phi = S_blk.hom([S_blk(x) for x in S_blk.variable_names()], S_blk)

    row_rank_vars = [S_blk(n) for n in row_rank_vars_names]
    u_vars = [S_blk(n) for n in u_names]
    lin_cert = [S_blk(n) for n in lin_cert_names]

    # we need to remove denominators to use groebner basis. To do so soundly we scale each column by the lowest common multiple
    col_denoms = []
    for j in range(M.ncols()):
        col_denoms.append([M[i, j].denominator() for i in range(M.nrows())])

    col_lcms = [reduce(lambda a, b: a.lcm(b), col) for col in col_denoms]
    M_scaled = M[:, :]
    for j in range(M.ncols()):
        for i in range(M.nrows()):
            M_scaled[i, j] = M[i, j] * col_lcms[j]

    constraint_polys = []
    # check for linear dependency by taking a row scalar variable and summing over the columns
    # if all sums are 0 it means we have linear dep between rows
    for j in range(M_scaled.ncols()):
        constraint_polys.append(
            sum(
                row_rank_vars[i] * phi(M_scaled[i, j])
                for i in range(M_scaled.nrows())
            )
        )
    # prevent trivial solution for linear dependency
    constraint_polys.append(
        sum(u_vars[i] * row_rank_vars[i] for i in range(len(row_rank_vars)))
        - S_blk(1)
    )
    # build constraint that at least one secret coeff cannot be zero. CAREFUL, only works over fields.
    # the idea here is that at least one element is non-zero, i.e. has a multiplicative inverse s.t. c*f = 1 with c=f⁻¹
    # more coeffs can be non-zero, then their coeffs be chosen as c_i = 0 to fulfill this equation.
    constraint_polys.append(
        sum(
            lin_cert[i] * phi(f.numerator())
            for i, f in enumerate(sec_dep_coeffs)
        )
        - S_blk(1)
    )

    I = S_blk.ideal([phi(g) for g in basis] + constraint_polys)
    G = I.groebner_basis(algorithm="libsingular:slimgb")
    return G == [S_blk(1)]


def has_full_row_rank_cached(
    constraints: Tuple[
        Sequence[MPolynomial], ...
    ],  # masking scheme specific constraints which are used in groebner basis checking
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    M: Matrix,
    sec_dep_coeffs: Set[MPolynomial],
    log: bool = False,
) -> bool:
    cache = _get_full_rank_cache(constraints, S)
    global _FULL_RANK_CACHE_HITS, _FULL_RANK_CACHE_MISSES
    M_formatted = _format_matrix(M)
    sec_dep_coeffs_formatted = _format_sec_coeffs(sec_dep_coeffs)

    key = hashlib.sha256(
        (M_formatted + sec_dep_coeffs_formatted).encode()
    ).hexdigest()[:16]
    if key in cache:
        with _FULL_RANK_CACHE_HITS.get_lock():
            _FULL_RANK_CACHE_HITS.value += 1
        res = cache[key]
        if log:
            print(f"Root cache hit for {M} resulting in {res}.")
        assert isinstance(res, bool)
        return res
    else:
        with _FULL_RANK_CACHE_MISSES.get_lock():
            _FULL_RANK_CACHE_MISSES.value += 1
        res = has_full_row_rank(groebner, M, sec_dep_coeffs)
        if log:
            print(f"Root cache set entry for {M} to {res}.")
        cache[key] = res
        return res


def has_no_roots(
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    element: MPolynomial,
    log: bool = False,
):
    """
    Check if `element` has no roots, i.e. is invertible in ring `S`.
    """
    assert element.parent() == S, (
        f"unexpected ring of element {element},\ngot      {element.parent()},\nexpected {S}."
    )

    S_ext, basis = groebner
    if element.parent() != S_ext:
        # Map element to extended ring if needed
        phi = element.parent().hom(
            [S_ext(x) for x in element.parent().variable_names()], S_ext
        )
        element = phi(element)

    start = time.perf_counter()
    # Check if element can be zero under constraints by adding it to basis
    I = S_ext.ideal(basis + [element])
    G = I.groebner_basis(algorithm="libsingular:slimgb")
    b = G == [S_ext(1)]
    if log:
        elapsed = time.perf_counter() - start
        print(
            f"Computed Gröbner basis in {elapsed:.3f}s for element {element}."
        )
    if not b and log:
        print(
            f"Element {element} has roots as it may vanish with solutions: {G}."
        )
    return b


def __has_no_roots_cached_inner(
    constraints_hash: str,
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S,
    cache,
    element,
    log: bool = False,
) -> bool:
    global _ROOTS_CACHE_HITS, _ROOTS_CACHE_MISSES
    key = f"{constraints_hash}::{str(element)}"
    if key in cache:
        with _ROOTS_CACHE_HITS.get_lock():
            _ROOTS_CACHE_HITS.value += 1
        res = cache[key]
        if log:
            print(f"Root cache hit for {element} resulting in {res}.")
        assert isinstance(res, bool)
        return res
    else:
        with _ROOTS_CACHE_MISSES.get_lock():
            _ROOTS_CACHE_MISSES.value += 1
        res = has_no_roots(groebner, S, element, log=log)
        if log:
            print(f"Root cache set entry for {element} to {res}.")
        cache[key] = res
        return res


def has_no_roots_cached(
    constraints_hash: str,
    groebner: Tuple[
        CommutativeRing, list
    ],  # Tuple of an extended ring S_ext and a precomputed ideal with a computed Groebner basis
    S: CommutativeRing,
    element: MPolynomial,
    log: bool = False,
) -> bool:
    """
    Check if `element` has no roots, i.e. is invertible in ring `S`.
    Leverages a diskcache.
    """
    global _ROOTS_CACHE_HITS, _ROOTS_CACHE_MISSES
    cache = _get_roots_cache(S)

    # first test if element is in the cache
    key = f"{constraints_hash}::{str(element)}"
    if key in cache:
        return __has_no_roots_cached_inner(
            constraints_hash, groebner, S, cache, element, log=log
        )
    else:
        # otherwise, try to factorize and check all factors
        sys.stdout.flush()
        factors = element.factor()
        if log:
            print(f"Factorized element {element} into {factors}.")
        res = True
        for factor, _ in factors:
            if log:
                print(f"Processing factor {factor} of element {element}.")
            if not __has_no_roots_cached_inner(
                constraints_hash, groebner, S, cache, factor, log=log
            ):
                if log:
                    print(
                        f"Element {element} has factor with roots {factor} and is hence not root free."
                    )
                sys.stdout.flush()
                res = False
                break
        if log and res:
            print(
                f"Element {element} has root free factors and is hence root free."
            )
        with _ROOTS_CACHE_MISSES.get_lock():
            _ROOTS_CACHE_MISSES.value += 1
        if log:
            print(f"Root cache set entry for {element} to {res}.")
        cache[key] = res
        sys.stdout.flush()
        return res


def __unsafe_cache_insert(
    constraints: Tuple[Sequence[MPolynomial], ...],
    S: CommutativeRing,
    p: MPolynomial,
    val: bool,
    overwrite: bool = False,
    log: bool = False,
):
    cache = _get_roots_cache(S)

    constraints_hash = _roots_cache_sanitize_constraints(constraints)
    key = f"{constraints_hash}::{str(p)}"
    if key in cache:
        current_val = cache[key]
        if val != current_val and overwrite:
            print(
                f"Warning: root cache entry for {p} is currently {current_val} but to be updated to {val}."
            )
            cache[key] = val
    else:
        if log:
            print(f"Root cache set entry for {p} to {val}.")
        cache[key] = val


def add_vandermonde_shamir_props_to_cache(
    constraints: Tuple[Sequence[MPolynomial], ...],
    S: CommutativeRing,
    alphas: Sequence[MPolynomial],
):
    """
    Derive ground truths regarding the support points and Vandermonde matrices used in shamir secret sharing based poly masking.
    """
    # Construct Vandermonde matrix
    n = len(alphas)
    V = Matrix(S, n, n, lambda i, j: alphas[i] ** j)
    V_inv = V.inverse()

    # Collect denominators from entries in Vandermonde and its inverse
    # these must be well defined if alpha_i are distinct, hence their denominators are necessarily root-free.
    root_free_polys = set()

    def add_denom(v):
        denom = v.denominator()
        assert not denom.is_zero()
        root_free_polys.add(denom)

    for i in range(n):
        for j in range(n):
            add_denom(V[i, j])
            add_denom(V_inv[i, j])

    # also, the inverse vandermonde is invertible and hence has determinant without roots
    # TODO: this takes very long for unknown reasons
    # det = V_inv.det()
    # root_free_polys.add(det.numerator())
    # root_free_polys.add(det.denominator())

    # pre-fill the cache with these facts
    for p in root_free_polys:
        if not (p == 1):
            # add the fact that p != 0
            __unsafe_cache_insert(constraints, S, p, True)


def add_IP_weight_props_to_cache(
    constraints: Tuple[Sequence[MPolynomial], ...],
    S: CommutativeRing,
    parameter_vars: Sequence[MPolynomial],
):
    """
    Establish the ground truth that the weights in IP masking are all non-zero.
    """

    for w in parameter_vars:
        __unsafe_cache_insert(constraints, S, w, True)


def prepare_cache(
    enc,
    constraints: Tuple[Sequence[MPolynomial], ...],
    S: CommutativeRing,
    parameter_vars: Sequence[MPolynomial],
):
    """
    Derive some ground-truth about root-free polynomials and add them to the cache to avoid costly gröbner calls.
    """
    # import at runtime to avoid circular imports... love python
    from encoding import IPEnc, PolyEnc

    if isinstance(enc, PolyEnc):
        if enc.k == 1:
            add_vandermonde_shamir_props_to_cache(
                constraints, S, parameter_vars
            )

    elif isinstance(enc, IPEnc):
        add_IP_weight_props_to_cache(constraints, S, parameter_vars)

    else:
        return
