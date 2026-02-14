# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from itertools import combinations
from math import comb
from sage.all import Matrix, matrix, block_matrix, SR
from sage.rings.polynomial.multi_polynomial import MPolynomial
from typing import Tuple


# Return the Vandermonde matrix for `supports` restricted to `n` rows and `m` columns.
def generate_vandermonde(polyring, supports, n: int, m: int) -> Matrix:
    if not (all(isinstance(e, MPolynomial) for e in supports)):
        for e in supports:
            print(f"Element type: {type(e)}")
        raise ValueError(
            f"Supports must be Polynomials, but got {type(supports[0])}: {supports}"
        )

    v_square = matrix.vandermonde(
        supports[:n] + [0 for _ in range(max(n, m) - 1)], polyring
    )
    v_n_x_m = v_square.submatrix(0, 0, n, m)

    return v_n_x_m


def generate_inverse_vandermonde(
    polyring, supports, n: int, shape: Tuple[int, int]
) -> Matrix:
    assert shape[0] >= 0 and shape[1] >= 0, (
        f"Shape must be non-negative, but got {shape}"
    )
    assert shape[0] <= n and shape[1] <= n, (
        f"Shape must be less than or equal to {n}x{n}, but got {shape[0]}x{shape[1]}"
    )

    v = generate_vandermonde(polyring, supports, n, n)
    v_inv = v.inverse()
    v_inv_n_x_m = v_inv.submatrix(
        0, 0, shape[0], shape[1]
    )  # restrict to n rows and m columns as defined in Appendix E.1

    return v_inv_n_x_m


def generate_lambda_hat_non_packed(
    polyring, supports: list[MPolynomial], degree
) -> Matrix:
    if not (all(isinstance(e, MPolynomial) for e in supports)):
        raise ValueError(
            f"Supports must be Polynomials, but got {type(supports)}: {supports}"
        )

    fracfield = polyring.fraction_field()
    n = len(supports)
    v_inv = generate_inverse_vandermonde(fracfield, supports, n, (n, n))
    lambda_hat = matrix(fracfield, n, n, 0)
    for i in range(n):
        for j in range(n):
            sum = v_inv[0, j]
            for k in range(degree + 1, n):
                sum += v_inv[k, j] * supports[i] ** k
            lambda_hat[i, j] = sum
    return lambda_hat


def generate_A_tilde(
    polyring, M_enc: list[Matrix], num_secrets: int, degree: int
) -> list[Matrix]:
    A_tilde = []
    for d in range(1, degree + 1):
        if d >= num_secrets:
            A_tilde_d = generate_A_tilde_for_degree_d(
                polyring, M_enc[d - 1], num_secrets, d
            )
        else:
            A_tilde_d = []
        A_tilde.append(A_tilde_d)
    return A_tilde


def generate_A_tilde_for_degree_d(
    polyring, M_enc: Matrix, num_secrets: int, degree: int
) -> Matrix:
    # truncate the first k=num_secret columns
    mat_d = M_enc.submatrix(0, num_secrets)

    mat_u = matrix(
        polyring, degree + 1 - num_secrets, degree + 1 - num_secrets, 1
    )
    A_tilde = block_matrix([[mat_u], [mat_d]], subdivide=False)

    return A_tilde


def gen_A_tilde_3D(
    polyring,
    n: int,
    d: int,
    k: int,
    secrets: list[MPolynomial],
    shares: list[MPolynomial],
) -> list[list[list[MPolynomial]]]:
    """
    Generate the symbolic variables for the A_tilde matrix used for optimized zero-encodings.
    The `A_tilde` matrix is a 3D list of size d x n x (d-k+1).
    Here, the first dimension is neccesary since A_tilde is degree specific and all variants between 1 and d might be used.
    """
    # secrets_supports: list[Expression]: secrets at point zero -> 'f', 'g', ...
    # shares_supports: list[Expression]: actual shares -> 'alpha_0', 'alpha_1', ...
    # num_shares: int: number of shares: len(shares_supports)
    # num_secrets: int: number of secrets: len(secrets_supports)
    # degree: int: maximal degree, get it from enc
    # -> list[Matrix]:

    M_enc = generate_M_enc(polyring, list(secrets), list(shares), n, k, d)
    A_tilde = generate_A_tilde(polyring, M_enc, k, d)

    return A_tilde


def generate_H_GCM(
    polyring, H_vars: list[MPolynomial], n: int, k: int, d: int
) -> Matrix:
    """
    Generate matrix H as described in Section 3.1 of https://tches.iacr.org/index.php/TCHES/article/view/9699/9230.
    Note that `m` corresponds to `d` here.
    """
    R = matrix(polyring, d, n - d, H_vars)
    I_d = matrix.identity(polyring, d)
    H = matrix.block([[R, I_d]], subdivide=False)

    return H


def generate_A_GCM(polyring, H: Matrix, n: int, k: int, d: int) -> Matrix:
    """
    Generate practical encoder matrix A as described in Section 3.1 of https://tches.iacr.org/index.php/TCHES/article/view/9699/9230.
    Note that `m` corresponds to `d` here.
    """
    # Upper part G: identity matrix concatenated with zeros
    I_k = matrix.identity(polyring, k)
    O = matrix(polyring, k, n - k, 0)
    G = matrix.block([[I_k, O]], subdivide=False)

    # Concatenate G and H row wise
    A = matrix.block([[G], [H]], subdivide=False)

    return A


def generate_A_hat_GCM(polyring, H: Matrix, n: int, k: int, d: int) -> Matrix:
    """
    Generate practical encoder matrix A as described in Section 3.1 of https://tches.iacr.org/index.php/TCHES/article/view/9699/9230.
    Note that `m` corresponds to `d` here.
    """
    A = generate_A_GCM(polyring, H, n, k, d)
    A_inv = A.inverse()
    O = matrix(polyring, n, d, 0)
    A_hat = matrix.block([[A_inv[:, :k], O]], subdivide=False)
    return A_hat


def generate_H_GCM_WMCS20(
    polyring, H_vars: list[MPolynomial], n: int, d: int
) -> Matrix:
    """
    Generate matrix H as described in Section 3 of https://tches.iacr.org/index.php/TCHES/article/view/8547/8112.
    Note that `m` corresponds to `d` here.
    """
    H = matrix(polyring, d, n, H_vars)

    return H


def generate_G_GCM_WMCS20(
    polyring, H_vars: list[MPolynomial], n: int, k: int
) -> Matrix:
    """
    Generate matrix H as described in Section 3 of https://tches.iacr.org/index.php/TCHES/article/view/8547/8112.
    Note that `m` corresponds to `d` here.
    """
    H = matrix(polyring, k, n, H_vars)

    return H


def generate_A_GCM_WMCS20(polyring, G: Matrix, H: Matrix) -> Matrix:
    """
    Generate encoder matrix A as described in Section 3 of https://tches.iacr.org/index.php/TCHES/article/view/9699/9230.
    Note that `m` corresponds to `d` here.
    """
    # Concatenate G and H row wise
    A = matrix.block([[G], [H]], subdivide=False)

    return A


def generate_A_hat_GCM_WMCS20(
    polyring, G: Matrix, H: Matrix, n: int, k: int, d: int
) -> Matrix:
    """
    Generate practical encoder matrix A as described in Section 3.1 of https://tches.iacr.org/index.php/TCHES/article/view/9699/9230.
    Note that `m` corresponds to `d` here.
    """
    A = generate_A_GCM_WMCS20(polyring, G, H)
    A_inv = A.inverse()
    O = matrix(polyring, n, d, 0)
    A_hat = matrix.block([[A_inv[:, :k], O]], subdivide=False)
    return A_hat


def generate_M_enc(
    polyring,
    secrets_supports: list[MPolynomial],
    shares_supports: list[MPolynomial],
    num_shares: int,
    num_secrets: int,
    degree: int,
) -> list[Matrix]:
    M_enc = []
    for d in range(1, degree + 1):
        M_enc_d = generate_M_enc_for_degree_d(
            polyring,
            secrets_supports,
            shares_supports,
            num_shares,
            num_secrets,
            d,
        )
        M_enc.append(M_enc_d)
    return M_enc


def generate_M_enc_for_degree_d(
    polyring,
    secrets_supports: list[MPolynomial],
    shares_supports: list[MPolynomial],
    num_shares: int,
    num_secrets: int,
    degree: int,
) -> Matrix:
    U = generate_vandermonde(
        polyring,
        secrets_supports[:num_secrets]
        + shares_supports[: degree + 1 - num_secrets],
        degree + 1,
        degree + 1,
    )
    U_inv = U.inverse()

    V = generate_vandermonde(
        polyring,
        shares_supports[degree + 1 - num_secrets :],
        num_shares - (degree + 1 - num_secrets),
        degree + 1,
    )
    M_enc = V * U_inv

    return M_enc


def generate_M_enc_for_degree_d_FOWZ25(
    polyring,
    secrets_supports: list[MPolynomial],
    shares_supports: list[MPolynomial],
    num_shares: int,
    num_secrets: int,
    degree: int,
) -> Matrix:
    U = generate_vandermonde(
        polyring,
        secrets_supports[:num_secrets]
        + shares_supports[: degree + 1 - num_secrets],
        degree + 1,
        degree + 1,
    )
    U_inv = U.inverse()

    V = generate_vandermonde(polyring, shares_supports, num_shares, degree + 1)
    M_enc = V * U_inv

    return M_enc


def generate_lambda_hat_degred(
    polyring,
    n: int,
    d: int,
    supports_x: list[MPolynomial],
    supports_u: list[MPolynomial],
) -> Matrix:
    if not (all(isinstance(e, MPolynomial) for e in supports_u)):
        raise ValueError(
            f"Supports (u) must be expressions, but got {type(supports_u)}: {supports_u}"
        )

    if not (all(isinstance(e, MPolynomial) for e in supports_x)):
        raise ValueError(
            f"Supports (x) must be expressions, but got {type(supports_x)}: {supports_x}"
        )

    assert len(supports_u) == 2 * d + 1, (
        f"supports_u must be of length {2 * d + 1}, but got {len(supports_u)}"
    )
    assert len(supports_x) == n, (
        f"supports_x must be of length {n}, but got {len(supports_x)}"
    )

    # Step 1: generate the unmask matrix which is defined to be the Vandermonde matrix of supports_u (2d+1 x 2d+1) times the upper left (n x 2d+1) submatrix of the inverse Vandermonde matrix of supports_x (n x n)
    mat_1 = generate_vandermonde(polyring, supports_u, 2 * d + 1, 2 * d + 1)
    mat_2 = generate_inverse_vandermonde(
        polyring, supports_x, n, (2 * d + 1, n)
    )
    unmask = mat_1 * mat_2

    # Step 2: generate the mask matrix which is defined to be the Vandermonde matrix of supports_x (n x n) times the upper left (n x 2d+1) submatrix of the inverse Vandermonde matrix of supports_u (2d+1 x 2d+1)
    mat_3 = generate_vandermonde(polyring, supports_x, n, d + 1)
    mat_4 = generate_inverse_vandermonde(
        polyring, supports_u, d + 1, (d + 1, d + 1)
    )
    mask = mat_3 * mat_4

    # Step 3: combine unmask and mask into a single matrix
    lambda_hat_degred = unmask * mask

    # Step 4: pad with zeros to obtain n x n matrix
    zero_padding = matrix(
        SR, n - lambda_hat_degred.nrows(), d + 1, 0
    )  # create padding such that the resulting matrix is n x (d+1)
    lambda_hat_degred = block_matrix(
        [[lambda_hat_degred], [zero_padding]], subdivide=False
    )

    return lambda_hat_degred


def generate_M_dec_for_degree_d(
    polyring,
    secrets_supports: list[MPolynomial],
    shares_supports: list[MPolynomial],
    num_shares: int,
    num_secrets: int,
    degree: int,
) -> Matrix:
    U = generate_vandermonde(
        polyring, secrets_supports[: degree + 2], num_secrets, num_shares
    )
    V = generate_vandermonde(polyring, shares_supports, num_shares, num_shares)
    V_inv = V.inverse()
    M_dec = U * V_inv

    return M_dec


def generate_M_lambda(
    polyring,
    secret_supports: list[MPolynomial],
    share_supports: list[MPolynomial],
    indegree: int,
    outdegree: int,
) -> Matrix:
    n = len(share_supports)
    # Generate the inverse of the Vandermonde matrix of the shares_supports
    # This is V_inverse (cf. Section 2.2)
    # mat_V_inv * n shares = polynomial coefficients, with zero coefficients, 0, ..., 0
    mat_V_inv = generate_vandermonde(polyring, share_supports, n, n).inverse()

    # Generate matrix mat_M1 using a submatrix of mat_V_inv
    # mat_M1 reconstructs "outdegree+1" coefficients from n shares
    # mat_M1 * n shares = coefficients of polynomial with degree "outdegree", without zero coefficient, 0, ..., 0
    mat_M1 = mat_V_inv.submatrix(0, 0, indegree + 1, -1)

    # Generate (inverse) Vandermonde matrix using secret support points
    mat_U_indegree_x_indegree = generate_vandermonde(
        polyring, secret_supports, indegree + 1, indegree + 1
    )
    mat_U_outdegree_x_outdegree = generate_vandermonde(
        polyring, secret_supports, outdegree + 1, outdegree + 1
    )
    mat_U_outdegree_x_outdegree_inv = mat_U_outdegree_x_outdegree.inverse()

    # Generate mat_M2 by padding mat_U_outdegree_x_outdegree_inv with zeros
    zero_pad_right = matrix(polyring, outdegree + 1, indegree - outdegree, 0)
    zero_pad_bottom = matrix(polyring, indegree - outdegree, indegree + 1, 0)
    mat_M2 = block_matrix(
        [[mat_U_outdegree_x_outdegree_inv, zero_pad_right], [zero_pad_bottom]],
        subdivide=False,
    )

    # Generate mat_M3
    mat_M3 = mat_M2 * (mat_U_indegree_x_indegree * mat_M1)

    mat_M_lambda = mat_M3.submatrix(0, 0, outdegree + 1, -1)
    return mat_M_lambda


def generate_error_propagation_matrix(
    indegree: int, V: Matrix, V_inv: Matrix
) -> Matrix:
    V_submatrix = V.submatrix(0, indegree + 1, -1, -1)
    V_inv_submatrix = V_inv.submatrix(indegree + 1, 0, -1, -1)
    mat_E = V_submatrix * V_inv_submatrix

    return mat_E


def generate_lambda_hat_packed(
    polyring,
    secret_supports: list[MPolynomial],
    shares_supports: list[MPolynomial],
    indegree: int,
    outdegree: int,
) -> Matrix:
    n = len(shares_supports)
    V = generate_vandermonde(polyring, shares_supports, n, n)
    V_inv = V.inverse()
    M_lambda = generate_M_lambda(
        polyring, secret_supports, shares_supports, indegree, outdegree
    )
    error_propagation_matrix = generate_error_propagation_matrix(
        indegree, V, V_inv
    )

    V_submatrix = V.submatrix(0, 0, -1, outdegree + 1)
    M_F_to_F_tilde_mat = V_submatrix * M_lambda

    lambda_hat_matrix = M_F_to_F_tilde_mat + error_propagation_matrix
    return lambda_hat_matrix


def _diag_selector(polyring, n: int, S: tuple[int, ...]):
    one, zero = polyring(1), polyring(0)
    return matrix(
        polyring, n, n, lambda i, j: one if (i == j and i in S) else zero
    )


def generate_d_private_encoder_constraints(
    polyring,
    T: list[Matrix],
    G: Matrix,
    H: Matrix,
    d: int,
) -> list[MPolynomial]:
    """
    Translate the notion of d-privacy from https://tches.iacr.org/index.php/TCHES/article/view/8547/8112 into constraints compatible with a Groebner basis.
    d-privacy means that for all vectors w with HW(w) <= d: Hw^T = 0 => Gw^T = 0.
    We use the following properties for transformation:
        1. Hw^T = 0 => Gw^T = 0 is equivalent to the stating that Nullspace(H) ⊆ Nullspace(G)
        2. Nullspace(H) ⊆ Nullspace(G) <==> Rowspace(G) ⊆ Rowspace(H) since it is the orthogonal complement of the Nullspace https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
        3. This can be encoded as ∃T s.t. G' = TH', where G',H' have up to d non-zero columns.
        4. Since the previous constraint would need to be encoded for all d' <= d, we make use of the fact that if the statement G' = TH' holds for a all selections of d columns, it also hold for all d'.
        5. To encode the selection we choose H' = H x W, where W is a diagonal matrix of shape n x n with bits b_i i in [n] on its diagonal, with the constraint that b_i² - b_i = 0, i.e. it is zero or one, and   sum b_i - d = 0, i.e. d rows are selected at once.
    """

    k = G.nrows()
    n = G.ncols()
    m = H.nrows()
    assert len(T) == comb(n, d), f"T must contain {comb(n, d)} matrices"
    assert G.ncols() == H.ncols(), (
        "mismatch between dimensions of columns of G and H"
    )
    assert all(t.nrows() == k and t.ncols() == m for t in T), (
        f"dimensions of Ts were expected as {k} x {m}, some diverge"
    )

    constraints = []
    for W_i, T_i in zip(combinations(range(n), d), T):
        W_diag = _diag_selector(polyring, n, W_i)

        G_prime = G * W_diag
        H_prime = H * W_diag
        transformed_H = T_i * H_prime
        for i in range(k):
            for j in range(n):
                constraint = transformed_H[i, j] - G_prime[i, j]
                if constraint != polyring(0):
                    constraints.append(constraint)

    return constraints


def generate_full_row_rank_constraints(
    polyring, A: Matrix, A_vars: list[MPolynomial]
) -> list[MPolynomial]:
    """
    Encode the condition of a matrix having full row rank as it having a right inverse, i.e. A * A_inv = I https://en.wikipedia.org/wiki/Invertible_matrix.
    A has dim m x n, A_inv has dim n x m and I has dim m x m.
    Result is a list equalities that represent this constraint.
    """
    m, n = A.nrows(), A.ncols()

    assert len(A_vars) == m * n, (
        f"expected {m * n} vars to construct a symbolic inverse matrix, got {len(A_vars)} insteda"
    )
    A_inv = matrix(polyring, n, m, A_vars)

    constraints = []
    one, zero = polyring(1), polyring(0)

    for i in range(m):
        for b in range(m):
            # result needs to be one on the diagonal, else zero
            target = one if i == b else zero
            # row x column to calculate resulting element Res[i,b]. If we are on diagonal we subtract 1 to encode Res[i,b] = 1 <==> Res[i,b] - 1 = 0
            expr = sum(A[i, j] * A_inv[j, b] for j in range(n)) - target
            constraints.append(expr)
    return constraints
