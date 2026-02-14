# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from typing import Optional, Set, Callable
from sage.rings.polynomial.multi_polynomial import MPolynomial
from observations import Location, ObservableValue, mk_obsval
from encoding import Encoding
from itertools import count

ObsMat = list[list[ObservableValue]]
ObsList = list[ObservableValue]


def transpose(M: ObsMat) -> ObsMat:
    return [list(col) for col in zip(*M)] if M else []


def zeros(rows: int, cols: int, zero: ObservableValue) -> ObsMat:
    return [[zero for _ in range(cols)] for _ in range(rows)]


def to_obsval_factory(x: Encoding) -> Callable[[MPolynomial], ObservableValue]:
    def to_obsval(var: MPolynomial) -> ObservableValue:
        return mk_obsval(x.obsgraph, var, var)

    return to_obsval


def new_random_var(
    x: Encoding, rc: count, acc: Set[MPolynomial]
) -> MPolynomial:
    name = f"R_{next(rc)}"
    r = x.variable_ring(name)
    acc.add(r)
    return r


def matmul_obs(
    A: ObsMat, B: ObsMat, zero: ObservableValue, loc: Location
) -> ObsMat:
    assert A and B and len(A[0]) == len(B), "Shape mismatch for matmul_obs"
    a_rows, a_cols, b_cols = len(A), len(A[0]), len(B[0])
    out = zeros(a_rows, b_cols, zero)
    for i in range(a_rows):
        for j in range(b_cols):
            total = zero
            for k in range(a_cols):
                desc = "" if loc.description is None else loc.description
                tmp_loc = Location(
                    loc.filename,
                    loc.lineno,
                    desc + f"      OP: Mat1[{i}][{k}] * Mat2[{k}][{j}]",
                )
                prod = A[i][k].__mul__(B[k][j], loc=tmp_loc)
                tmp_loc = Location(
                    loc.filename,
                    loc.lineno,
                    desc + f"      OP: Res[{i}][{j}] += Mat1[{i}][{k}] * Mat2[{k}][{j}]",
                )
                total = total.__add__(prod, loc=loc)
            out[i][j] = total
    return out


def colscale_obs(
    A: ObsMat,
    a_row: list[ObservableValue],
    zero: ObservableValue,
    loc: Location,
) -> ObsMat:
    n, m = len(A), len(A[0])
    out = zeros(n, m, zero)
    for j in range(m):
        s = a_row[j]
        for i in range(n):
            out[i][j] = A[i][j].__mul__(s, loc=loc)
    return out


def to_obsmat(
    A, var_ring, to_obsval: Callable[[MPolynomial], ObservableValue]
) -> ObsMat:
    return [
        [to_obsval(var_ring((A[i, j]))) for j in range(A.ncols())]
        for i in range(A.nrows())
    ]


def mk_loc_factory(name: str, parent: Optional[Location]):
    def mk(line: int, description: str) -> Location:
        return Location(name, line, description, parent)

    return mk
