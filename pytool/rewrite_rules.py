# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Sequence, Union, TYPE_CHECKING

if TYPE_CHECKING:
    from sage.rings.polynomial.multi_polynomial import MPolynomial


@dataclass(frozen=True)
class FwOtp:
    """
    Forward OTP:
      fwOTP[{expr} -> {rv}]
    """

    expr: MPolynomial
    rv: MPolynomial

    def __str__(self) -> str:
        return f"fwOTP[{self.expr} -> {self.rv}]"


@dataclass(frozen=True)
class ExpOtp:
    """
    Expanding OTP:
      expOTP[{rv} -> {expr}]
    """

    rv: MPolynomial
    expr: MPolynomial

    def __str__(self) -> str:
        return f"expOTP[{self.rv} -> {self.expr}]"


@dataclass(frozen=True)
class Permute:
    """
    Permutation with multiple random variables:
      permute[{rvs}, {this_rv}->{this_expr}]
    """

    rvs: Sequence[MPolynomial] = field(repr=False)
    this_rv: MPolynomial
    this_expr: MPolynomial

    def __str__(self) -> str:
        rvs = ", ".join(f"{rv}" for rv in self.rvs)
        return f"permute[{rvs}, {self.this_expr}->{self.this_rv}]"


@dataclass(frozen=True)
class Destruct:
    """
    Destruction (safe or unsafe):
      sdestruct[{cid}->{pid}]   if safe == True
      destruct[{cid}->{pid}]     otherwise
    """

    cid: int
    pid: int
    safe: bool = False

    def __str__(self) -> str:
        kind = "sdestruct" if self.safe else "destruct"
        return f"{kind}[{self.cid}->{self.pid}]"


@dataclass(frozen=True)
class FDedup:
    """
    Dedup:
      fdedup[{expr}->{factor}]
    """

    factor: MPolynomial
    expr: MPolynomial

    def __str__(self) -> str:
        return f"fdedup[{self.expr}->{self.factor}]"


RewriteRule = Union[ExpOtp, FwOtp, Permute, Destruct, FDedup]
