# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from itertools import count
from typing import Optional, Self, Set, Type
from sage.all import GF
from observations import Location, mk_obsval
from gadget import Gadget
from encoding import AddEnc, AddEnc_setup


class ISWMult(Gadget[AddEnc]):
    def __init__(
        self,
        x: AddEnc,
        y: AddEnc,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(x, AddEnc) or not isinstance(y, AddEnc):
            raise TypeError(f"{self.name()} requires two AddEnc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)

        self.randoms = set()
        c = [
            xi.__mul__(
                yi,
                loc=Location(
                    "ISWMult",
                    2,
                    f"multiplication of shares x,y with index[{i}]",
                    callloc,
                ),
            )
            for i, (xi, yi) in enumerate(zip(x.sharing, y.sharing))
        ]

        for i in range(x.n):
            for j in range(i + 1, x.n):
                name = f"R_{next(rc)}"
                R_poly = x.variable_ring(name)
                self.randoms.add(R_poly)
                R_obs = mk_obsval(
                    x.obsgraph,
                    R_poly,
                    R_poly,
                    location=Location(
                        "ISWMult", 1, description=f"R_{i}_{j}", caller=callloc
                    ),
                )
                xi_yj = x.sharing[i].__mul__(
                    y.sharing[j],
                    loc=Location(
                        "ISWMult",
                        1,
                        description=f"multiplication of shares x[{i}], y[{j}]",
                        caller=callloc,
                    ),
                )
                xj_yi = x.sharing[j].__mul__(
                    y.sharing[i],
                    loc=Location(
                        "ISWMult",
                        1,
                        description=f"multiplication of shares x[{j}], y[{i}]",
                        caller=callloc,
                    ),
                )
                r_xi_yj = R_obs.__add__(
                    xi_yj,
                    loc=Location(
                        "ISWMult",
                        1,
                        description=f"R_{i}_{j} - x[{i}] * y[{j}]",
                        caller=callloc,
                    ),
                )
                r_prime = r_xi_yj.__add__(
                    xj_yi,
                    loc=Location(
                        "ISWMult",
                        1,
                        description=f"R_prime_{i}_{j} = (R_{i}_{j} + x[{i}] * y[{j}]) + (x[{j}] * y[{i}])",
                        caller=callloc,
                    ),
                )
                c[i] = c[i].__sub__(
                    R_obs,
                    loc=Location(
                        "ISWMult",
                        1,
                        description=f"c{i} = c{i} - R_{i}_{j}",
                        caller=callloc,
                    ),
                )
                c[j] = c[j].__add__(
                    r_prime,
                    loc=Location(
                        "ISWMult",
                        1,
                        description=f"c{j} = c{j} + R_prime_{i}_{j}",
                        caller=callloc,
                    ),
                )
        new_secrets = [si * ti for si, ti in zip(x.secrets, y.secrets)]
        self.output_enc = x.copy(sharing=c, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"ISWMult only supports e == 0, but got {e}"
        assert k == 1, f"ISWMult only supports k == 1, but got {k}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, rc_count = AddEnc_setup(F, secrets, n, 200)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> AddEnc:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class ISWRefresh(Gadget[AddEnc]):
    def __init__(
        self,
        x: AddEnc,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(x, AddEnc):
            raise TypeError(f"{self.name()} requires two AddEnc inputs.")
        super().__init__([x], callloc)

        self.randoms = set()
        c = [xi for xi in x.sharing]

        for i in range(x.n):
            for j in range(i + 1, x.n):
                name = f"R_{next(rc)}"
                R_poly = x.variable_ring(name)
                self.randoms.add(R_poly)
                R_obs = mk_obsval(
                    x.obsgraph,
                    R_poly,
                    R_poly,
                    location=Location(
                        "ISWRefresh",
                        1,
                        description=f"R_{i}_{j}",
                        caller=callloc,
                    ),
                )
                c[i] = c[i].__sub__(
                    R_obs,
                    loc=Location(
                        "ISWRefresh",
                        1,
                        description=f"c{i} = c{i} - R_{i}_{j}",
                        caller=callloc,
                    ),
                )
                c[j] = c[j].__add__(
                    R_obs,
                    loc=Location(
                        "ISWRefresh",
                        1,
                        description=f"c{j} = c{j} + R_{i}_{j}",
                        caller=callloc,
                    ),
                )

        self.output_enc = x.copy(sharing=c, secrets=x.secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"ISWRefresh only supports e == 0, but got {e}"
        assert k == 1, f"ISWRefresh only supports k == 1, but got {k}"

        n = d + 1
        secrets = ["x"]
        encodings, rc_count = AddEnc_setup(F, secrets, n, 200)
        x_enc = encodings["x"]
        instance = cls(x=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> AddEnc:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


if __name__ == "__main__":
    fields = [GF(2**8), GF(7)]
    num_processes = 64
    continue_on_fail = False
    log = False
    min_d, max_d = 1, 7
    for d in range(min_d, max_d + 1):
        for F in fields:
            print(f"Testing ISW Mult for d={d}, n={d + 1}, and F={F}")
            isw_mul = ISWMult.with_defaults(d, 0, 0, F)
            isw_mul.functional_correctness()

            isw_ref = ISWRefresh.with_defaults(d, 0, 0, F)
            isw_ref.functional_correctness()
