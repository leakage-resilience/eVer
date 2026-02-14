# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from itertools import count
from typing import Callable, Optional, Self, Set, Type
from sage.all import GF
from sage.rings.polynomial.multi_polynomial import MPolynomial
from observations import Location, ObservableValue, mk_obsval
from gadget import Gadget
from encoding import GCMEncWMCS20, GCM_WMCS20_setup
from gen_parameter_vars import (
    generate_A_GCM_WMCS20,
    generate_A_hat_GCM_WMCS20,
)
from utils import (
    ObsList,
    ObsMat,
    colscale_obs,
    matmul_obs,
    mk_loc_factory,
    new_random_var,
    to_obsmat,
    to_obsval_factory,
    transpose,
    zeros,
)
from observations import _frobenius_mpoly_square


class GCM20AddSW(Gadget[GCMEncWMCS20]):
    """
    Sharewise addition of two GCM20 encodings.
    """

    def __init__(
        self, x: GCMEncWMCS20, y: GCMEncWMCS20, callloc: Optional[Location]
    ):
        if not isinstance(x, GCMEncWMCS20) or not isinstance(y, GCMEncWMCS20):
            raise TypeError(f"{self.name()} requires two GCM20Enc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)
        new_sharing = [
            xi.__add__(
                yi,
                loc=Location(
                    "GCM20AddSW",
                    1,
                    f"addition of shares with index[{i}]",
                    callloc,
                ),
            )
            for i, (xi, yi) in enumerate(zip(x.sharing, y.sharing))
        ]
        new_secrets = [si + ti for si, ti in zip(x.secrets, y.secrets)]
        self.output_enc = x.copy(sharing=new_sharing, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCM20AddSW only supports e == 0, but got {e}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, _ = GCM_WMCS20_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, callloc=None)

        return instance

    def output(self) -> GCMEncWMCS20:
        return self.output_enc


class GCM20MultSW(Gadget[GCMEncWMCS20]):
    """
    Sharewise multiplication of two GCM20 encodings.
    """

    def __init__(
        self, x: GCMEncWMCS20, y: GCMEncWMCS20, callloc: Optional[Location]
    ):
        if not isinstance(x, GCMEncWMCS20) or not isinstance(y, GCMEncWMCS20):
            raise TypeError(f"{self.name()} requires two GCM20Enc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)
        new_sharing = [
            xi.__mul__(
                yi,
                loc=Location(
                    "GCM20MultSW",
                    1,
                    f"multiplication of shares with index[{i}]",
                    callloc,
                ),
            )
            for i, (xi, yi) in enumerate(zip(x.sharing, y.sharing))
        ]
        new_secrets = [si * ti for si, ti in zip(x.secrets, y.secrets)]
        self.output_enc = x.copy(sharing=new_sharing, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCM20MultSW only supports e == 0, but got {e}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, _ = GCM_WMCS20_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, callloc=None)

        return instance

    def output(self) -> GCMEncWMCS20:
        return self.output_enc


class GCMMult_WMCS20(Gadget[GCMEncWMCS20]):
    def __init__(
        self,
        x: GCMEncWMCS20,
        y: GCMEncWMCS20,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(x, GCMEncWMCS20) or not isinstance(y, GCMEncWMCS20):
            raise TypeError(f"{self.name()} requires two GCMEncWMCS20 inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)

        self.randoms = set()

        to_obsval: Callable[[MPolynomial], ObservableValue] = to_obsval_factory(
            x
        )
        mk_loc_a: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part A", callloc
        )
        mk_loc_b: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part B", callloc
        )
        mk_loc_c: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part C", callloc
        )

        def new_random() -> MPolynomial:
            return new_random_var(x, rc, self.randoms)

        zero = to_obsval(x.variable_ring(0))

        A: ObsMat = to_obsmat(
            generate_A_GCM_WMCS20(x.base_ring, x.G, x.H),
            x.variable_ring,
            to_obsval,
        )

        A_hat: ObsMat = to_obsmat(
            generate_A_hat_GCM_WMCS20(x.base_ring, x.G, x.H, x.n, x.k, x.d),
            x.variable_ring,
            to_obsval,
        )
        R_1: ObsMat = [
            [zero for _ in range(x.k)]
            + [to_obsval(new_random()) for _ in range(x.d)]
            for _ in range(x.n)
        ]
        R_2: ObsMat = [
            [zero for _ in range(x.k)]
            + [to_obsval(new_random()) for _ in range(x.d)]
            for _ in range(x.n)
        ]

        S: ObsMat = zeros(x.n, x.n, zero)

        R_1_hat = transpose(
            matmul_obs(
                R_1, A, zero, mk_loc_a(1, "compute R_1_hat = [O,R_1] x A")
            )
        )

        R_2_hat = matmul_obs(
            R_2,
            A,
            zero,
            mk_loc_c(1, "compute R_2_hat = [O,R_2] x A"),
        )

        for i in range(x.n):
            for j in range(x.n):
                S[i][j] = x.sharing[i].__mul__(
                    y.sharing[j],
                    mk_loc_a(
                        4,
                        "compute S[{i}][{j}] = x[{i}] * y[{j}]",
                    ),
                )
                S[i][j] = S[i][j].__add__(
                    R_1_hat[i][j],
                    mk_loc_a(
                        4,
                        "compute S[{i}][{j}] = (x[{i}] * y[{j}]) + R_1_hat[{i}][{j}]",
                    ),
                )

        M_list: list[list[list[ObservableValue]]] = []
        for i in range(x.n):
            a_row = A_hat[i]  # 1×n row
            M_i = colscale_obs(
                A_hat,
                a_row,
                zero,
                mk_loc_a(
                    7,
                    f"M*_i = tensor(A_hat, diag(A_hat[{i},*]))",
                ),
            )  # shape n × N
            M_list.append(M_i)

        # Compute T with dim n x k
        T: ObsMat = zeros(x.n, x.k, zero)
        for i in range(x.n):
            T[i] = matmul_obs(
                [S[i]],
                M_list[i],
                zero,
                mk_loc_a(
                    8,
                    f"T_{i} = S_{i} x M_{i}",
                ),
            )[0]
        W = matmul_obs(
            T,
            A,
            zero,
            mk_loc_b(
                1,
                "W = T x A",
            ),
        )
        K: ObsMat = zeros(x.n, x.n, zero)
        # compute K with dim n x n
        for i in range(x.n):
            for j in range(x.n):
                K[i][j] = W[i][j].__add__(
                    R_2_hat[i][j],
                    mk_loc_c(
                        2,
                        f"K[{i}][{j}] = W[{i}][{j}] + R_2_hat[{i}][{j}]",
                    ),
                )

        # compute gadget output z_hat
        z_hat: ObsList = [zero for _ in range(x.n)]
        for j in range(x.n):
            sum = zero
            for i in range(x.n):
                sum = sum.__add__(
                    K[i][j],
                    mk_loc_c(
                        4,
                        f"z_hat[{j}] = sum_{i} K[{i}][{j}]",
                    ),
                )
            z_hat[j] = sum
        new_secrets = [si * ti for si, ti in zip(x.secrets, y.secrets)]
        self.output_enc = x.copy(sharing=z_hat, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCMMult only supports e == 0, but got {e}"

        n = d + k
        secrets = ["x", "y"]
        encodings, rc_count = GCM_WMCS20_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEncWMCS20:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class GCM_L_WMCS20(Gadget[GCMEncWMCS20]):
    def __init__(
        self,
        x: GCMEncWMCS20,
        rc: count,
        callloc: Optional[Location],
        is_GF2k: Optional[bool] = False,
    ):
        if not isinstance(x, GCMEncWMCS20):
            raise TypeError(f"{self.name()} requires two GCMEncWMCS20 inputs.")
        super().__init__([x], callloc)

        self.randoms = set()

        to_obsval: Callable[[MPolynomial], ObservableValue] = to_obsval_factory(
            x
        )
        mk_loc_a: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part A", callloc
        )
        mk_loc_b: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part B", callloc
        )
        mk_loc_c: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part C", callloc
        )

        def new_random() -> MPolynomial:
            return new_random_var(x, rc, self.randoms)

        def f_square(share: ObservableValue, loc: Location) -> ObservableValue:
            if is_GF2k:
                ps_square = _frobenius_mpoly_square(share.ps_obs.value)
                ni_square = _frobenius_mpoly_square(share.ni_obs.value)
            else:
                ps_square = share.ps_obs.value**2
                ni_square = share.ni_obs.value**2
            return mk_obsval(x.obsgraph, ps_square, ni_square, location=loc)

        zero = to_obsval(x.variable_ring(0))
        one = to_obsval(x.variable_ring(1))

        A: ObsMat = to_obsmat(
            generate_A_GCM_WMCS20(x.base_ring, x.G, x.H),
            x.variable_ring,
            to_obsval,
        )
        one_enc = matmul_obs(
            [[one for _ in range(x.k)] + [zero for _ in range(x.d)]],
            A,
            zero,
            mk_loc_a(1, "generate an encoding of k many 1s"),
        )[0]

        A_hat: ObsMat = to_obsmat(
            generate_A_hat_GCM_WMCS20(x.base_ring, x.G, x.H, x.n, x.k, x.d),
            x.variable_ring,
            to_obsval,
        )

        R_2: ObsMat = [
            [zero for _ in range(x.k)]
            + [to_obsval(new_random()) for _ in range(x.d)]
            for _ in range(x.n)
        ]
        S: ObsMat = zeros(x.n, x.n, zero)

        R_2_hat = matmul_obs(
            R_2,
            A,
            zero,
            mk_loc_c(1, "compute R_2_hat = [O,R_2] x A"),
        )

        for i in range(x.n):
            for j in range(x.n):
                S[i][j] = x.sharing[i].__mul__(
                    one_enc[j],
                    mk_loc_a(
                        3,
                        "compute S[{i}][{j}] = x[{i}] * 1[{j}]",
                    ),
                )

        M_list: list[ObsMat] = []
        for i in range(x.n):
            a_row = A_hat[i]  # 1×n row
            M_i = colscale_obs(
                A_hat,
                a_row,
                zero,
                mk_loc_a(
                    7,
                    f"M*_i = tensor(A_hat, diag(A_hat[{i},*]))",
                ),
            )  # shape n × N
            M_list.append(M_i)

        # Compute T with dim n x k
        T: ObsMat = zeros(x.n, x.k, zero)
        for i in range(x.n):
            T[i] = matmul_obs(
                [S[i]],
                M_list[i],
                zero,
                mk_loc_a(
                    7,
                    f"T_{i} = S_{i} x M_{i}",
                ),
            )[0]
        V: ObsMat = zeros(x.n, x.k, zero)

        # compute linear function onto T as f(T[i])
        for i in range(x.n):
            V[i] = [
                f_square(T[i][j], mk_loc_b(2, "V[{i}] = f(T[{i}])"))
                for j in range(x.k)
            ] + [zero for i in range(x.d)]

        W = matmul_obs(
            V,
            A,
            zero,
            mk_loc_b(
                5,
                "W = T x A",
            ),
        )
        K: ObsMat = zeros(x.n, x.n, zero)
        # compute K with dim n x n
        for i in range(x.n):
            for j in range(x.n):
                K[i][j] = W[i][j].__add__(
                    R_2_hat[i][j],
                    mk_loc_c(
                        2,
                        f"K[{i}][{j}] = W[{i}][{j}] + R_2_hat[{i}][{j}]",
                    ),
                )

        # compute gadget output z_hat
        z_hat: ObsList = [zero for _ in range(x.n)]
        for j in range(x.n):
            sum = zero
            for i in range(x.n):
                sum = sum.__add__(
                    K[i][j],
                    mk_loc_c(
                        4,
                        f"z_hat[{j}] = sum_{i} K[{i}][{j}]",
                    ),
                )
            z_hat[j] = sum
        new_secrets = [si**2 for si in x.secrets]
        self.output_enc = x.copy(sharing=z_hat, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCMMult only supports e == 0, but got {e}"

        n = d + k
        secrets = ["x"]
        encodings, rc_count = GCM_WMCS20_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        instance = cls(x=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEncWMCS20:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class GCM_Refresh_WMCS20(Gadget[GCMEncWMCS20]):
    def __init__(
        self,
        x: GCMEncWMCS20,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(x, GCMEncWMCS20):
            raise TypeError(f"{self.name()} requires two GCMEncWMCS20 inputs.")
        super().__init__([x], callloc)

        self.randoms = set()

        to_obsval: Callable[[MPolynomial], ObservableValue] = to_obsval_factory(
            x
        )
        mk_loc_a: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part A", callloc
        )
        mk_loc_b: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part B", callloc
        )
        mk_loc_c: Callable[[int, str], Location] = mk_loc_factory(
            "GCM part C", callloc
        )

        def new_random() -> MPolynomial:
            return new_random_var(x, rc, self.randoms)

        zero = to_obsval(x.variable_ring(0))
        one = to_obsval(x.variable_ring(1))

        A: ObsMat = to_obsmat(
            generate_A_GCM_WMCS20(x.base_ring, x.G, x.H),
            x.variable_ring,
            to_obsval,
        )
        one_enc = matmul_obs(
            [[one for _ in range(x.k)] + [zero for _ in range(x.d)]],
            A,
            zero,
            mk_loc_a(1, "generate an encoding of k many 1s"),
        )[0]

        A_hat: ObsMat = to_obsmat(
            generate_A_hat_GCM_WMCS20(x.base_ring, x.G, x.H, x.n, x.k, x.d),
            x.variable_ring,
            to_obsval,
        )

        R_2: ObsMat = [
            [zero for _ in range(x.k)]
            + [to_obsval(new_random()) for _ in range(x.d)]
            for _ in range(x.n)
        ]
        S: ObsMat = zeros(x.n, x.n, zero)

        R_2_hat = matmul_obs(
            R_2,
            A,
            zero,
            mk_loc_c(1, "compute R_2_hat = [O,R_2] x A"),
        )

        for i in range(x.n):
            for j in range(x.n):
                S[i][j] = x.sharing[i].__mul__(
                    one_enc[j],
                    mk_loc_a(
                        3,
                        "compute S[{i}][{j}] = x[{i}] * 1[{j}]",
                    ),
                )

        M_list: list[ObsMat] = []
        for i in range(x.n):
            a_row = A_hat[i]  # 1×n row
            M_i = colscale_obs(
                A_hat,
                a_row,
                zero,
                mk_loc_a(
                    7,
                    f"M*_i = tensor(A_hat, diag(A_hat[{i},*]))",
                ),
            )  # shape n × N
            M_list.append(M_i)

        # Compute T with dim n x k
        T: ObsMat = zeros(x.n, x.k, zero)
        for i in range(x.n):
            T[i] = matmul_obs(
                [S[i]],
                M_list[i],
                zero,
                mk_loc_a(
                    7,
                    f"T_{i} = S_{i} x M_{i}",
                ),
            )[0]
        V: ObsMat = zeros(x.n, x.k, zero)

        # compute linear function onto T as f(T[i])
        for i in range(x.n):
            V[i] = [T[i][j] for j in range(x.k)] + [zero for i in range(x.d)]

        W = matmul_obs(
            V,
            A,
            zero,
            mk_loc_b(
                5,
                "W = T x A",
            ),
        )
        K: ObsMat = zeros(x.n, x.n, zero)
        # compute K with dim n x n
        for i in range(x.n):
            for j in range(x.n):
                K[i][j] = W[i][j].__add__(
                    R_2_hat[i][j],
                    mk_loc_c(
                        2,
                        f"K[{i}][{j}] = W[{i}][{j}] + R_2_hat[{i}][{j}]",
                    ),
                )

        # compute gadget output z_hat
        z_hat: ObsList = [zero for _ in range(x.n)]
        for j in range(x.n):
            sum = zero
            for i in range(x.n):
                sum = sum.__add__(
                    K[i][j],
                    mk_loc_c(
                        4,
                        f"z_hat[{j}] = sum_{i} K[{i}][{j}]",
                    ),
                )
            z_hat[j] = sum
        new_secrets = [si for si in x.secrets]
        self.output_enc = x.copy(sharing=z_hat, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCMMult only supports e == 0, but got {e}"

        n = d + k
        secrets = ["x"]
        encodings, rc_count = GCM_WMCS20_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        instance = cls(x=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEncWMCS20:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class GCM20AESSbox(Gadget[GCMEncWMCS20]):
    """
    AES Sbox using GCMMult_WMCS20 and Refresh from https://tches.iacr.org/index.php/TCHES/article/view/8547/8112 with Sbox construction from https://eprint.iacr.org/2010/441.pdf.
    """

    def __init__(
        self,
        f: GCMEncWMCS20,
        rc: count,
        callloc: Optional[Location],
    ):
        assert isinstance(f, GCMEncWMCS20), (
            f"{self.name()} requires GCMEncWMCS20 input."
        )
        super().__init__([f], callloc)

        to_obsval = to_obsval_factory(f)
        self.randoms = set()
        mk_loc = mk_loc_factory("GCM20AESSbox", callloc)
        f2 = GCM_L_WMCS20(f, rc, mk_loc(1, "f2 = f * f"), is_GF2k=True)
        self.randoms.update(f2.randoms)
        f3 = GCMMult_WMCS20(f2.output(), f, rc, mk_loc(4, "f3 = f2 * f"))
        self.randoms.update(f3.randoms)
        f6 = GCM_L_WMCS20(
            f3.output(), rc, mk_loc(2, "f6 = f3 * f3"), is_GF2k=True
        )
        self.randoms.update(f6.randoms)
        f12 = GCM_L_WMCS20(
            f6.output(), rc, mk_loc(2, "f12 = f6 * f6"), is_GF2k=True
        )
        self.randoms.update(f12.randoms)
        f15 = GCMMult_WMCS20(
            f3.output(), f12.output(), rc, mk_loc(4, "f15 = f3 * f12")
        )
        self.randoms.update(f15.randoms)
        f30 = GCM_L_WMCS20(
            f15.output(), rc, mk_loc(2, "f30 = f15 * f15"), is_GF2k=True
        )
        self.randoms.update(f30.randoms)
        f60 = GCM_L_WMCS20(
            f30.output(), rc, mk_loc(2, "f60 = f30 * f30"), is_GF2k=True
        )
        self.randoms.update(f60.randoms)
        f120 = GCM_L_WMCS20(
            f60.output(), rc, mk_loc(2, "f120 = f60 * f60"), is_GF2k=True
        )
        self.randoms.update(f120.randoms)
        f240 = GCM_L_WMCS20(
            f120.output(), rc, mk_loc(2, "f240 = f120 * f120"), is_GF2k=True
        )
        self.randoms.update(f240.randoms)
        f252 = GCMMult_WMCS20(
            f240.output(), f12.output(), rc, mk_loc(4, "f252 = f240 * f12")
        )
        self.randoms.update(f252.randoms)
        f254 = GCMMult_WMCS20(
            f2.output(), f252.output(), rc, mk_loc(4, "f254 = f2 * f252")
        )
        self.randoms.update(f254.randoms)

        # generate sharings of constant values to perform addition and multiplication with constants
        enc_63 = f.copy(
            sharing=[to_obsval(f.variable_ring(f.field(0x63)))]
            + [to_obsval(f.variable_ring(f.field(0))) for _ in range(f.n - 1)],
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
        tmp = GCM20MultSW(f254.output(), enc_05, mk_loc(12, "f254 * 0x05"))
        res = GCM20AddSW(res, tmp.output(), mk_loc(13, "res += f254 * 0x05"))

        x = GCM_L_WMCS20(
            f254.output(), rc, mk_loc(14, "x2 = f254 * f254"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM20MultSW(x.output(), enc_09, mk_loc(15, "x2 * 0x09"))
        res = GCM20AddSW(
            res.output(), tmp.output(), mk_loc(16, "res += x2 * 0x09")
        )

        x = GCM_L_WMCS20(
            x.output(), rc, mk_loc(17, "x4 = x2 * x2"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM20MultSW(x.output(), enc_f9, mk_loc(18, "x4 * 0xf9"))
        res = GCM20AddSW(
            res.output(), tmp.output(), mk_loc(19, "res += x4 * 0xf9")
        )

        x = GCM_L_WMCS20(
            x.output(), rc, mk_loc(20, "x8 = x4 * x4"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM20MultSW(x.output(), enc_25, mk_loc(21, "x8 * 0x25"))
        res = GCM20AddSW(
            res.output(), tmp.output(), mk_loc(22, "res += x8 * 0x25")
        )

        x = GCM_L_WMCS20(
            x.output(), rc, mk_loc(23, "x16 = x8 * x8"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM20MultSW(x.output(), enc_f4, mk_loc(24, "x16 * 0xf4"))
        res = GCM20AddSW(
            res.output(), tmp.output(), mk_loc(25, "res += x16 * 0xf4")
        )

        x = GCM_L_WMCS20(
            x.output(), rc, mk_loc(26, "x32 = x16 * x16"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM20MultSW(x.output(), enc_01, mk_loc(27, "x32 * 0x01"))
        res = GCM20AddSW(
            res.output(), tmp.output(), mk_loc(28, "res += x32 * 0x01")
        )

        x = GCM_L_WMCS20(
            x.output(), rc, mk_loc(29, "x64 = x32 * x32"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM20MultSW(x.output(), enc_b5, mk_loc(30, "x64 * 0xb5"))
        res = GCM20AddSW(
            res.output(), tmp.output(), mk_loc(31, "res += x64 * 0xb5")
        )

        x = GCM_L_WMCS20(
            x.output(), rc, mk_loc(32, "x128 = x64 * x64"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM20MultSW(x.output(), enc_8f, mk_loc(33, "x128 * 0x8f"))
        res = GCM20AddSW(
            res.output(), tmp.output(), mk_loc(34, "res += x128 * 0x8f")
        )
        self.output_enc = res.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        secrets = ["x"]
        encodings, rc_count = GCM_WMCS20_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        instance = cls(f=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEncWMCS20:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


if __name__ == "__main__":
    # fields = [GF(7), GF(2**8)]
    fields = [GF(2**8)]
    num_processes = 2
    continue_on_fail = False
    log = False
    min_d, max_d = 1, 2
    min_k, max_k = 1, 1
    for d in range(min_d, max_d + 1):
        for k in range(min_k, max_k + 1):
            for F in fields:
                GCM_mul = GCMMult_WMCS20.with_defaults(d, k, 0, F)
                GCM_mul.functional_correctness()
                GCM_mul.verify_t_PS(
                    d,
                    num_worker=num_processes,
                    log=log,
                    max_memory_mb=400000,
                    timeout=3600000,
                )
                # GCM_ref = GCM_Refresh_WMCS20.with_defaults(d, k, 0, F)
                # GCM_ref.functional_correctness()
                # if F.characteristic() == 2:
                #     GCMl = GCM_L_WMCS20.with_defaults(d, k, 0, F)
                #     GCMl.functional_correctness()
