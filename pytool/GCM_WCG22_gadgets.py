# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from itertools import count
from typing import Callable, Optional, Self, Set, Type
from sage.all import GF
from sage.rings.polynomial.multi_polynomial import MPolynomial
from observations import Location, ObservableValue, mk_obsval
from gadget import Gadget
from encoding import GCMEnc_WCG22, GCM_WCG22_setup
from gen_parameter_vars import generate_A_hat_GCM
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


class GCM22AddSW(Gadget[GCMEnc_WCG22]):
    """
    Sharewise addition of two GCM22 encodings.
    """

    def __init__(
        self, x: GCMEnc_WCG22, y: GCMEnc_WCG22, callloc: Optional[Location]
    ):
        if not isinstance(x, GCMEnc_WCG22) or not isinstance(y, GCMEnc_WCG22):
            raise TypeError(f"{self.name()} requires two GCM22Enc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)
        new_sharing = [
            xi.__add__(
                yi,
                loc=Location(
                    "GCM22AddSW",
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
        assert e == 0, f"GCM22AddSW only supports e == 0, but got {e}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, _ = GCM_WCG22_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, callloc=None)

        return instance

    def output(self) -> GCMEnc_WCG22:
        return self.output_enc


class GCM22MultSW(Gadget[GCMEnc_WCG22]):
    """
    Sharewise multiplication of two GCM22 encodings.
    """

    def __init__(
        self, x: GCMEnc_WCG22, y: GCMEnc_WCG22, callloc: Optional[Location]
    ):
        if not isinstance(x, GCMEnc_WCG22) or not isinstance(y, GCMEnc_WCG22):
            raise TypeError(f"{self.name()} requires two GCM22Enc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)
        new_sharing = [
            xi.__mul__(
                yi,
                loc=Location(
                    "GCM22MultSW",
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
        assert e == 0, f"GCM22MultSW only supports e == 0, but got {e}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, _ = GCM_WCG22_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, callloc=None)

        return instance

    def output(self) -> GCMEnc_WCG22:
        return self.output_enc


class GCMMult_WCG22(Gadget[GCMEnc_WCG22]):
    def __init__(
        self,
        x: GCMEnc_WCG22,
        y: GCMEnc_WCG22,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(x, GCMEnc_WCG22) or not isinstance(y, GCMEnc_WCG22):
            raise TypeError(f"{self.name()} requires two GCM22Enc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)

        self.randoms = set()
        to_obsval: Callable[[MPolynomial], ObservableValue] = to_obsval_factory(
            x
        )
        mk_loc: Callable[[int, str], Location] = mk_loc_factory(
            "GCM22 Mult", callloc
        )

        def new_random() -> MPolynomial:
            return new_random_var(x, rc, self.randoms)

        zero = to_obsval(x.variable_ring(0))

        H: ObsMat = to_obsmat(x.H, x.variable_ring, to_obsval)
        A_hat: ObsMat = to_obsmat(
            generate_A_hat_GCM(x.base_ring, x.H, x.n, x.k, x.d),
            x.variable_ring,
            to_obsval,
        )

        R_1: ObsMat = [
            [to_obsval(new_random()) for _ in range(x.d)] for _ in range(x.n)
        ]
        R_1_hat = transpose(
            matmul_obs(R_1, H, zero, mk_loc(2, "compute R_1_hat = R_1 x H"))
        )
        R_2: ObsMat = [
            [to_obsval(new_random()) for _ in range(x.d)] for _ in range(x.n)
        ]

        R_2_hat = matmul_obs(
            R_2,
            H,
            zero,
            mk_loc(2, "compute R_2_hat = R_2 x H"),
        )
        S: ObsMat = zeros(x.n, x.n, zero)

        for i in range(x.n):
            for j in range(x.n):
                S[i][j] = x.sharing[i].__mul__(
                    y.sharing[j],
                    mk_loc(
                        5,
                        f"compute S[{i}][{j}] = x[{i}] * y[{j}]",
                    ),
                )
                S[i][j] = S[i][j].__add__(
                    R_1_hat[i][j],
                    mk_loc(
                        5,
                        f"compute S[{i}][{j}] = (x[{i}] * y[{j}]) + R_1_hat[{i}][{j}]",
                    ),
                )

        M_list: list[ObsMat] = []
        for i in range(x.n):
            a_row = A_hat[i]
            M_star_i = colscale_obs(
                A_hat,
                a_row,
                zero,
                mk_loc(
                    6,
                    f"M*_i = tensor(A_hat, diag(A_hat[{i},*]))",
                ),
            )  # shape n × N

            # M_i is the first k columns
            M_i = [[M_star_i[r][c] for c in range(x.k)] for r in range(x.n)]
            M_list.append(M_i)

        # Compute T with dim n x k
        T: ObsMat = zeros(x.n, x.k, zero)
        for i in range(x.n):
            T[i] = matmul_obs(
                [S[i]],
                M_list[i],
                zero,
                mk_loc(
                    10,
                    f"T_{i} = S_{i} x M_{i}",
                ),
            )[0] + [zero for _ in range(x.d)]  # append d many 0s to get nxn

        K: ObsMat = zeros(x.n, x.n, zero)
        # compute K with dim n x n
        for i in range(x.n):
            for j in range(x.n):
                K[i][j] = T[i][j].__add__(
                    R_2_hat[i][j],
                    mk_loc(
                        12,
                        f"K[{i}][{j}] = T[{i}][{j}] + R_2_hat[{i}][{j}]",
                    ),
                )

        # compute gadget output z_hat
        z_hat: ObsList = [zero for _ in range(x.n)]
        for j in range(x.n):
            sum = zero
            for i in range(x.n):
                sum = sum.__add__(
                    K[i][j],
                    mk_loc(
                        14,
                        f"z_hat[{j}] = sum_{i} K[{i}][{j}]",
                    ),
                )
            z_hat[j] = sum
        new_secrets = [si * ti for si, ti in zip(x.secrets, y.secrets)]
        self.output_enc = x.copy(sharing=z_hat, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCM22Mult only supports e == 0, but got {e}"

        n = d + k
        secrets = ["x", "y"]
        encodings, rc_count = GCM_WCG22_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEnc_WCG22:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class GCM_L_WCG22(Gadget[GCMEnc_WCG22]):
    def __init__(
        self,
        x: GCMEnc_WCG22,
        rc: count,
        callloc: Optional[Location],
        is_GF2k: Optional[bool] = False,
    ):
        if not isinstance(x, GCMEnc_WCG22):
            raise TypeError(f"{self.name()} requires two GCM22Enc inputs.")
        super().__init__([x], callloc)

        self.randoms = set()

        to_obsval: Callable[[MPolynomial], ObservableValue] = to_obsval_factory(
            x
        )
        mk_loc: Callable[[int, str], Location] = mk_loc_factory(
            "GCM L", callloc
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

        H: ObsMat = to_obsmat(x.H, x.variable_ring, to_obsval)
        A_hat: ObsMat = to_obsmat(
            generate_A_hat_GCM(x.base_ring, x.H, x.n, x.k, x.d),
            x.variable_ring,
            to_obsval,
        )

        R_2: ObsMat = [
            [to_obsval(new_random()) for _ in range(x.d)] for _ in range(x.n)
        ]

        R_2_hat = matmul_obs(
            R_2, H, zero, mk_loc(2, "compute R_2_hat = R_2 x H")
        )

        S: ObsMat = zeros(x.n, x.n, zero)
        for i in range(x.n):
            for j in range(x.k):
                S[i][j] = x.sharing[i]
            for j in range(x.k, x.n):
                S[i][j] = zero

        M_list: list[ObsMat] = []
        for i in range(x.n):
            a_row = A_hat[i]  # 1×n row
            M_star_i = colscale_obs(
                A_hat,
                a_row,
                zero,
                mk_loc(
                    6,
                    f"M*_i = tensor(A_hat, diag(A_hat[{i},*]))",
                ),
            )  # shape n × N

            # M_i is the first k columns
            M_i = [[M_star_i[r][c] for c in range(x.k)] for r in range(x.n)]
            M_list.append(M_i)

        # Compute T with dim n x k
        T: ObsMat = zeros(x.n, x.k, zero)
        for i in range(x.n):
            T[i] = matmul_obs(
                [S[i]],
                M_list[i],
                zero,
                mk_loc(
                    10,
                    f"T_{i} = S_{i} x M_{i}",
                ),
            )[0]

        # Compute V with dim n x k
        V: ObsMat = zeros(x.n, x.n, zero)

        # this computes the linear function f(T[i])
        for i in range(x.n):
            for j in range(x.k):
                V[i][j] = f_square(T[i][j], mk_loc(16, "V[{i}] = f(T[{i}])"))

        K: ObsMat = zeros(x.n, x.n, zero)
        # compute K with dim n x n
        for i in range(x.n):
            for j in range(x.n):
                K[i][j] = V[i][j].__add__(
                    R_2_hat[i][j],
                    mk_loc(
                        12,
                        f"K[{i}][{j}] = T[{i}][{j}] + R_2_hat[{i}][{j}]",
                    ),
                )

        # compute gadget output z_hat
        z_hat: ObsList = [zero for _ in range(x.n)]
        for j in range(x.n):
            sum = zero
            for i in range(x.n):
                sum = sum.__add__(
                    K[i][j],
                    loc=Location(
                        "GCM22 L",
                        14,
                        f"z_hat[{j}] = sum_{i} K[{i}][{j}]",
                        callloc,
                    ),
                )
            z_hat[j] = sum
        new_secrets = [si**2 for si in x.secrets]
        self.output_enc = x.copy(sharing=z_hat, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCM22_L only supports e == 0, but got {e}"

        n = d + k
        secrets = ["x"]
        encodings, rc_count = GCM_WCG22_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        instance = cls(x=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEnc_WCG22:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class GCM_Refresh_WCG22(Gadget[GCMEnc_WCG22]):
    def __init__(
        self,
        x: GCMEnc_WCG22,
        rc: count,
        callloc: Optional[Location],
    ):
        if not isinstance(x, GCMEnc_WCG22):
            raise TypeError(f"{self.name()} requires GCM22Enc input.")
        super().__init__([x], callloc)

        self.randoms = set()

        to_obsval: Callable[[MPolynomial], ObservableValue] = to_obsval_factory(
            x
        )
        mk_loc: Callable[[int, str], Location] = mk_loc_factory(
            "GCM Refresh", callloc
        )

        def new_random() -> MPolynomial:
            return new_random_var(x, rc, self.randoms)

        zero = to_obsval(x.variable_ring(0))

        H: ObsMat = to_obsmat(x.H, x.variable_ring, to_obsval)
        A_hat: ObsMat = to_obsmat(
            generate_A_hat_GCM(x.base_ring, x.H, x.n, x.k, x.d),
            x.variable_ring,
            to_obsval,
        )

        R_2: ObsMat = [
            [to_obsval(new_random()) for _ in range(x.d)] for _ in range(x.n)
        ]

        R_2_hat = matmul_obs(
            R_2, H, zero, mk_loc(2, "compute R_2_hat = R_2 x H")
        )

        S: ObsMat = zeros(x.n, x.n, zero)
        for i in range(x.n):
            for j in range(x.k):
                S[i][j] = x.sharing[i]
            for j in range(x.k, x.n):
                S[i][j] = zero

        M_list: list[ObsMat] = []
        for i in range(x.n):
            a_row = A_hat[i]  # 1×n row
            M_star_i = colscale_obs(
                A_hat,
                a_row,
                zero,
                mk_loc(
                    6,
                    f"M*_i = tensor(A_hat, diag(A_hat[{i},*]))",
                ),
            )  # shape n × N

            # M_i is the first k columns
            M_i = [[M_star_i[r][c] for c in range(x.k)] for r in range(x.n)]
            M_list.append(M_i)

        # Compute T with dim n x k
        T: ObsMat = zeros(x.n, x.k, zero)
        for i in range(x.n):
            T[i] = matmul_obs(
                [S[i]],
                M_list[i],
                zero,
                mk_loc(
                    10,
                    f"T_{i} = S_{i} x M_{i}",
                ),
            )[0]

        # Compute V with dim n x k
        V: ObsMat = zeros(x.n, x.n, zero)

        # this computes the linear function f(T[i])
        for i in range(x.n):
            for j in range(x.k):
                V[i][j] = T[i][j]

        K: ObsMat = zeros(x.n, x.n, zero)
        # compute K with dim n x n
        for i in range(x.n):
            for j in range(x.n):
                K[i][j] = V[i][j].__add__(
                    R_2_hat[i][j],
                    mk_loc(
                        12,
                        f"K[{i}][{j}] = T[{i}][{j}] + R_2_hat[{i}][{j}]",
                    ),
                )

        # compute gadget output z_hat
        z_hat: ObsList = [zero for _ in range(x.n)]
        for j in range(x.n):
            sum = zero
            for i in range(x.n):
                sum = sum.__add__(
                    K[i][j],
                    loc=Location(
                        "GCM L",
                        14,
                        f"z_hat[{j}] = sum_{i} K[{i}][{j}]",
                        callloc,
                    ),
                )
            z_hat[j] = sum
        new_secrets = [si for si in x.secrets]
        self.output_enc = x.copy(sharing=z_hat, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"GCM Refresh only supports e == 0, but got {e}"

        n = d + k
        secrets = ["x"]
        encodings, rc_count = GCM_WCG22_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        instance = cls(x=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEnc_WCG22:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class GCM22AESSbox(Gadget[GCMEnc_WCG22]):
    """
    AES Sbox using GCMMult_WCG22 and Refresh from https://tches.iacr.org/index.php/TCHES/article/view/8547/8112 with Sbox construction from https://eprint.iacr.org/2010/441.pdf.
    """

    def __init__(
        self,
        f: GCMEnc_WCG22,
        rc: count,
        callloc: Optional[Location],
    ):
        assert isinstance(f, GCMEnc_WCG22), (
            f"{self.name()} requires GCMEnc_WCG22 input."
        )
        super().__init__([f], callloc)

        to_obsval = to_obsval_factory(f)
        self.randoms = set()
        mk_loc = mk_loc_factory("GCM22AESSbox", callloc)
        f2 = GCM_L_WCG22(f, rc, mk_loc(1, "f2 = f * f"), is_GF2k=True)
        self.randoms.update(f2.randoms)
        f3 = GCMMult_WCG22(f2.output(), f, rc, mk_loc(4, "f3 = f2 * f"))
        self.randoms.update(f3.randoms)
        f6 = GCM_L_WCG22(
            f3.output(), rc, mk_loc(2, "f6 = f3 * f3"), is_GF2k=True
        )
        self.randoms.update(f6.randoms)
        f12 = GCM_L_WCG22(
            f6.output(), rc, mk_loc(2, "f12 = f6 * f6"), is_GF2k=True
        )
        self.randoms.update(f12.randoms)
        f15 = GCMMult_WCG22(
            f3.output(), f12.output(), rc, mk_loc(4, "f15 = f3 * f12")
        )
        self.randoms.update(f15.randoms)
        f30 = GCM_L_WCG22(
            f15.output(), rc, mk_loc(2, "f30 = f15 * f15"), is_GF2k=True
        )
        self.randoms.update(f30.randoms)
        f60 = GCM_L_WCG22(
            f30.output(), rc, mk_loc(2, "f60 = f30 * f30"), is_GF2k=True
        )
        self.randoms.update(f60.randoms)
        f120 = GCM_L_WCG22(
            f60.output(), rc, mk_loc(2, "f120 = f60 * f60"), is_GF2k=True
        )
        self.randoms.update(f120.randoms)
        f240 = GCM_L_WCG22(
            f120.output(), rc, mk_loc(2, "f240 = f120 * f120"), is_GF2k=True
        )
        self.randoms.update(f240.randoms)
        f252 = GCMMult_WCG22(
            f240.output(), f12.output(), rc, mk_loc(4, "f252 = f240 * f12")
        )
        self.randoms.update(f252.randoms)
        f254 = GCMMult_WCG22(
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
        tmp = GCM22MultSW(f254.output(), enc_05, mk_loc(12, "f254 * 0x05"))
        res = GCM22AddSW(res, tmp.output(), mk_loc(13, "res += f254 * 0x05"))

        x = GCM_L_WCG22(
            f254.output(), rc, mk_loc(14, "x2 = f254 * f254"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM22MultSW(x.output(), enc_09, mk_loc(15, "x2 * 0x09"))
        res = GCM22AddSW(
            res.output(), tmp.output(), mk_loc(16, "res += x2 * 0x09")
        )

        x = GCM_L_WCG22(
            x.output(), rc, mk_loc(17, "x4 = x2 * x2"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM22MultSW(x.output(), enc_f9, mk_loc(18, "x4 * 0xf9"))
        res = GCM22AddSW(
            res.output(), tmp.output(), mk_loc(19, "res += x4 * 0xf9")
        )

        x = GCM_L_WCG22(
            x.output(), rc, mk_loc(20, "x8 = x4 * x4"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM22MultSW(x.output(), enc_25, mk_loc(21, "x8 * 0x25"))
        res = GCM22AddSW(
            res.output(), tmp.output(), mk_loc(22, "res += x8 * 0x25")
        )

        x = GCM_L_WCG22(
            x.output(), rc, mk_loc(23, "x16 = x8 * x8"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM22MultSW(x.output(), enc_f4, mk_loc(24, "x16 * 0xf4"))
        res = GCM22AddSW(
            res.output(), tmp.output(), mk_loc(25, "res += x16 * 0xf4")
        )

        x = GCM_L_WCG22(
            x.output(), rc, mk_loc(26, "x32 = x16 * x16"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM22MultSW(x.output(), enc_01, mk_loc(27, "x32 * 0x01"))
        res = GCM22AddSW(
            res.output(), tmp.output(), mk_loc(28, "res += x32 * 0x01")
        )

        x = GCM_L_WCG22(
            x.output(), rc, mk_loc(29, "x64 = x32 * x32"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM22MultSW(x.output(), enc_b5, mk_loc(30, "x64 * 0xb5"))
        res = GCM22AddSW(
            res.output(), tmp.output(), mk_loc(31, "res += x64 * 0xb5")
        )

        x = GCM_L_WCG22(
            x.output(), rc, mk_loc(32, "x128 = x64 * x64"), is_GF2k=True
        )
        self.randoms.update(x.randoms)
        tmp = GCM22MultSW(x.output(), enc_8f, mk_loc(33, "x128 * 0x8f"))
        res = GCM22AddSW(
            res.output(), tmp.output(), mk_loc(34, "res += x128 * 0x8f")
        )
        self.output_enc = res.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        secrets = ["x"]
        encodings, rc_count = GCM_WCG22_setup(d, e, n, k, F, secrets, 200)
        x_enc = encodings["x"]
        instance = cls(f=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> GCMEnc_WCG22:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


if __name__ == "__main__":
    fields = [GF(7), GF(2**8)]
    num_processes = 64
    continue_on_fail = False
    log = False
    min_d, max_d = 1, 2
    min_k, max_k = 1, 1

    for d in range(min_d, max_d + 1):
        for k in range(min_k, max_k + 1):
            for F in fields:
                GCM_mul = GCMMult_WCG22.with_defaults(d, k, 0, F)
                GCM_mul.functional_correctness()
                GCM_mul.verify_t_PS(
                    d,
                    num_worker=num_processes,
                    continue_on_fail=continue_on_fail,
                    log=log,
                )

                GCM_ref = GCM_Refresh_WCG22.with_defaults(d, k, 0, F)
                GCM_ref.functional_correctness()
                if F.characteristic() == 2:
                    GCMl = GCM_L_WCG22.with_defaults(d, k, 0, F)
                    GCMl.functional_correctness()
