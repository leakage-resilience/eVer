# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from itertools import count
from typing import Optional, Self, Set, Type

from observations import Location, mk_obsval
from gadget import Gadget
from encoding import IPEnc, IP_setup
from utils import mk_loc_factory, to_obsval_factory


class IPAddGadget(Gadget[IPEnc]):
    """
    Addition of two sharings in the IP masked domain. Algorithm 4 from https://www.iacr.org/archive/eurocrypt2015/90560293/90560293.pdf .
    Usage of vector L is implicit, since all encodings share the same L and IPAdd does not need to compute anything w.r.t. L.
    """

    def __init__(self, x: IPEnc, y: IPEnc, callloc: Optional[Location]):
        if not isinstance(x, IPEnc) or not isinstance(y, IPEnc):
            raise TypeError(f"{self.name()} requires two PolyEnc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)
        new_sharing = [
            xi.__add__(
                yi,
                loc=Location(
                    "IPAdd", 2, f"addition of shares with index[{i}]", callloc
                ),
            )
            for i, (xi, yi) in enumerate(zip(x.sharing, y.sharing))
        ]
        new_secrets = [si + ti for si, ti in zip(x.secrets, y.secrets)]
        self.output_enc = x.copy(sharing=new_sharing, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d, k, e, F) -> Self:
        assert e == 0, f"IPAddGadget only supports e == 0, but got {e}"
        assert k == 1, f"IPAddGadget only supports k == 1, but got {k}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, _ = IP_setup(F, secrets, n, 50)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, callloc=None)

        return instance

    def output(self) -> IPEnc:
        return self.output_enc


class IPSWMulGadget(Gadget[IPEnc]):
    """
    Sharewise multiplication of two sharings in the IP masked domain.
    Usage of vector L is implicit, since all encodings share the same L.
    """

    def __init__(self, x: IPEnc, y: IPEnc, callloc: Optional[Location]):
        if not isinstance(x, IPEnc) or not isinstance(y, IPEnc):
            raise TypeError(f"{self.name()} requires two IPEnc inputs.")
        if x.field != y.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([x, y], callloc)
        new_sharing = [
            xi.__mul__(
                yi,
                loc=Location(
                    "SWIPMult",
                    2,
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
        assert e == 0, f"IPMulGadget only supports e == 0, but got {e}"
        assert k == 1, f"IPMulGadget only supports k == 1, but got {k}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, _ = IP_setup(F, secrets, n, 50)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(x=x_enc, y=y_enc, callloc=None)

        return instance

    def output(self) -> IPEnc:
        return self.output_enc


class IPRefreshGadget(Gadget[IPEnc]):
    """
    Refresh an IPEnc through addition of new randomness. Algorithm 5 from https://eprint.iacr.org/2017/1047.pdf .
    """

    def __init__(self, R: IPEnc, rc: count, callloc: Optional[Location]):
        if not isinstance(R, IPEnc):
            raise TypeError(f"{self.name()} requires two PolyEnc inputs.")
        super().__init__([R], callloc)
        self.randoms = set()

        A = []
        L = R.L[1:]
        zero = mk_obsval(
            R.obsgraph, R.variable_ring.zero(), R.variable_ring.zero()
        )
        L = [
            mk_obsval(
                R.obsgraph,
                R.base_ring(l),
                R.base_ring(l),
                location=Location(
                    "IPRefresh",
                    1,
                    description="convert L to obs values",
                    caller=callloc,
                ),
            )
            for l in L
        ]
        for _ in range(1, R.n):
            name = f"R_{next(rc)}"
            R_i_poly = R.variable_ring(name)
            self.randoms.add(R_i_poly)
            A.append(
                mk_obsval(
                    R.obsgraph,
                    R_i_poly,
                    R_i_poly,
                    location=Location(
                        "IPRefresh",
                        1,
                        description="gen randoms",
                        caller=callloc,
                    ),
                )
            )  # position corresponds to line one in the paper algorithm
        # use an ObservationValue to make the following sum operation trackable as Observations
        sum = mk_obsval(
            R.obsgraph,
            R.variable_ring.zero(),
            R.variable_ring.zero(),
            location=Location(
                "IPRefresh", 1, description="sum up first share", caller=callloc
            ),
        )
        for a, l in zip(A, L):
            sum += a * l

        A = [zero - sum] + A

        R_prime = [
            ri.__add__(
                ai,
                loc=Location(
                    "IPRefresh",
                    2,
                    f"addition of shares with index[{i}]",
                    callloc,
                ),
            )
            for i, (ri, ai) in enumerate(zip(R.sharing, A))
        ]
        self.output_enc = R.copy(sharing=R_prime)

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        assert e == 0, f"IPRefreshGadget only supports e == 0, but got {e}"
        assert k == 1, f"IPRefreshGadget only supports k == 1, but got {k}"

        n = d + 1
        secrets = ["x"]
        encodings, rc_count = IP_setup(F, secrets, n, 50)
        x_enc = encodings["x"]
        instance = cls(x_enc, rc_count, callloc=None)

        return instance

    def output(self) -> IPEnc:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class SecIPRefreshGadget(Gadget[IPEnc]):
    """
    SNI Refresh an IPEnc `X` performing n IPRefreshs. Algorithm 6 from https://eprint.iacr.org/2017/1047.pdf .
    """

    def __init__(self, X: IPEnc, rc: count, callloc: Optional[Location]):
        if not isinstance(X, IPEnc):
            raise TypeError(f"{self.name()} requires two PolyEnc inputs.")
        super().__init__([X], callloc)
        self.randoms = set()

        Y = X
        for _ in range(X.n):
            refresh = IPRefreshGadget(
                Y, rc, callloc=Location("SecIPRefresh", caller=callloc)
            )
            self.randoms.update(refresh.random_vars())
            Y = refresh.output()

        self.output_enc = Y

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        assert e == 0, f"SecIPRefreshGadget only supports e == 0, but got {e}"
        assert k == 1, f"SecIPRefreshGadget only supports k == 1, but got {k}"

        n = d + 1
        secrets = ["x"]
        encodings, rc_count = IP_setup(F, secrets, n, 50)
        x_enc = encodings["x"]
        instance = cls(x_enc, rc_count, callloc=None)

        return instance

    def output(self) -> IPEnc:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class IPMultGadget(Gadget[IPEnc]):
    """
    Perform an IP masked multiplication of two IPEncs according to Algorithm 3 from https://eprint.iacr.org/2017/1047.pdf .
    """

    def __init__(
        self, A: IPEnc, B: IPEnc, rc: count, callloc: Optional[Location]
    ):
        if not isinstance(A, IPEnc) or not isinstance(B, IPEnc):
            raise TypeError(f"{self.name()} requires two PolyEnc inputs.")
        if A.field != B.field:
            raise ValueError("Fields differ between the two encodings.")
        super().__init__([A, B], callloc)

        self.randoms = set()

        # turn L into ObservationValues to allow for correct operations
        L = [mk_obsval(A.obsgraph, l, l) for l in A.L]

        # dummy obs for constants
        zero = mk_obsval(
            A.obsgraph, A.variable_ring.zero(), A.variable_ring.zero()
        )
        one = mk_obsval(A.obsgraph, A.variable_ring(1), A.variable_ring(1))

        # compute matrix T
        T = [[zero for _ in range(A.n)] for _ in range(A.n)]
        for i in range(A.n):
            for j in range(A.n):
                T[i][j] = (
                    A.sharing[i].__mul__(
                        B.sharing[j],
                        loc=Location(
                            "IPMul",
                            3,
                            f"compute T with A_i={i}, B_j={j}",
                            callloc,
                        ),
                    )
                ).__mul__(
                    L[j],
                    loc=Location(
                        "IPMul",
                        3,
                        f"compute T with A[{i}], B[{j}], L[{j}]",
                        callloc,
                    ),
                )

        U = [[zero for _ in range(A.n)] for _ in range(A.n)]
        U_prime = [[zero for _ in range(A.n)] for _ in range(A.n)]
        # compute matrices U and U'
        for i in range(A.n):
            # U_i_i = A.variable_ring.zero() ommit due to init above
            for j in range(A.n):
                if i < j:
                    name = f"R_{next(rc)}"
                    R_poly = A.variable_ring(name)
                    self.randoms.add(R_poly)
                    U_prime[i][j] = mk_obsval(
                        A.obsgraph,
                        R_poly,
                        R_poly,
                        location=Location(
                            "IPMult",
                            11,
                            description=f"U_prime[{i}][{j}]",
                            caller=callloc,
                        ),
                    )

                if i > j:
                    # TODO: one element negation is not implemented so we instead subtract from Observation zero
                    U_prime[i][j] = zero.__sub__(
                        U_prime[j][i],
                        loc=Location(
                            "IPMult",
                            14,
                            description=f"U_prime[{i}][{j}] = -U_prime[{j}][{i}]",
                            caller=callloc,
                        ),
                    )

                delta_i_j = zero if i == j else one
                U[i][j] = (U_prime[i][j] * delta_i_j).__mul__(
                    one / L[i],
                    loc=Location(
                        "IPMult",
                        16,
                        description=f"compute U[{i}][{j}]",
                        caller=callloc,
                    ),
                )

        # compute matrix V
        V = [
            [
                T[i][j].__add__(
                    U[i][j],
                    loc=Location(
                        "IPMult",
                        20,
                        description=f"compute V[{i}][{j}]",
                        caller=callloc,
                    ),
                )
                for j in range(A.n)
            ]
            for i in range(A.n)
        ]

        C = []

        for i in range(A.n):
            sum = zero
            for j in range(A.n):
                sum = sum.__add__(
                    V[i][j],
                    loc=Location(
                        "IPMult",
                        23,
                        description=f"sum for C[{i}] from 0 to j={j}: sum += V[{i}][{j}]",
                        caller=callloc,
                    ),
                )
            C.append(sum)

        new_secrets = [si * ti for si, ti in zip(A.secrets, B.secrets)]
        self.output_enc = A.copy(sharing=C, secrets=new_secrets)

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        assert e == 0, f"IPMultGadget only supports e == 0, but got {e}"
        assert k == 1, f"IPMultGadget only supports k == 1, but got {k}"

        n = d + 1
        secrets = ["x", "y"]
        encodings, rc_count = IP_setup(F, secrets, n, 50)
        x_enc = encodings["x"]
        y_enc = encodings["y"]
        instance = cls(A=x_enc, B=y_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> IPEnc:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms


class IPSquare(Gadget[IPEnc]):
    """
    Linear squaring of all shares, only works correctly in GF(2)^k since we use Frobenius endomorphism here https://en.wikipedia.org/wiki/Frobenius_endomorphism.
    """

    def __init__(self, f: IPEnc, callloc: Optional[Location]):
        if not isinstance(f, IPEnc):
            raise TypeError(f"{self.name()} requires two IPEnc inputs.")
        super().__init__([f], callloc)
        to_obsval = to_obsval_factory(f)

        new_sharing = [
            fi.square_GF2k(
                loc=Location(
                    "IPSquare",
                    2,
                    f"squaring of shares with index[{i}]",
                    callloc,
                ),
            ).__mul__(
                to_obsval(f.L[i]),
                loc=Location(
                    "IPSquare",
                    2,
                    f"X{[i]} * L{[i]}",
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
        secrets = ["x"]
        encodings, rc_count = IP_setup(F, secrets, n, 50)
        x_enc = encodings["x"]
        instance = cls(f=x_enc, callloc=None)

        return instance

    def output(self) -> IPEnc:
        return self.output_enc


class IPAESSbox(Gadget[IPEnc]):
    """
    AES Sbox using IP masking from https://eprint.iacr.org/2017/1047.pdf.
    """

    def __init__(
        self,
        f: IPEnc,
        rc: count,
        callloc: Optional[Location],
    ):
        assert isinstance(f, IPEnc), f"{self.name()} requires IPEnc input."
        super().__init__([f], callloc)

        to_obsval = to_obsval_factory(f)
        self.randoms = set()
        mk_loc = mk_loc_factory("IPSbox", callloc)
        f2 = IPSquare(f, mk_loc(1, "f2 = f * f"))
        f2 = SecIPRefreshGadget(f2.output(), rc, mk_loc(2, "f2 refresh"))
        self.randoms.update(f2.randoms)
        f3 = IPMultGadget(f2.output(), f, rc, mk_loc(3, "f3 = f2 * f"))
        self.randoms.update(f3.randoms)
        f6 = IPSquare(f3.output(), mk_loc(4, "f6 = f3 * f3"))
        f12 = IPSquare(f6.output(), mk_loc(5, "f12 = f6 * f6"))
        f12 = SecIPRefreshGadget(f12.output(), rc, mk_loc(6, "f12 refresh"))
        self.randoms.update(f12.randoms)
        f15 = IPMultGadget(
            f3.output(), f12.output(), rc, mk_loc(7, "f15 = f3 * f12")
        )
        self.randoms.update(f15.randoms)
        f30 = IPSquare(f15.output(), mk_loc(8, "f30 = f15 * f15"))
        f60 = IPSquare(f30.output(), mk_loc(9, "f60 = f30 * f30"))
        f120 = IPSquare(f60.output(), mk_loc(10, "f120 = f60 * f60"))
        f240 = IPSquare(f120.output(), mk_loc(11, "f240 = f120 * f120"))
        f252 = IPMultGadget(
            f240.output(), f12.output(), rc, mk_loc(12, "f252 = f240 * f12")
        )
        self.randoms.update(f252.randoms)
        f254 = IPMultGadget(
            f2.output(), f252.output(), rc, mk_loc(13, "f254 = f2 * f252")
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
        tmp = IPSWMulGadget(f254.output(), enc_05, mk_loc(14, "f254 * 0x05"))
        res = IPAddGadget(res, tmp.output(), mk_loc(15, "res += f254 * 0x05"))

        x = IPSquare(f254.output(), mk_loc(16, "x2 = f254 * f254"))
        tmp = IPSWMulGadget(x.output(), enc_09, mk_loc(17, "x2 * 0x09"))
        res = IPAddGadget(
            res.output(), tmp.output(), mk_loc(18, "res += x2 * 0x09")
        )

        x = IPSquare(x.output(), mk_loc(19, "x4 = x2 * x2"))
        tmp = IPSWMulGadget(x.output(), enc_f9, mk_loc(20, "x4 * 0xf9"))
        res = IPAddGadget(
            res.output(), tmp.output(), mk_loc(21, "res += x4 * 0xf9")
        )

        x = IPSquare(x.output(), mk_loc(22, "x8 = x4 * x4"))
        tmp = IPSWMulGadget(x.output(), enc_25, mk_loc(23, "x8 * 0x25"))
        res = IPAddGadget(
            res.output(), tmp.output(), mk_loc(24, "res += x8 * 0x25")
        )

        x = IPSquare(x.output(), mk_loc(25, "x16 = x8 * x8"))
        tmp = IPSWMulGadget(x.output(), enc_f4, mk_loc(26, "x16 * 0xf4"))
        res = IPAddGadget(
            res.output(), tmp.output(), mk_loc(27, "res += x16 * 0xf4")
        )

        x = IPSquare(x.output(), mk_loc(26, "x32 = x16 * x16"))
        tmp = IPSWMulGadget(x.output(), enc_01, mk_loc(27, "x32 * 0x01"))
        res = IPAddGadget(
            res.output(), tmp.output(), mk_loc(28, "res += x32 * 0x01")
        )

        x = IPSquare(x.output(), mk_loc(29, "x64 = x32 * x32"))
        tmp = IPSWMulGadget(x.output(), enc_b5, mk_loc(30, "x64 * 0xb5"))
        res = IPAddGadget(
            res.output(), tmp.output(), mk_loc(31, "res += x64 * 0xb5")
        )

        x = IPSquare(x.output(), mk_loc(32, "x128 = x64 * x64"))
        tmp = IPSWMulGadget(x.output(), enc_8f, mk_loc(33, "x128 * 0x8f"))
        res = IPAddGadget(
            res.output(), tmp.output(), mk_loc(34, "res += x128 * 0x8f")
        )
        self.output_enc = res.output()

    @classmethod
    def with_defaults(cls: Type[Self], d: int, k: int, e: int, F) -> Self:
        n = d + e + 1
        secrets = ["x"]
        encodings, rc_count = IP_setup(F, secrets, n, 50)
        x_enc = encodings["x"]
        instance = cls(f=x_enc, rc=rc_count, callloc=None)

        return instance

    def output(self) -> IPEnc:
        return self.output_enc

    def random_vars(self) -> Set:
        return self.randoms
