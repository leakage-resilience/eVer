# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from dataclasses import dataclass, field
from math import comb
from typing import (
    Dict,
    List,
    Self,
    Sequence,
    Set,
    Tuple,
)
from itertools import combinations, count
from sage.all import matrix, PolynomialRing
from sage.rings.ring import CommutativeRing
from sage.matrix.constructor import Matrix
from gen_parameter_vars import (
    generate_A_GCM_WMCS20,
    generate_G_GCM_WMCS20,
    generate_H_GCM,
    generate_H_GCM_WMCS20,
    generate_d_private_encoder_constraints,
    generate_full_row_rank_constraints,
    generate_inverse_vandermonde,
    generate_M_enc_for_degree_d,
    generate_M_dec_for_degree_d,
    generate_A_GCM,
)
from sage.rings.polynomial.multi_polynomial import MPolynomial
from observations import ObservableValue, ObservationGraph, mk_obsval
from polyring import gen_rings_for_gadgets


@dataclass
class Encoding:
    d: int
    e: int
    n: int
    obsgraph: ObservationGraph
    base_ring: CommutativeRing
    variable_ring: CommutativeRing
    sharing: list[ObservableValue] = field(init=False, default_factory=list)
    secrets: list[MPolynomial]

    field: CommutativeRing

    def __post_init__(self):
        if self.d < 1:
            raise ValueError(
                f"Encoding must have threshold d>0, but got d={self.d}."
            )
        if len(self.secrets) == 0:
            raise ValueError("Encoding must have at least one secret variable.")

    @property
    def k(self) -> int:
        """Number of encoded secrets."""
        return len(self.secrets)

    def encode(self, secret_vars) -> Sequence[MPolynomial]:
        """
        An encoding type must have a function to encode secrets.
        """
        raise NotImplementedError

    def decode(self) -> Sequence[MPolynomial]:
        """
        An encoding type must have a function to decode its sharing.
        """
        raise NotImplementedError

    def parameter_vars(self) -> Set[MPolynomial]:
        """
        Variables used to parameterize or instatiate the encoding, e.g., support points for PolyEnc and L vec for IPEnc
        """
        raise NotImplementedError

    def ps_random_vars(self) -> Set[MPolynomial]:
        """
        Return the random variables that were used in the process of computing the sharing of an actual secret variable.
        """

        raise NotImplementedError

    def get_encoded_shares(self) -> Sequence[MPolynomial]:
        """
        Return the shares of Encoding in probing security style, i.e.,
        shares are expressions over random variables and secrets.
        """
        encoding = [share.ps_obs.value for share in self.sharing]
        return encoding

    def get_symbolic_shares(self) -> Sequence[MPolynomial]:
        """
        Return the shares of this Encoding in non-interference style, i.e.,
        shares are symbols.
        """
        symbolic_shares = [share.ni_obs.value for share in self.sharing]
        return symbolic_shares

    def get_constraint_equalities(self) -> Sequence[MPolynomial]:
        """
        Return the constraints placed on the encoding for security purposes encoded as equalities, e.g. d-privacy notion for GCM.
        """
        return []

    def get_constraint_inequalities(self) -> Sequence[MPolynomial]:
        """
        Return the constraints placed on the encoding for security purposes encoded as inequalities, e.g. non-zero and pairwise distinct supports for poly masking, full rank matrix A for GCM, non-zero sampled L for IPM.
        """
        return []

    def compute_groebner_ideal(self):
        """
        Create an ideal over the constraints provided by the encoding and compute its groebner basis.
        Also return the extended ring used for the groebner basis.
        """
        equalities = self.get_constraint_equalities()
        inequalities = self.get_constraint_inequalities()
        S = self.base_ring

        if not equalities and not inequalities:
            return S, [S(0)]

        # Rabinowitsch trick with auxiliary variables
        aux_var_names = [f"aux_{i}" for i in range(len(inequalities))]
        S_ext = PolynomialRing(
            S.base_ring(),
            list(S.variable_names()) + aux_var_names,
            order="degrevlex",
        )

        # Build homomorphism S -> S_ext to map variables
        phi = S.hom([S_ext(x) for x in S.variable_names()], S_ext)

        constraint_polys = []

        # Add inequality constraints with auxiliary variables
        for i, ineq in enumerate(inequalities):
            aux = S_ext(aux_var_names[i])
            constraint_polys.append(phi(ineq) * aux - 1)

        # Add mapped equality constraints
        if equalities:
            constraint_polys.extend(phi(eq) for eq in equalities)

        I = S_ext.ideal(constraint_polys)
        G0 = I.groebner_basis(algorithm="libsingular:slimgb")
        G0 = S_ext.ideal(G0).interreduced_basis()
        return S_ext, G0


@dataclass
class PolyEnc(Encoding):
    base_ring: CommutativeRing
    variable_ring: CommutativeRing
    support_points: list[MPolynomial]
    secret_support_points: list[MPolynomial] = field(default_factory=list)
    symbolic_shares: list[MPolynomial] = field(default_factory=list)
    M_enc: Matrix = field(init=False, default_factory=Matrix)
    M_dec: Matrix = field(init=False, default_factory=Matrix)
    rc_count: count = field(default_factory=count)
    # internal flag to skip the __post_init__ encoding step
    _skip_encode: bool = field(init=False, default=False)

    def __post_init__(self):
        super().__post_init__()
        if self._skip_encode:
            # we were built from existing DualValue sharing,
            # skip all the re-encoding bits
            return

        supp_set = set(self.support_points)
        if self.k == 1:
            self.secret_support_points = [
                self.base_ring.zero()
            ]  # Secret shamir sharing assumption
        if len(self.secret_support_points) != self.k:
            raise ValueError(
                f"PolyEnc inconsistent number of secrets and secret support points, got k = {self.k} and supports: {self.secret_support_points}"
            )

        if any(not isinstance(suppp, MPolynomial) for suppp in supp_set):
            raise ValueError(
                f"PolyEnc requires polynomials as support points but got {[(type(suppp), suppp) for suppp in self.support_points]}"
            )
        if self.n < self.d + self.e + 1:
            raise ValueError(
                f"PolyEnc requires n >= d + e + 1, but got n={self.n}, d={self.d}, e={self.e}."
            )
        if len(supp_set) != self.n:
            raise ValueError(
                f"PolyEnc requires {self.n} distinct supports but got {len(set(self.support_points))}: {set(self.support_points)}."
            )
        elif self.base_ring.zero() in set(self.support_points):
            raise ValueError(
                "PolyEnc with zero support point is not permitted."
            )

        if self.k > 1:
            self.M_enc = generate_M_enc_for_degree_d(
                self.base_ring,
                list(self.secret_support_points),
                list(self.support_points),
                len(self.support_points),
                self.k,
                self.d,
            )

            self.M_dec = generate_M_dec_for_degree_d(
                self.base_ring,
                list(self.secret_support_points),
                list(self.support_points),
                len(self.support_points),
                self.k,
                self.d,
            )

        # normal path: create fresh shares
        encoding = self.encode(self.secrets)

        self.sharing = [
            mk_obsval(self.obsgraph, enc, sym)
            for enc, sym in zip(encoding, self.symbolic_shares)
        ]

    def copy(self, **overrides) -> Self:
        """
        Make a brand-new PolyEnc that starts as a shallow clone of `self`,
        then replaces any attributes given in `overrides`.

        Example usages:
        ```
        # Clone the PolyEnc, but change the shares and secrets:
            new = old.copy(
                sharing=new_sharing,
                secrets=new_secrets
            )
        ```
        """
        # 1) Allocate a blank PolyEnc without running __post_init__:
        new_obj = self.__class__.__new__(self.__class__)
        # 2) Ensure __post_init__ is never called on this clone:
        new_obj._skip_encode = True

        # 3) Copy every attribute from self.__dict__ into new_obj:
        for attr_name, attr_val in self.__dict__.items():
            setattr(new_obj, attr_name, attr_val)

        # 4) Apply any overrides the user passed in:
        for key, val in overrides.items():
            if not hasattr(new_obj, key):
                raise AttributeError(
                    f"Cannot override '{key}': no such attribute in PolyEnc"
                )
            setattr(new_obj, key, val)

        # 5) If the user replaced .sharing but did not supply .symbolic_shares,
        #    then recompute symbolic_shares from the new DualValue list:
        if "sharing" in overrides and "symbolic_shares" not in overrides:
            new_obj.symbolic_shares = [dv.ps_obs for dv in new_obj.sharing]

        return new_obj

    def decode_packed_secret_sharing(self) -> list[MPolynomial]:
        shares = self.get_encoded_shares()
        decoded_secrets = self.M_dec * matrix(shares).transpose()
        return [decoded_secrets[i][0] for i in range(self.k)]

    def encode_packed_secret_sharing(
        self, secret_vars
    ) -> Sequence[MPolynomial]:
        shares_n = []
        self.randoms = set()
        for _ in range(self.d + 1 - self.k):
            name = f"R_{next(self.rc_count)}"
            shares_n.append(self.variable_ring(name))
            self.randoms.add(self.variable_ring(name))

        shares = self.M_enc * matrix(secret_vars + shares_n).transpose()
        for i in range(self.d + 1 - self.k, self.n):
            shares_n.append(shares[i - (self.d + 1 - self.k), 0])

        return shares_n

    def decode_shamir(self) -> MPolynomial:
        """
        Decode the polynomial encoding for a single secret value.
        """
        if self.k != 1:
            raise NotImplementedError(
                f"Shamir secret sharing decode only works for k=1, not {self.k}."
            )
        if len(self.support_points) != self.n:
            raise ValueError(
                f"PolyEnc requires {self.n} support points, but got {len(self.support_points)}."
            )
        encoding = self.get_encoded_shares()
        v_inv = generate_inverse_vandermonde(
            self.base_ring, list(self.support_points), self.n, (self.n, self.n)
        )
        sum = self.variable_ring.zero()
        for i in range(self.n):
            sum += v_inv[0, i] * encoding[i]
        return sum

    def encode_shamir(self, value: MPolynomial) -> Sequence[MPolynomial]:
        if self.k != 1:
            raise NotImplementedError(
                f"Shamir secret sharing encode only works for k=1, not {self.k}."
            )
        if len(self.support_points) != self.n:
            raise ValueError(
                f"PolyEnc requires {self.n} support points, but got {len(self.support_points)}."
            )
        if not isinstance(value, MPolynomial):
            raise TypeError(
                f"PolyEnc encode requires an MPolynomial, but got {type(value)}."
            )

        shares = [self.variable_ring.zero() for _ in range(self.n)]
        # encode the value in the first coefficient of a polynomial of degree d with random coefficients
        coeffs = [self.variable_ring.zero() for _ in range(self.d + 1)]
        supports = list(self.support_points)
        coeffs[0] = value
        self.randoms = set()
        # generate random coefficients in the polynomial ring
        for i in range(1, self.d + 1):
            name = f"R_{next(self.rc_count)}"
            coeffs[i] = self.variable_ring(name)
            self.randoms.add(coeffs[i])

        # evaluate polynomial at all public support points
        for i in range(self.n):
            sum = coeffs[0]
            for j in range(1, self.d + 1):
                sum += coeffs[j] * supports[i] ** j
            shares[i] = sum
        return shares

    def decode(self) -> list[MPolynomial]:
        """
        Decode the polynomial encoding for all secrets.
        """
        if self.k == 1:
            return [self.decode_shamir()]
        else:
            return self.decode_packed_secret_sharing()

    def encode(
        self, secret_vars: Sequence[MPolynomial]
    ) -> Sequence[MPolynomial]:
        """
        Generate a polynomial encoding for the given secret variables
        """
        if self.k == 1:
            return self.encode_shamir(secret_vars[0])
        else:
            return self.encode_packed_secret_sharing(secret_vars)

    def __name__(self) -> str:
        """
        Return the name of this PolyEnc.
        """
        return f"PolyEnc(d={self.d}, n={self.n}, k={self.k}, e={self.e}, field={self.field()})"

    def parameter_vars(self) -> Set[MPolynomial]:
        """
        Return the support points of this PolyEnc.
        """
        return set(list(self.support_points) + list(self.secret_support_points))

    def ps_random_vars(self) -> Set[MPolynomial]:
        """
        Return the random variables that were used in the process of computing the sharing of an actual secret variable.
        """
        return self.randoms

    def get_constraint_inequalities(self) -> Sequence[MPolynomial]:
        """
        Return a list of constraints used in Groebner basis checkes, i.e., a_i != 0 and a_i != a_j.
        """
        supports = self.base_ring.gens()
        constraints = []
        # shamir secret sharing require non-zero supports, packed secret sharing does not
        if self.k == 1:
            for a in supports:
                constraints.append(a)
        for ai, aj in combinations(supports, 2):
            constraints.append(ai - aj)

        return constraints


@dataclass
class IPEnc(Encoding):
    """
    Secret sharing through inner product masking (https://eprint.iacr.org/2017/1047.pdf),
    where a secret s is encoded s.t. s = 〈L,S〉.
    Constraints are that L only contains non-zero elements and S_2 to S_n are random variables.
    Such a sharing fulfills t = n-1 probing security and encodes only one secret.
    """

    base_ring: CommutativeRing  # MPolynomialRing over variable of L that form a FractionField that the variable_ring is constructed over
    variable_ring: CommutativeRing  # MPolynomialRing that all variables live in
    symbolic_shares: list[MPolynomial] = field(default_factory=list)
    L: list[MPolynomial] = field(default_factory=list)
    rc_count: count = field(default_factory=count)

    # internal flag to skip the __post_init__ encoding step
    _skip_encode: bool = field(init=False, default=False)

    def __post_init__(self):
        super().__post_init__()
        if self._skip_encode:
            # we were built from existing DualValue sharing,
            # skip all the re-encoding bits
            return
        if self.k != 1:
            raise ValueError(
                f"Inner product masking permits the use of one secret, but got k={self.k}."
            )

        secret = self.secrets[0]
        encoding = self.encode(secret)

        self.sharing = [
            mk_obsval(self.obsgraph, enc, sym)
            for enc, sym in zip(encoding, self.symbolic_shares)
        ]

    def copy(self, **overrides) -> Self:
        """
        Make a brand-new IPEnc that starts as a shallow clone of `self`,
        then replaces any attributes given in `overrides`.

        Example usages:
        ```
        # Clone the IPEnc, but change the shares and secrets:
            new = old.copy(
                sharing=new_sharing,
                secrets=new_secrets
            )
        ```
        """
        # 1) Allocate a blank IPEnc without running __post_init__:
        new_obj = self.__class__.__new__(self.__class__)
        # 2) Ensure __post_init__ is never called on this clone:
        new_obj._skip_encode = True

        # 3) Copy every attribute from self.__dict__ into new_obj:
        for attr_name, attr_val in self.__dict__.items():
            setattr(new_obj, attr_name, attr_val)

        # 4) Apply any overrides the user passed in:
        for key, val in overrides.items():
            if not hasattr(new_obj, key):
                raise AttributeError(
                    f"Cannot override '{key}': no such attribute in IPEnc"
                )
            setattr(new_obj, key, val)

        # 5) If the user replaced .sharing but did not supply .symbolic_shares,
        #    then recompute symbolic_shares from the new DualValue list:
        if "sharing" in overrides and "symbolic_shares" not in overrides:
            new_obj.symbolic_shares = [dv.ps_obs for dv in new_obj.sharing]

        return new_obj

    def encode(self, secret_vars: MPolynomial) -> Sequence[MPolynomial]:
        """
        Generate an inner product encoding of the specified secret.
        """
        S = [
            self.variable_ring(f"R_{next(self.rc_count)}")
            for _ in range(1, self.n)
        ]
        self.randoms = {r for r in S}
        L = self.L[1:]

        # calculate inner product the set the remaining share S_1 to the correct value
        sum = self.variable_ring.zero()
        for l, s in zip(L, S):
            sum += l * s
        S_1 = [secret_vars - sum]

        return S_1 + S

    def decode(self) -> Sequence[MPolynomial]:
        """
        Decode an IP sharing.
        """
        secret = self.variable_ring.zero()
        enc = self.get_encoded_shares()

        if len(enc) != len(self.L) != self.n:
            raise ValueError(
                f"Encoding, L and num shares {self.n} are not consistent:\n |Enc| = {len(enc)} \n |L| = {len(self.L)}\n"
            )

        for l, e in zip(self.L, enc):
            secret += l * e

        return [secret]  # return a list here for compatibility reasons

    def __name__(self) -> str:
        """
        Return the name of this IPEnc.
        """
        return f"IPEnc(d={self.d}, n={self.n}, field={self.field()})"

    def parameter_vars(self) -> Set[MPolynomial]:
        return set(self.L)

    def ps_random_vars(self) -> Set[MPolynomial]:
        """
        Return the random variables that were used in the process of computing the sharing of an actual secret variable.
        """
        return self.randoms

    def get_constraint_inequalities(self) -> Sequence[MPolynomial]:
        """
        Return a list of constraints used in Groebner basis checkes, i.e., L_i != 0.
        """
        L_vars = set(self.base_ring.gens())
        constraints = []
        for var in L_vars:
            constraints.append(var)

        return constraints


# TODO: add a function to provide a buffer and rc_counter to an encoding, to be able to reuse encodings instead.
def IP_setup(
    F: CommutativeRing, secrets: Sequence[str], n: int, max_randoms: int = 1000
) -> Tuple[
    Dict[str, IPEnc],
    count,  # random-counter
]:
    """
    Generate the vector L for a given field. This vector is used for all encodings and gadgets.
    We use the constructions from https://eprint.iacr.org/2017/1047.pdf and therefore consider the constraints:
        - L_1 is field element 1
        - L_2 to L_n are random non-zero variables (important for security and needs to be encoded into groebner constraints)
    L is not output and instead embedded into each encoding and can be accessed that way by gadgets.
    This function also generates `MPolynomialRings` that our variables live in and also outputs encodings for all specified secret variables.
    """

    # generate the necessary variables for the single layer MPolynomial ring over L, secrets, shares, and random vars (unfortunately need to pre alloc these here)
    secret_vars: List[str] = []
    symbolic_shares: List[str] = []
    for s in secrets:
        secret_vars += [f"{s}"]
        symbolic_shares += [f"{s.upper()}{i}" for i in range(n)]
    L_vars = [f"L_{i}" for i in range(1, n)]

    # 1) build rings
    base_ring, ring = gen_rings_for_gadgets(
        F, L_vars, secret_vars + symbolic_shares, max_randoms=max_randoms
    )

    # 2) build L vector for encodings and gadgets
    L = [
        base_ring(1)
    ]  # encodings from https://eprint.iacr.org/2017/1047.pdf always have first element set to 1
    for l in L_vars:  # noqa: E741
        L.append(base_ring(l))

    # 3) shared log & counter
    rc = count()
    obsgraph = ObservationGraph()

    # 4) generate encodings for all secrets
    encs: Dict[str, IPEnc] = {}
    for s in secrets:
        tmp_secrets = [ring(f"{s}")]
        tmp_shares = [ring(f"{s.upper()}{i}") for i in range(n)]
        encs[s] = IPEnc(
            d=n - 1,  # probing security parameter of the encoding
            e=0,  #  IP masking does not have a fault tolerance parameter
            n=n,  # num shares
            obsgraph=obsgraph,
            secrets=tmp_secrets,
            field=F,  # base field, e.g. F_2^8
            base_ring=base_ring,
            variable_ring=ring,
            symbolic_shares=tmp_shares,
            L=L,
            rc_count=rc,
        )

    return encs, rc


@dataclass
class AddEnc(Encoding):
    """
    Standard additive secret sharing, where a secret s is encoded s.t r_n = s - (∑ r_i) for i in [n-1].
    No additional constraints or parameters are imposed on this encoding.
    Such a sharing fulfills t = n-1 probing security and encodes only one secret.
    """

    # TODO: change structure to support Boolean and arithmetic masking
    base_ring: CommutativeRing
    variable_ring: CommutativeRing  # MPolynomialRing that all variables live in
    symbolic_shares: list[MPolynomial] = field(default_factory=list)
    rc_count: count = field(default_factory=count)

    # internal flag to skip the __post_init__ encoding step
    _skip_encode: bool = field(init=False, default=False)

    def __post_init__(self):
        super().__post_init__()
        if self._skip_encode:
            # we were built from existing DualValue sharing,
            # skip all the re-encoding bits
            return
        if self.k != 1:
            raise ValueError(
                f"Additive masking permits only one secret per encoding, but got k={self.k}."
            )

        secret = self.secrets[0]
        encoding = self.encode(secret)

        self.sharing = [
            mk_obsval(self.obsgraph, enc, sym)
            for enc, sym in zip(encoding, self.symbolic_shares)
        ]

    def copy(self, **overrides) -> Self:
        """
        Make a brand-new AdditiveEnc that starts as a shallow clone of `self`,
        then replaces any attributes given in `overrides`.

        Example usages:
        ```
        # Clone the AdditiveEnc, but change the shares and secrets:
            new = old.copy(
                sharing=new_sharing,
                secrets=new_secrets
            )
        ```
        """
        # 1) Allocate a blank AdditiveEnc without running __post_init__:
        new_obj = self.__class__.__new__(self.__class__)
        # 2) Ensure __post_init__ is never called on this clone:
        new_obj._skip_encode = True

        # 3) Copy every attribute from self.__dict__ into new_obj:
        for attr_name, attr_val in self.__dict__.items():
            setattr(new_obj, attr_name, attr_val)

        # 4) Apply any overrides the user passed in:
        for key, val in overrides.items():
            if not hasattr(new_obj, key):
                raise AttributeError(
                    f"Cannot override '{key}': no such attribute in AddEnc"
                )
            setattr(new_obj, key, val)

        # 5) If the user replaced .sharing but did not supply .symbolic_shares,
        #    then recompute symbolic_shares from the new DualValue list:
        if "sharing" in overrides and "symbolic_shares" not in overrides:
            new_obj.symbolic_shares = [dv.ps_obs for dv in new_obj.sharing]

        return new_obj

    def encode(self, secret_vars: MPolynomial) -> Sequence[MPolynomial]:
        """
        Generate an additive encoding of the specified secret.
        """
        R = [
            self.variable_ring(f"R_{next(self.rc_count)}")
            for _ in range(1, self.n)
        ]
        self.randoms = {r for r in R}

        # calculate sum for remaining share r_0
        sum = self.variable_ring.zero()
        for r in R:
            sum += r
        r_0 = [secret_vars - sum]

        return r_0 + R

    def decode(self) -> Sequence[MPolynomial]:
        """
        Decode an addtive encoding.
        """
        secret = self.variable_ring.zero()
        enc = self.get_encoded_shares()

        if len(enc) != self.n:
            raise ValueError(
                f"Encoding and num shares {self.n} are not consistent:\n |Enc| = {len(enc)} \n num shares = {self.n}\n"
            )

        for e in enc:
            secret += e

        return [secret]  # return a list here for compatibility reasons

    def __name__(self) -> str:
        """
        Return the name of this AdditiveEnc.
        """
        return f"AdditiveEnc(d={self.d}, n={self.n}, field={self.field()})"

    def parameter_vars(self) -> Set[MPolynomial]:
        return set()

    def ps_random_vars(self) -> Set[MPolynomial]:
        """
        Return the random variables that were used in the process of computing the sharing of an actual secret variable.
        """
        return self.randoms


# TODO: add a function to provide a buffer and rc_counter to an encoding, to be able to reuse encodings instead.
def AddEnc_setup(
    F: CommutativeRing, secrets: Sequence[str], n: int, max_randoms: int = 1000
) -> Tuple[
    Dict[str, AddEnc],
    count,  # random-counter
]:
    """
    This function generates `MPolynomialRings` that our variables live in and also outputs encodings for all specified secret variables.
    """

    # generate the necessary variables for the single layer MPolynomial ring over L, secrets, shares, and random vars (unfortunately need to pre alloc these here)
    secret_vars: List[str] = []
    symbolic_shares: List[str] = []
    for s in secrets:
        secret_vars += [f"{s}"]
        symbolic_shares += [f"{s.upper()}{i}" for i in range(n)]

    # 1) build rings
    base_ring, ring = gen_rings_for_gadgets(
        F, [], secret_vars + symbolic_shares, max_randoms=max_randoms
    )

    # 2) shared log & counter
    rc = count()
    obsgraph = ObservationGraph()

    # 3) generate encodings for all secrets
    encs: Dict[str, AddEnc] = {}
    for s in secrets:
        tmp_secrets = [ring(f"{s}")]
        tmp_shares = [ring(f"{s.upper()}{i}") for i in range(n)]
        encs[s] = AddEnc(
            d=n - 1,  # probing security parameter of the encoding
            e=0,  #  Additive masking does not have fault tolerance in its encoding
            n=n,  # num shares
            obsgraph=obsgraph,
            secrets=tmp_secrets,
            field=F,  # base field, e.g. F_2^8
            base_ring=base_ring,
            variable_ring=ring,
            symbolic_shares=tmp_shares,
            rc_count=rc,
        )

    return encs, rc


@dataclass
class GCMEnc_WCG22(Encoding):
    """
    Secret sharing through generalized code-based masking (https://tches.iacr.org/index.php/TCHES/article/view/9699/9230),
    with construtor matrix, aka. practical encoder, A as outline in section 3.1 of the above.
    No constraints are placed on the parameter variables of the matrix R with dimensions d x (n - d).
    GCM supports packing multiple secret values into one encoding.
    """

    base_ring: CommutativeRing  # MPolynomialRing over variables of H that form a FractionField that the variable_ring is constructed over
    variable_ring: CommutativeRing  # MPolynomialRing that all variables live in
    H_vars: list[MPolynomial]  # variables used to construct the matrix H
    T_vars: list[MPolynomial]  # variables for the d-privacy condition
    symbolic_shares: list[MPolynomial] = field(default_factory=list)
    rc_count: count = field(default_factory=count)

    A: Matrix = field(init=False, default_factory=Matrix)

    # internal flag to skip the __post_init__ encoding step
    _skip_encode: bool = field(init=False, default=False)

    def __post_init__(self):
        super().__post_init__()
        if self._skip_encode:
            # we were built from existing DualValue sharing,
            # skip all the re-encoding bits
            return

        para_set = set(self.H_vars)

        if any(not isinstance(para, MPolynomial) for para in para_set):
            raise ValueError(
                f"CodeBasedEnc requires polynomials as parameter variables but got {[(type(para), para) for para in self.H_vars]}"
            )
        if self.n < self.d + 1:
            raise ValueError(
                f"CodeBasedEnc requires n >= d + 1, but got n={self.n}, d={self.d}."
            )
        if len(para_set) != self.d * (self.n - self.d):
            raise ValueError(
                f"CodeBasedEnc requires {self.d * (self.n - self.d)} parameter vars but got {len(set(self.H_vars))}: {set(self.H_vars)}."
            )
        if len(self.secrets) != self.k:
            raise ValueError(
                f"CodeBasedEnc requires {self.k} secret variables but got  {len(self.secrets)}: {self.secrets}."
            )
        self.H = generate_H_GCM(
            self.base_ring, self.H_vars, self.n, self.k, self.d
        )
        I_k = matrix.identity(self.base_ring, self.k)
        O = matrix(self.base_ring, self.k, self.n - self.k, 0)
        self.G = matrix.block([[I_k, O]], subdivide=False)
        self.T = [
            matrix(self.base_ring, self.k, self.d, t) for t in self.T_vars
        ]
        self.A = generate_A_GCM(self.base_ring, self.H, self.n, self.k, self.d)
        assert self.A.nrows() == self.A.ncols() == self.n, (
            f"matrix A is not quadratic n x n, instead it is {self.A.nrows()} x {self.A.ncols()}"
        )
        # normal path: create fresh shares
        encoding = self.encode(self.secrets)

        self.sharing = [
            mk_obsval(self.obsgraph, enc, sym)
            for enc, sym in zip(encoding, self.symbolic_shares)
        ]

    def copy(self, **overrides) -> Self:
        """
        Make a brand-new GCM22Enc that starts as a shallow clone of `self`,
        then replaces any attributes given in `overrides`.

        Example usages:
        ```
        # Clone the GCM22Enc, but change the shares and secrets:
            new = old.copy(
                sharing=new_sharing,
                secrets=new_secrets
            )
        ```
        """
        # 1) Allocate a blank GCM22Enc without running __post_init__:
        new_obj = self.__class__.__new__(self.__class__)
        # 2) Ensure __post_init__ is never called on this clone:
        new_obj._skip_encode = True

        # 3) Copy every attribute from self.__dict__ into new_obj:
        for attr_name, attr_val in self.__dict__.items():
            setattr(new_obj, attr_name, attr_val)

        # 4) Apply any overrides the user passed in:
        for key, val in overrides.items():
            if not hasattr(new_obj, key):
                raise AttributeError(
                    f"Cannot override '{key}': no such attribute in GCM22Enc"
                )
            setattr(new_obj, key, val)

        # 5) If the user replaced .sharing but did not supply .symbolic_shares,
        #    then recompute symbolic_shares from the new DualValue list:
        if "sharing" in overrides and "symbolic_shares" not in overrides:
            new_obj.symbolic_shares = [dv.ps_obs for dv in new_obj.sharing]

        return new_obj

    def decode(self) -> list[MPolynomial]:
        """
        Decode the polynomial encoding for all secrets.
        """
        enc = matrix(1, self.n, self.get_encoded_shares())
        A_inv = self.A.inverse()
        dec = enc * A_inv
        secrets = dec[0, : self.k]

        return secrets.list()

    def encode(
        self, secret_vars: Sequence[MPolynomial]
    ) -> Sequence[MPolynomial]:
        """
        Generate a code-based encoding for the given secret variables:
        [z]_n = [[x]_k | [r]_d] * A
        as described in https://tches.iacr.org/index.php/TCHES/article/view/8547/8112.
        """
        rands = []
        for _ in range(self.d):
            name = f"R_{next(self.rc_count)}"
            r = self.variable_ring(name)
            rands.append(r)
        self.randoms = set(rands)

        enc = matrix(1, self.k + self.d, list(secret_vars) + rands) * self.A
        return list(enc.list())

    def __name__(self) -> str:
        """
        Return the name of this GCM22Enc.
        """
        return f"GCM22Enc(d={self.d}, n={self.n}, k={self.k}, e={self.e}, field={self.field()})"

    def parameter_vars(self) -> Set[MPolynomial]:
        """
        Return the support points of this GCM22Enc.
        """
        return set(self.H_vars)

    def ps_random_vars(self) -> Set[MPolynomial]:
        """
        Return the random variables that were used in the process of computing the sharing of an actual secret variable.
        """
        return self.randoms

    def get_constraint_equalities(self) -> Sequence[MPolynomial]:
        """
        The choice of the practical encoder A in https://tches.iacr.org/index.php/TCHES/article/view/9699/9230 guarantees full rank and therefore requires no constraints.
        """
        return generate_d_private_encoder_constraints(
            self.base_ring, self.T, self.G, self.H, self.d
        )


def GCM_WCG22_setup(
    d: int,
    e: int,
    n: int,
    k: int,
    F: CommutativeRing,
    prefixes: Sequence[str],
    max_randoms: int = 1000,  # interestingly, blowing up the ring with many unused variables seems to have no significant effect on performance
) -> Tuple[
    Dict[str, GCMEnc_WCG22],
    count,  # random-counter
]:
    """
    Build one GCMEnc per name in `prefixes`.
    """
    # symbolic names
    H_vars = [f"h_{i}" for i in range(d * (n - d))]

    # per-prefix variable names
    secret_vars: List[str] = []
    symbolic_shares: List[str] = []
    for p in prefixes:
        secret_vars += [f"{p}{i}" for i in range(k)]
        symbolic_shares += [f"{p.upper()}{i}" for i in range(n)]

    # these variables are used for constraint building to encode the notion of a d-private encoder
    T_vars = []
    T_flat = []
    for i in range(comb(n, d)):
        temp = [f"t{i}_{j}_constraint_var" for j in range(k * d)]
        T_vars.append(temp)
        T_flat.extend(temp)

    # 1) build rings
    base_ring, ring = gen_rings_for_gadgets(
        F,
        H_vars + T_flat,
        secret_vars + symbolic_shares,
        max_randoms=max_randoms,
    )

    # 2) coerce support points into the fraction-field
    H_vars = [base_ring(a) for a in H_vars]
    T_vars = [[base_ring(t) for t in T] for T in T_vars]

    # 3) shared log & counter
    rc = count()
    obsgraph = ObservationGraph()

    # 4) make each GCM22Enc
    encs: Dict[str, GCMEnc_WCG22] = {}
    for p in prefixes:
        f_secrets = [ring(f"{p}{i}") for i in range(k)]
        f_sym_shares = [ring(f"{p.upper()}{i}") for i in range(n)]
        encs[p] = GCMEnc_WCG22(
            d=d,
            e=e,
            n=n,
            obsgraph=obsgraph,
            secrets=f_secrets,
            field=F,
            base_ring=base_ring,
            variable_ring=ring,
            H_vars=H_vars,
            T_vars=T_vars,
            symbolic_shares=f_sym_shares,
            rc_count=rc,
        )

    return encs, rc


@dataclass
class GCMEncWMCS20(Encoding):
    """
    Secret sharing through generalized code-based masking (https://tches.iacr.org/index.php/TCHES/article/view/8547/8112).
    The matrix A = [G;H] is required to be full rank.
    GCM supports packing multiple secret values into one encoding.
    """

    base_ring: CommutativeRing  # MPolynomialRing over variable of H that form a FractionField that the variable_ring is constructed over
    variable_ring: CommutativeRing  # MPolynomialRing that all variables live in
    G_vars: list[MPolynomial]  # variables used to construct the matrix G
    H_vars: list[MPolynomial]  # variables used to construct the matrix H
    A_row_rank_vars: list[
        MPolynomial
    ]  # variables for a full row rank condition encoding
    T_vars: list[MPolynomial]  # variables for the d-privacy condition
    symbolic_shares: list[MPolynomial] = field(default_factory=list)
    rc_count: count = field(default_factory=count)

    A: Matrix = field(init=False, default_factory=Matrix)

    # internal flag to skip the __post_init__ encoding step
    _skip_encode: bool = field(init=False, default=False)

    def __post_init__(self):
        super().__post_init__()
        if self._skip_encode:
            # we were built from existing DualValue sharing,
            # skip all the re-encoding bits
            return
        para_set = set(self.G_vars + self.H_vars)

        if any(not isinstance(para, MPolynomial) for para in para_set):
            raise ValueError(
                f"CodeBasedEnc requires polynomials as parameter variables but got {[(type(para), para) for para in self.H_vars]}"
            )
        if self.n < self.d + 1:
            raise ValueError(
                f"CodeBasedEnc requires n >= d + 1, but got n={self.n}, d={self.d}."
            )
        if len(para_set) != self.n * self.n:
            raise ValueError(
                f"CodeBasedEnc requires {self.n * self.n} parameter vars but got {len(set(self.H_vars))}: {set(self.H_vars)}."
            )
        if len(self.secrets) != self.k:
            raise ValueError(
                f"CodeBasedEnc requires {self.k} secret variables but got  {len(self.secrets)}: {self.secrets}."
            )
        self.H = generate_H_GCM_WMCS20(
            self.base_ring, self.H_vars, self.n, self.d
        )
        self.G = generate_G_GCM_WMCS20(
            self.base_ring, self.G_vars, self.n, self.k
        )
        self.T = [
            matrix(self.base_ring, self.k, self.d, t) for t in self.T_vars
        ]
        self.A = generate_A_GCM_WMCS20(self.base_ring, self.G, self.H)
        # normal path: create fresh shares
        encoding = self.encode(self.secrets)

        self.sharing = [
            mk_obsval(self.obsgraph, enc, sym)
            for enc, sym in zip(encoding, self.symbolic_shares)
        ]

    def copy(self, **overrides) -> Self:
        """
        Make a brand-new GCM20Enc that starts as a shallow clone of `self`,
        then replaces any attributes given in `overrides`.

        Example usages:
        ```
        # Clone the GCM20Enc, but change the shares and secrets:
            new = old.copy(
                sharing=new_sharing,
                secrets=new_secrets
            )
        ```
        """
        # 1) Allocate a blank GCM20Enc without running __post_init__:
        new_obj = self.__class__.__new__(self.__class__)
        # 2) Ensure __post_init__ is never called on this clone:
        new_obj._skip_encode = True

        # 3) Copy every attribute from self.__dict__ into new_obj:
        for attr_name, attr_val in self.__dict__.items():
            setattr(new_obj, attr_name, attr_val)

        # 4) Apply any overrides the user passed in:
        for key, val in overrides.items():
            if not hasattr(new_obj, key):
                raise AttributeError(
                    f"Cannot override '{key}': no such attribute in GCM20Enc"
                )
            setattr(new_obj, key, val)

        # 5) If the user replaced .sharing but did not supply .symbolic_shares,
        #    then recompute symbolic_shares from the new DualValue list:
        if "sharing" in overrides and "symbolic_shares" not in overrides:
            new_obj.symbolic_shares = [dv.ps_obs for dv in new_obj.sharing]

        return new_obj

    def decode(self) -> list[MPolynomial]:
        """
        Decode the GCM20 encoding for all secrets.
        """
        enc = matrix(1, self.n, self.get_encoded_shares())
        A_inv = self.A.inverse()
        dec = enc * A_inv
        secrets = dec[0, : self.k]

        return secrets.list()

    def encode(
        self, secret_vars: Sequence[MPolynomial]
    ) -> Sequence[MPolynomial]:
        """
        Generate a code-based encoding for the given secret variables:
        [z]_n = [[x]_k | [r]_d] * A
        as described in https://tches.iacr.org/index.php/TCHES/article/view/8547/8112.
        """
        rands = []
        for _ in range(self.d):
            name = f"R_{next(self.rc_count)}"
            r = self.variable_ring(name)
            rands.append(r)
        self.randoms = set(rands)

        enc = matrix(1, self.k + self.d, list(secret_vars) + rands) * self.A
        return list(enc.list())

    def __name__(self) -> str:
        """
        Return the name of this GCM20Enc.
        """
        return f"GCM20Enc(d={self.d}, n={self.n}, k={self.k}, e={self.e}, field={self.field()})"

    def parameter_vars(self) -> Set[MPolynomial]:
        """
        Return the support points of this GCM20Enc.
        """
        return set(self.G_vars + self.H_vars)

    def ps_random_vars(self) -> Set[MPolynomial]:
        """
        Return the random variables that were used in the process of computing the sharing of an actual secret variable.
        """
        return self.randoms

    def get_constraint_equalities(self) -> Sequence[MPolynomial]:
        """
        The encoder matrix is required to fulfill d-privacy https://tches.iacr.org/index.php/TCHES/article/view/8547/8112.
        """
        d_privacy_constraints = generate_d_private_encoder_constraints(
            self.base_ring, self.T, self.G, self.H, self.d
        )
        A_full_rank_constraints = generate_full_row_rank_constraints(
            self.base_ring, self.A, self.A_row_rank_vars
        )

        return d_privacy_constraints + A_full_rank_constraints


def GCM_WMCS20_setup(
    d: int,
    e: int,
    n: int,
    k: int,
    F: CommutativeRing,
    prefixes: Sequence[str],
    max_randoms: int = 1000,  # interestingly, blowing up the ring with many unused variables seems to have no significant effect on performance
) -> Tuple[
    Dict[str, GCMEncWMCS20],
    count,  # random-counter
]:
    """
    Build one GCMEnc per name in `prefixes`.
    """

    # symbolic names
    G_vars = [f"g_{i}" for i in range(k * n)]
    H_vars = [f"h_{i}" for i in range(d * n)]
    A_row_rank_vars = [f"a_{i}_row_rank_var" for i in range((k + d) * n)]

    # per-prefix variable names
    secret_vars: List[str] = []
    symbolic_shares: List[str] = []
    for p in prefixes:
        secret_vars += [f"{p}{i}" for i in range(k)]
        symbolic_shares += [f"{p.upper()}{i}" for i in range(n)]

    # these variables are used for constraint building to encode the notion of a d-private encoder
    T_vars = []
    T_flat = []
    for i in range(comb(n, d)):
        temp = [f"t{i}_{j}_constraint_var" for j in range(k * d)]
        T_vars.append(temp)
        T_flat.extend(temp)

    vars1 = T_flat + G_vars
    vars2 = A_row_rank_vars + H_vars
    # to = TermOrder("degrevlex", len(vars1)) + TermOrder("lex", len(vars2))
    to = "degrevlex"
    # 1) build rings
    base_ring, ring = gen_rings_for_gadgets(
        F,
        # G_vars + H_vars + T_flat + A_row_rank_vars,
        vars1 + vars2,
        secret_vars + symbolic_shares,
        max_randoms=max_randoms,
        termorder=to,
    )

    # 2) coerce support points into the fraction-field
    G_vars = [base_ring(g) for g in G_vars]
    H_vars = [base_ring(h) for h in H_vars]
    A_row_rank_vars = [base_ring(a) for a in A_row_rank_vars]
    T_vars = [[base_ring(t) for t in T] for T in T_vars]

    # 3) shared log & counter
    rc = count()
    obsgraph = ObservationGraph()

    # 4) make each GCM20Enc
    encs: Dict[str, GCMEncWMCS20] = {}
    for p in prefixes:
        f_secrets = [ring(f"{p}{i}") for i in range(k)]
        f_sym_shares = [ring(f"{p.upper()}{i}") for i in range(n)]
        encs[p] = GCMEncWMCS20(
            d=d,
            e=e,
            n=n,
            obsgraph=obsgraph,
            secrets=f_secrets,
            field=F,
            base_ring=base_ring,
            variable_ring=ring,
            G_vars=G_vars,
            H_vars=H_vars,
            A_row_rank_vars=A_row_rank_vars,
            T_vars=T_vars,
            symbolic_shares=f_sym_shares,
            rc_count=rc,
        )

    return encs, rc
