# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from encoding import GCM_WMCS20_setup, GCM_WCG22_setup
from GCM_WCG22_gadgets import (
    GCM_Refresh_WCG22,
    GCMMult_WCG22,
    GCM_L_WCG22,
)
from GCM_WMCS20_gadgets import GCM_Refresh_WMCS20, GCMMult_WMCS20, GCM_L_WMCS20
from sage.all import GF
from sage.rings.ring import CommutativeRing


def generate_gadgets(d: int, k: int, F: CommutativeRing):
    print(
        f"\n=== Generating GCM masking gadgets with d={d}, k={k}, n={d + k} ==="
    )

    if d <= 5:
        WCG22_mul = GCMMult_WCG22.with_defaults(d, k, 0, F)
        WCG22_mul.serialize(d, k)

        WCG22_ref = GCM_Refresh_WCG22.with_defaults(d, k, 0, F)
        WCG22_ref.serialize(d, k)

        if F.characteristic() == 2:
            WCG22_l = GCM_L_WCG22.with_defaults(d, k, 0, F)
            WCG22_l.serialize(d, k)

    if d <= 3:
        WMCS20_mul = GCMMult_WMCS20.with_defaults(d, k, 0, F)
        WMCS20_mul.serialize(d, k)

        WMCS20_ref = GCM_Refresh_WMCS20.with_defaults(d, k, 0, F)
        WMCS20_ref.serialize(d, k)

        if F.characteristic() == 2:
            WMCS20_l = GCM_L_WMCS20.with_defaults(d, k, 0, F)
            WMCS20_l.serialize(d, k)


def main():
    fields = [GF(2**8)]
    secrets = ["x"]

    min_d, max_d = 4, 5
    min_k, max_k = 1, 1
    for d in range(min_d, max_d + 1):
        for k in range(min_k, max_k + 1):
            for F in fields:
                n = d + k
                encodings, _ = GCM_WMCS20_setup(d, 0, n, k, F, secrets, 200)
                for enc in encodings:
                    assert encodings[enc].decode() == encodings[enc].secrets, (
                        f"decoding of a GCM_WMCS20 encoding did not result in the secret value for encoding {encodings[enc]}"
                    )
                encodings, _ = GCM_WCG22_setup(d, 0, n, k, F, secrets, 200)
                for enc in encodings:
                    assert encodings[enc].decode() == encodings[enc].secrets, (
                        f"decoding of a GCM_WCG22 encoding did not result in the secret value for encoding {encodings[enc]}"
                    )
                generate_gadgets(d, k, F)


if __name__ == "__main__":
    main()
