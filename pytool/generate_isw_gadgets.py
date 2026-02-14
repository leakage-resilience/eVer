# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from encoding import AddEnc_setup
from isw_gadgets import ISWMult, ISWRefresh

from sage.all import GF
from sage.rings.ring import CommutativeRing


def generate_gadgets(d: int, F: CommutativeRing):
    print(f"\n=== Generating ISW masking gadgets with d={d}, n={d + 1} ===")

    ISW_mul = ISWMult.with_defaults(d, 1, 0, F)
    ISW_mul.serialize(d)

    ISW_ref = ISWRefresh.with_defaults(d, 1, 0, F)
    ISW_ref.serialize(d)


def main():
    fields = [GF(2**8)]
    secrets = ["x"]

    min_d, max_d = 1, 6
    for d in range(min_d, max_d + 1):
        for F in fields:
            n = d + 1
            encodings, _ = AddEnc_setup(F, secrets, n, 200)
            for enc in encodings:
                assert encodings[enc].decode() == encodings[enc].secrets, (
                    f"decoding of an additive encoding did not result in the secret value for encoding {encodings[enc]}"
                )
            generate_gadgets(d, F)


if __name__ == "__main__":
    main()
