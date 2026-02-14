# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from ip_masking_gadgets import IPAESSbox
from polymasking_gadgets import PolyAESSbox
from GCM_WMCS20_gadgets import GCM20AESSbox
from GCM_WCG22_gadgets import GCM22AESSbox
from sage.all import GF
from sage.rings.ring import CommutativeRing


def generate_gadgets(d: int, F: CommutativeRing):
    print(f"\n=== Generating masked Sbox gadgets with d={d} ===")

    if d <= 2:
        IP_sbox = IPAESSbox.with_defaults(d, 1, 0, F)
        IP_sbox.serialize(d)

        GCM22_sbox = GCM22AESSbox.with_defaults(d, 1, 0, F)
        GCM22_sbox.serialize(d)

    if d == 1:
        Poly_sbox = PolyAESSbox.with_defaults(d, 1, 0, F)
        Poly_sbox.serialize(d)

        GCM20_sbox = GCM20AESSbox.with_defaults(d, 1, 0, F)
        GCM20_sbox.serialize(d)


def main():
    fields = [GF(2**8)]
    min_d, max_d = 1, 2
    for d in range(min_d, max_d + 1):
        for F in fields:
            generate_gadgets(d, F)


if __name__ == "__main__":
    main()
