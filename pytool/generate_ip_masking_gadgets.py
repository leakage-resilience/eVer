# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from encoding import IP_setup
from ip_masking_gadgets import (
    IPAddGadget,
    IPRefreshGadget,
    IPMultGadget,
    SecIPRefreshGadget,
)
from sage.all import GF
from sage.rings.ring import CommutativeRing


def generate_gadgets(d: int, F: CommutativeRing):
    print(f"\n=== Generating IP masking gadgets with d={d}, n={d + 1} ===")

    ip_add = IPAddGadget.with_defaults(d, 1, 0, F)
    ip_add.serialize(d)

    ip_mult = IPMultGadget.with_defaults(d, 1, 0, F)
    ip_mult.serialize(d)

    ip_refresh = IPRefreshGadget.with_defaults(d, 1, 0, F)
    ip_refresh.serialize(d)

    sec_ip_refresh = SecIPRefreshGadget.with_defaults(d, 1, 0, F)
    sec_ip_refresh.serialize(d)


def main():
    F = GF(2**8)
    secrets = ["x", "y"]

    for d in range(1, 7):
        n = d + 1
        encodings, _ = IP_setup(F, secrets, n, 100)
        for enc in encodings:
            assert encodings[enc].decode() == encodings[enc].secrets, (
                f"decoding of an encoding did not result in the secret value for encoding {encodings[enc]}"
            )
        generate_gadgets(d, F)


if __name__ == "__main__":
    main()
