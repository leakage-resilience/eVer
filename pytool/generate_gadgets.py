# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
import generate_GCM_gadgets
import generate_ip_masking_gadgets
import generate_isw_gadgets
import generate_polymasking_gadgets
import generate_sbox_gadgets
from concurrent.futures import ProcessPoolExecutor, as_completed


def main():
    funcs = [
        generate_polymasking_gadgets.main,
        generate_GCM_gadgets.main,
        generate_isw_gadgets.main,
        generate_ip_masking_gadgets.main,
        generate_sbox_gadgets.main,
    ]

    with ProcessPoolExecutor(max_workers=len(funcs)) as ex:
        futs = {ex.submit(f): f.__module__ for f in funcs}
        for fut in as_completed(futs):
            name = futs[fut]
            fut.result()
            print(f"{name} finished")


if __name__ == "__main__":
    main()
