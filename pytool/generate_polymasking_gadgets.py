# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
import contextlib
import logging
import sys
import time
from multiprocessing import cpu_count
from typing import Type

from concurrent.futures import ProcessPoolExecutor, as_completed
from sage.all import GF
from sage.rings.ring import CommutativeRing
from tqdm import tqdm
from tqdm.contrib import DummyTqdmFile

from gadget import Gadget
from polymasking_gadgets import (
    BgwMultGadget,
    SWPolyAddGadget,
    SWPolySubGadget,
    SWPolyMulGadget,
    FOWZ25Zenc,
    FOWZ25SZenc,
    FOWZ25Refresh,
    OptZenc,
    OptSZenc,
    OptRefresh,
    RefreshSFRES18,
    LaolaMultGadget,
    SWComp,
)


def generate_gadget(
    g: Type[Gadget], d: int, e: int, k: int, F: CommutativeRing
):
    """
    Generate gadgets for polynomial masking with given parameters,
    but serialize each gadget in parallel.
    """
    logging.info(
        f"\n=== Generating gadget {g.__name__} with d={d}, e={e}, k={k} ==="
    )
    start = time.perf_counter()

    gadget = None

    try:
        gadget = g.from_file(d, k, e, F)
    except Exception:
        pass
    # successfully loaded?
    if gadget:
        logging.info(
            f"Successfully loaded gadget {g.__name__} from file, skipping generation."
        )
        return f"Completed {g.__name__} for d={d}, e={e}, k={k}"

    gadget = g.with_defaults(d, k, e, F)

    gadget.serialize(d, k, e)

    logging.info(
        f"Generation of {g.__name__} took: {time.perf_counter() - start:.3f}s"
    )
    return f"Completed {g.__name__} for d={d}, e={e}, k={k}"


# taken from: https://github.com/tqdm/tqdm/blob/master/examples/redirect_print.py
@contextlib.contextmanager
def redirect_stdout():
    orig_out_err = sys.stdout, sys.stderr
    try:
        sys.stdout, sys.stderr = map(DummyTqdmFile, orig_out_err)
        yield orig_out_err[0]
    # Relay exceptions
    except Exception as exc:
        raise exc
    # Always restore sys.stdout/err if necessary
    finally:
        sys.stdout, sys.stderr = orig_out_err


def main():
    F = GF(2**8)
    min_k, max_k = 1, 3
    min_e, max_e = 0, 2
    min_d, max_d = 1, 6

    gadgets = [
        SWPolyAddGadget,
        SWPolySubGadget,
        SWPolyMulGadget,
        SWComp,
        FOWZ25Zenc,
        FOWZ25SZenc,
        FOWZ25Refresh,
        OptZenc,
        OptSZenc,
        OptRefresh,
        RefreshSFRES18,
        BgwMultGadget,
        LaolaMultGadget,
    ]

    # Generate all valid parameter combinations
    tasks = []

    def exclude_laola(d, e):
        return (
            d > 4
            or e > 3
            or (d == 3 and e > 2)
            or (d == 4 and e > 0)
            or (k == 3 and e > 0)
        )

    def exclude_bgw(d, e):
        return d > 3 or e > 3 or (k == 3 and e > 0)

    def exclude_task(g, d, e):
        return (g == LaolaMultGadget and exclude_laola(d, e)) or (
            g == BgwMultGadget and exclude_bgw(d, e)
        )

    for g in gadgets:
        for k in range(min_k, max_k + 1):
            for d in range(min_d, max_d + 1):  # d > 0 and k <= d
                for e in range(min_e, max_e + 1):  # e >= 0
                    if k > d:
                        logging.info(f"Skipping k={k}, d={d} (k must be <= d)")
                        continue
                    if exclude_task(g, d, e):
                        logging.info(
                            f"Skipping {g.__name__} for d={d}, e={e}, k={k} (filtered out)"
                        )
                        continue
                    # generate_gadget(g, d, e, k, F) # single execution for profiling and debugging purposes
                    tasks.append((g, d, e, k, F))

    logging.info(
        f"Starting parallel execution of {len(tasks)} parameter combinations"
    )
    total_start = time.perf_counter()

    # tqdm needs the original stdout
    with tqdm(
        total=len(tasks),
        desc="Generating gadgets",
        unit="gadgets",
        file=sys.__stdout__,
    ) as pbar:
        # Run tasks in parallel
        with ProcessPoolExecutor(
            max_workers=max(min(64, cpu_count()), min(64, len(tasks)))
        ) as executor:
            # Submit all tasks
            futures = {
                executor.submit(generate_gadget, g, d, e, k, F): (g, d, e, k)
                for g, d, e, k, F in reversed(tasks)
            }

            # Process results as they complete
            for future in as_completed(futures):
                pbar.update(1)
                pbar.refresh()
                params = futures[future]
                try:
                    logging.info(f"✓ {future.result()}")
                except Exception as exc:
                    logging.warning(
                        f"× Error with g={params[0].__name__}, d={params[1]}, e={params[2]}, k={params[3]}: {exc}"
                    )

    logging.info(
        f"Total execution time for all parameter combinations: {time.perf_counter() - total_start:.3f}s"
    )


if __name__ == "__main__":
    # Redirect stdout to tqdm.write()
    with redirect_stdout():
        # we first need to redirect stdout and then setup the logger here to make sure tqdm stays on the bottom and outputs don't interfere with it.
        logging.basicConfig(
            level=logging.INFO,
            format="%(asctime)s - %(levelname)s - %(message)s",
            handlers=[
                logging.FileHandler("generate_polymasking_gadgets.log"),
                logging.StreamHandler(sys.stdout),
            ],
        )
        main()
