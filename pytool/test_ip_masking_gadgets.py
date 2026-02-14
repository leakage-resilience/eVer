# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
import sys
import time
from contextlib import contextmanager
from ip_masking_gadgets import (
    IPAddGadget,
    IPMultGadget,
    IPRefreshGadget,
    SecIPRefreshGadget,
)
from sage.rings.ring import CommutativeRing
from sage.all import GF


def verify_gadgets_correctness(F: CommutativeRing, d: int, log: bool = False):
    """
    Run functional correctness and security checks for inner product masking gadgets.
    """
    print(
        f"\n=== Running functional correctness checks with d={d}, n={d + 1} ==="
    )
    start = time.perf_counter()

    # Define expected results for each gadget
    expected_results = {
        "IPAddGadget": True,
        "IPRefreshGadget": True,
        "IPMultGadget": True,
        "SecIPRefreshGadget": True,
    }

    results = {}

    # Test each gadget and track results
    try:
        ip_add = IPAddGadget.from_file(d, field=F)
        results["IPAddGadget"] = ip_add.functional_correctness()
    except Exception as exc:
        results["IPAddGadget"] = f"ERROR: {exc}"

    try:
        ip_refresh = IPRefreshGadget.from_file(d, field=F)
        results["IPRefreshGadget"] = ip_refresh.functional_correctness()
    except Exception as exc:
        results["IPRefreshGadget"] = f"ERROR: {exc}"

    try:
        ip_mult = IPMultGadget.from_file(d, field=F)
        results["IPMultGadget"] = ip_mult.functional_correctness()
    except Exception as exc:
        results["IPMultGadget"] = f"ERROR: {exc}"

    try:
        sec_ip_refresh = SecIPRefreshGadget.from_file(d, field=F)
        results["SecIPRefreshGadget"] = sec_ip_refresh.functional_correctness()
    except Exception as exc:
        results["SecIPRefreshGadget"] = f"ERROR: {exc}"

    # Print result comparison
    print("\n=== Functional Test Results Summary ===")
    print(f"Parameters: d={d}, n={d + 1}")
    print(f"{'Gadget':<20} {'Expected':<10} {'Actual':<10} {'Match?':<10}")
    print("-" * 50)

    all_match = True
    for gadget, expected in expected_results.items():
        if gadget in results:
            actual = results[gadget]
            if isinstance(actual, bool):
                matches = actual == expected
                if not matches:
                    all_match = False
                print(
                    f"{gadget:<20} {str(expected):<10} {str(actual):<10} {'✓' if matches else '✗'}"
                )
            else:
                print(f"{gadget:<20} {str(expected):<10} {actual:<10} {'?'}")
                all_match = False

    print("\nOverall test result: " + ("PASS" if all_match else "FAIL"))

    elapsed = time.perf_counter() - start
    print(
        f"Execution time for functional correctness checks: {elapsed:.3f} seconds"
    )
    return results


def verify_gadgets_PS(
    F: CommutativeRing,
    d: int,
    log: bool = False,
    num_processes: int = 1,
    continue_on_fail: bool = False,
):
    print(
        f"\n=== Running t-PS security checks for IP masking gadgets with d={d}, n={d + 1} ==="
    )
    start = time.perf_counter()

    # Define expected results for each gadget
    expected_results = {
        "IPAddGadget": True,
        "IPRefreshGadget": True,
        "IPMultGadget": True,
        "SecIPRefreshGadget": True,
    }

    results = {}

    # Test each gadget and track results
    try:
        ip_add = IPAddGadget.from_file(d, field=F)
        results["IPAddGadget"] = ip_add.verify_t_PS(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPAddGadget"] = f"ERROR: {exc}"

    try:
        ip_refresh = IPRefreshGadget.from_file(d, field=F)
        results["IPRefreshGadget"] = ip_refresh.verify_t_PS(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPRefreshGadget"] = f"ERROR: {exc}"

    try:
        ip_mult = IPMultGadget.from_file(d, field=F)
        results["IPMultGadget"] = ip_mult.verify_t_PS(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPMultGadget"] = f"ERROR: {exc}"

    try:
        sec_ip_refresh = SecIPRefreshGadget.from_file(d, field=F)
        results["SecIPRefreshGadget"] = sec_ip_refresh.verify_t_PS(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["SecIPRefreshGadget"] = f"ERROR: {exc}"

    # Print result comparison
    print("\n=== t-PS Verification Results Summary ===")
    print(f"Parameters: d={d}, n={d + 1}")
    print(f"{'Gadget':<20} {'Expected':<10} {'Actual':<10} {'Match?':<10}")
    print("-" * 50)

    all_match = True
    for gadget, expected in expected_results.items():
        if gadget in results:
            actual = results[gadget]
            if isinstance(actual, bool):
                matches = actual == expected
                if not matches:
                    all_match = False
                print(
                    f"{gadget:<20} {str(expected):<10} {str(actual):<10} {'✓' if matches else '✗'}"
                )
            else:
                print(f"{gadget:<20} {str(expected):<10} {actual:<10} {'?'}")
                all_match = False

    print("\nOverall test result: " + ("PASS" if all_match else "FAIL"))

    elapsed = time.perf_counter() - start
    print(f"Execution time for t={d}-PS checks: {elapsed:.3f} seconds")
    return results


def verify_gadgets_NI(
    F: CommutativeRing,
    d: int,
    log: bool = False,
    num_processes: int = 1,
    continue_on_fail: bool = False,
):
    print(
        f"\n=== Running t-NI security checks for IP masking gadgets with d={d}, n={d + 1} ==="
    )
    start = time.perf_counter()

    # Define expected results for each gadget
    expected_results = {
        "IPAddGadget": True,
        "IPRefreshGadget": True,
        "IPMultGadget": True,
        "SecIPRefreshGadget": True,
    }

    results = {}

    # Test each gadget and track results
    try:
        ip_add = IPAddGadget.from_file(d, field=F)
        results["IPAddGadget"] = ip_add.verify_t_NI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPAddGadget"] = f"ERROR: {exc}"

    try:
        ip_refresh = IPRefreshGadget.from_file(d, field=F)
        results["IPRefreshGadget"] = ip_refresh.verify_t_NI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPRefreshGadget"] = f"ERROR: {exc}"

    try:
        ip_mult = IPMultGadget.from_file(d, field=F)
        results["IPMultGadget"] = ip_mult.verify_t_NI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPMultGadget"] = f"ERROR: {exc}"

    try:
        sec_ip_refresh = SecIPRefreshGadget.from_file(d, field=F)
        results["SecIPRefreshGadget"] = sec_ip_refresh.verify_t_NI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["SecIPRefreshGadget"] = f"ERROR: {exc}"

    # Print result comparison
    print("\n=== t-NI Verification Results Summary ===")
    print(f"Parameters: d={d}, n={d + 1}")
    print(f"{'Gadget':<20} {'Expected':<10} {'Actual':<10} {'Match?':<10}")
    print("-" * 50)

    all_match = True
    for gadget, expected in expected_results.items():
        if gadget in results:
            actual = results[gadget]
            if isinstance(actual, bool):
                matches = actual == expected
                if not matches:
                    all_match = False
                print(
                    f"{gadget:<20} {str(expected):<10} {str(actual):<10} {'✓' if matches else '✗'}"
                )
            else:
                print(f"{gadget:<20} {str(expected):<10} {actual:<10} {'?'}")
                all_match = False

    print("\nOverall test result: " + ("PASS" if all_match else "FAIL"))

    elapsed = time.perf_counter() - start
    print(f"Execution time for t={d}-NI checks: {elapsed:.3f} seconds")
    return results


def verify_gadgets_SNI(
    F: CommutativeRing,
    d: int,
    log: bool = False,
    num_processes: int = 1,
    continue_on_fail: bool = False,
):
    print(
        f"\n=== Running t-NI security checks for IP masking gadgets with d={d}, n={d + 1} ==="
    )
    start = time.perf_counter()

    # Define expected results for each gadget
    expected_results = {
        "IPAddGadget": False,
        "IPRefreshGadget": False,
        "IPMultGadget": True,
        "SecIPRefreshGadget": True,
    }

    results = {}

    # Test each gadget and track results
    try:
        ip_add = IPAddGadget.from_file(d, field=F)
        results["IPAddGadget"] = ip_add.verify_t_SNI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPAddGadget"] = f"ERROR: {exc}"

    try:
        ip_refresh = IPRefreshGadget.from_file(d, field=F)
        results["IPRefreshGadget"] = ip_refresh.verify_t_SNI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPRefreshGadget"] = f"ERROR: {exc}"

    try:
        ip_mult = IPMultGadget.from_file(d, field=F)
        results["IPMultGadget"] = ip_mult.verify_t_SNI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["IPMultGadget"] = f"ERROR: {exc}"

    try:
        sec_ip_refresh = SecIPRefreshGadget.from_file(d, field=F)
        results["SecIPRefreshGadget"] = sec_ip_refresh.verify_t_SNI(
            t=d,
            num_worker=num_processes,
            log=log,
            continue_on_fail=continue_on_fail,
        )
    except Exception as exc:
        results["SecIPRefreshGadget"] = f"ERROR: {exc}"

    # Print result comparison
    print("\n=== t-SNI Verification Results Summary ===")
    print(f"Parameters: d={d}, n={d + 1}")
    print(f"{'Gadget':<20} {'Expected':<10} {'Actual':<10} {'Match?':<10}")
    print("-" * 50)

    all_match = True
    for gadget, expected in expected_results.items():
        if gadget in results:
            actual = results[gadget]
            if isinstance(actual, bool):
                matches = actual == expected
                if not matches:
                    all_match = False
                print(
                    f"{gadget:<20} {str(expected):<10} {str(actual):<10} {'✓' if matches else '✗'}"
                )
            else:
                print(f"{gadget:<20} {str(expected):<10} {actual:<10} {'?'}")
                all_match = False

    print("\nOverall test result: " + ("PASS" if all_match else "FAIL"))

    elapsed = time.perf_counter() - start
    print(f"Execution time for t={d}-SNI checks: {elapsed:.3f} seconds")
    return results


if __name__ == "__main__":

    @contextmanager
    def tee_stdout(file_path):
        """Context manager that writes stdout to both terminal and file."""

        class TeeOutput:
            def __init__(self, file, original_stdout):
                self.file = file
                self.original_stdout = original_stdout

            def write(self, message):
                self.file.write(message)
                self.original_stdout.write(message)

            def flush(self):
                self.file.flush()
                self.original_stdout.flush()

        original_stdout = sys.stdout
        try:
            with open(file_path, "w") as f:
                sys.stdout = TeeOutput(f, original_stdout)
                yield
        finally:
            sys.stdout = original_stdout

    F = GF(2**8)
    num_processes = 80
    num_func_tests = 1
    continue_on_fail = False
    log = False
    min_d, max_d = 1, 3
    with tee_stdout("IP_gadget_benchmarks.log"):
        for d in range(min_d, max_d + 1):
            verify_gadgets_correctness(F, d)
            verify_gadgets_SNI(
                F=F,
                d=d,
                log=log,
                num_processes=num_processes,
                continue_on_fail=continue_on_fail,
            )
