# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter, Namespace
from datetime import datetime
from enum import Enum, auto
import logging
import multiprocessing
from multiprocessing.managers import DictProxy
import os
from pathlib import Path
import sys
import traceback
from typing import List, cast

import pandas as pd

from sage.all import GF, is_prime
from sage.rings.integer_ring import ZZ

from benchmark import (
    preprocess_row,
    process_one_entry,
    write_config,
    BenchmarkGadgetNotFound,
    handle_abort,
)
from gadget_list import GADGETS
from polyring import clear_all_caches
from security import SecurityNotion

### LOGGING ###


class ColorFormatter(logging.Formatter):
    GREY = "\033[90m"
    RED = "\033[91m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    BLUE = "\033[94m"
    RESET = "\033[0m"
    BOLD = "\033[1m"

    FORMAT = "%(asctime)s [%(levelname)s]:\t%(message)s"

    FORMATS = {
        logging.DEBUG: GREY + FORMAT + RESET,
        logging.INFO: GREEN + FORMAT + RESET,
        logging.WARNING: YELLOW + FORMAT + RESET,
        logging.ERROR: RED + FORMAT + RESET,
        logging.CRITICAL: BOLD + RED + FORMAT + RESET,
    }

    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt, datefmt="%Y-%m-%d %H:%M:%S")
        return formatter.format(record)


SAVE_INTERVAL = 30  # seconds

### BENCHMARK ###


class BenchmarkResult(Enum):
    SUCCESS = auto()
    GADGET_NOT_FOUND = auto()
    TIMEOUT = auto()
    MEMORY = auto()
    OTHER = auto()
    INCOMPLETE = auto()


def benchmark_loop(
    row: pd.Series,
    timeout: int,
    max_processes: int,
    max_memory_mb: int,
    return_dict: DictProxy,
) -> None:
    try:
        row = process_one_entry(row, timeout, max_processes, max_memory_mb)
        return_dict["value"] = BenchmarkResult.SUCCESS
        return_dict["message"] = "Success"
    except BenchmarkGadgetNotFound as e:
        return_dict["value"] = BenchmarkResult.GADGET_NOT_FOUND
        return_dict["message"] = str(e)
    except TimeoutError as e:
        return_dict["value"] = BenchmarkResult.TIMEOUT
        return_dict["message"] = str(e)
    except MemoryError as e:
        return_dict["value"] = BenchmarkResult.MEMORY
        return_dict["message"] = str(e)
    except Exception as e:
        return_dict["value"] = BenchmarkResult.OTHER
        return_dict["message"] = str(e)
    finally:
        return_dict["row"] = row


def run_benchmark(args: Namespace):
    pd.options.mode.copy_on_write = True
    print("Running benchmark with args:")
    for k, v in vars(args).items():
        print(f"  {k}: {v}")

    OUT_PATH = Path(args.out_dir)
    OUT_CSV = OUT_PATH / "benchmark.csv"
    OUT_LOG = OUT_PATH / "benchmark.log"
    OUT_CONF = OUT_PATH / "benchmark.conf"

    file_mode = "a" if args.append else "w"

    f_log = open(OUT_LOG, file_mode, encoding="utf-8")
    sys.stdout = f_log

    if not os.path.exists(OUT_PATH):
        print(f"Output directory {OUT_PATH} does not exist. Creating it.")
        os.makedirs(OUT_PATH)

    print(f"Writing results to {OUT_PATH} (append mode: {args.append})")
    max_processes = args.processes
    max_memory_mb = args.max_memory_mb
    timeout = args.timeout
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    with open(OUT_CONF, file_mode, encoding="utf-8") as f_conf:
        write_config(f_conf, timestamp, timeout, max_processes, max_memory_mb)

    df = pd.read_csv(args.bench_file, sep=";")
    # add new columns (initially empty)
    logging.info("Adding extra columns...")
    for col in (
        "preprocessing_passed",
        "num_tuples",
        "verification_threads",
        "verification_time",
        "verification_timeout",
        "verification_result",
        "verification_comment",
    ):
        df[col] = ""

    df = df.apply(preprocess_row, axis=1)

    # set last_save to datetime now
    last_save = datetime.now()

    manager = multiprocessing.Manager()
    return_dict = manager.dict()

    for i in df.index:
        row = df.loc[i]
        if row["preprocessing_passed"]:
            # Clear all caches
            logging.info("Clearing caches...")
            clear_all_caches()
            logging.info("Caches cleared.")
            # We run each benchmark in a separate process here to improve accuracy of memory usage
            # This helps to avoid old variables not being garbage collected artificially increasing memory usage
            proc = multiprocessing.Process(
                target=benchmark_loop,
                args=(row, timeout, max_processes, max_memory_mb, return_dict),
            )
            proc.start()
            proc.join()
            result = return_dict["value"]
            message = return_dict["message"]

            row.update(return_dict["row"])

            match result:
                case BenchmarkResult.SUCCESS:
                    pass
                case BenchmarkResult.GADGET_NOT_FOUND:
                    logging.warning(
                        f"Failed to load gadget for row {i}: {message}"
                    )
                    row["verification_comment"] = message
                case BenchmarkResult.TIMEOUT:
                    logging.warning(f"Timeout occurred for row {i}: {message}")
                    handle_abort(
                        df, row, message, "Disabled due to prior timeout"
                    )
                case BenchmarkResult.MEMORY:
                    logging.warning(
                        f"Memory limit exceeded for row {i}: {message}"
                    )
                    handle_abort(
                        df, row, message, "Disabled due to prior memory limit"
                    )
                case BenchmarkResult.OTHER:
                    logging.warning(
                        f"Other error occured for row {i}: {message}"
                    )
                    row["verification_comment"] = message

            # Final checks to see whether our obtained results actually match expectations. If not, we log a warning, and add a message to the verification comment.
            if (
                row["timeout_expected"]
                and row["verification_timeout"]
                and row["timeout_expected"] != row["verification_timeout"]
            ):
                row["verification_comment"] += " | Unexpected timeout result"
            if (
                row["verification_result"]
                and row["expected_security_result"]
                and row["expected_security_result"]
                != row["verification_result"]
            ):
                row["verification_comment"] += (
                    " | Unexpected verification result"
                )
            df.loc[i] = row

        # check if last save is more than SAVE_INTERVAL seconds.
        if (datetime.now() - last_save).total_seconds() > SAVE_INTERVAL:
            logging.info(
                f"Last save was more than {SAVE_INTERVAL} seconds ago."
            )
            df.to_csv(
                OUT_CSV,
                sep=";",
                index=False,
                columns=cast(List[str], df.keys().drop("preprocessing_passed")),
            )
            last_save = datetime.now()
            logging.info(f"Saved intermediate results to {OUT_CSV}.")

    logging.info("Benchmark complete.")

    f_log.close()
    sys.stdout = sys.__stdout__


### VERIFICATION ###


def run_verify(args: Namespace):
    gadget = args.gadget
    nproc = args.processes
    k = args.nsecrets
    d = args.degree
    e = args.redundancy
    t = args.order
    notion = args.security
    verify_correctness = args.verify_correctness

    try:
        field = parse_field_specification(args.field)
    except ValueError as e:
        print(f"Field specification error: {e}")
        return False

    print(
        f"Verifying {t}-{notion} of {gadget}(k={k}, d={d}, e={e}) in {field} with {nproc} processes."
    )
    try:
        try:
            gadget = GADGETS[gadget].from_file(d, k, e, field)
        except Exception:
            gadget = GADGETS[gadget].with_defaults(d, k, e, field)
            gadget.serialize(d, k, e)
    except Exception as exc:
        print(f"Error while trying to generate gadget: {exc}", file=sys.stderr)
        return False

    passed = True
    if verify_correctness:
        passed = gadget.functional_correctness()

    passed = (
        gadget.verify(
            snotion=SecurityNotion[notion],
            t=t,
            num_worker=nproc,
            continue_on_fail=args.continue_on_fail,
            timeout=args.timeout,
            log=args.log,
            max_memory_mb=args.max_memory_mb,
        )
        and passed
    )

    return passed


### PARSING ###


def parse_field_specification(field_spec: str):
    """
    Parse field specification from command line.
    Expected formats:
    - 'q': returns GF(q)
    - 'p^k' or 'p**k': returns GF(p**k)
    - If no field specified or 'ZZ', returns integer ring
    """
    if not field_spec or field_spec.upper() == "ZZ":
        return ZZ

    # Handle p^m or p**m format
    if "^" in field_spec:
        parts = field_spec.split("^")
    elif "**" in field_spec:
        parts = field_spec.split("**")
    else:
        try:
            p = int(field_spec)
            return GF(p)
        except ValueError:
            raise ValueError(f"Invalid field specification: {field_spec}")

    if len(parts) != 2:
        raise ValueError(f"Invalid field specification format: {field_spec}")

    try:
        p = int(parts[0])
        k = int(parts[1])
        if not is_prime(p):
            raise ValueError(f"Base {p} must be prime")
        if k <= 0:
            raise ValueError(f"Extension degree {k} must be positive")
        return GF(p**k)
    except ValueError as ve:
        if "must be prime" in str(ve) or "must be positive" in str(ve):
            raise ve
        raise ValueError(f"Invalid field specification: {field_spec}")


def add_common_flags(parser):
    parser.add_argument(
        "--verify-correctness",
        action="store_true",
        default=False,
        help="Verify the correctness of the gadget",
    )
    parser.add_argument(
        "-p",
        "--processes",
        type=int,
        default=32,
        help="Number of worker processes for verification ",
    )
    parser.add_argument(
        "--continue-on-fail",
        action="store_true",
        default=False,
        help="Continue verification even if failures are encountered",
    )
    parser.add_argument(
        "--log",
        action="store_true",
        default=False,
        help="Enable logging during verification",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=3600,
        help="Timeout in seconds for verification (default: 3600 = 1 hour)",
    )
    parser.add_argument(
        "--max-memory-mb",
        type=int,
        default=8192,
        help="Maximum memory limit in MB for verification (default: 8192 = 8 GB)",
    )


def add_verify_flags(parser):
    parser.add_argument(
        "gadget", choices=GADGETS.keys(), help="Gadget to check"
    )
    parser.add_argument(
        "-d",
        "--degree",
        type=int,
        default=2,
        help="Security parameter d (must be > 0)",
    )
    parser.add_argument(
        "-k",
        "--nsecrets",
        type=int,
        default=1,
        help="Number of packed secrets k (must satisfy k <= d and possibly other constraint based on the gadget)",
    )
    parser.add_argument(
        "-e",
        "--redundancy",
        type=int,
        default=0,
        help="Redundancy parameter e (must be >= 0)",
    )
    parser.add_argument(
        "-t",
        "--order",
        type=int,
        default=1,
        help="Security order to check (must be > 0)",
    )
    parser.add_argument(
        "-f",
        "--field",
        type=str,
        default="2^8",
        help='Field specification: "p" for GF(p), "p^m" or "p**m" for GF(p^m), "ZZ" for integers',
    )
    parser.add_argument(
        "-n",
        "--security",
        choices=("PS", "NI", "SNI"),
        required=True,
        help="Security Notion",
    )


def add_benchmark_flags(parser):
    parser.add_argument(
        "--bench-file",
        type=str,
        required=True,
        help="CSV file containing the requested benchmarks",
    )
    parser.add_argument(
        "--out-dir",
        type=str,
        required=True,
        help="Output directory for benchmarks",
    )
    parser.add_argument(
        "--append",
        action="store_true",
        default=False,
        help="Append benchmark results to existing file (if any)",
    )


def cli():
    handler = logging.StreamHandler()
    handler.setFormatter(ColorFormatter())
    logging.basicConfig(level=logging.INFO, handlers=[handler])

    parser = ArgumentParser(
        description="eVer -- A tool for verifying and benchmarking gadgets",
        formatter_class=ArgumentDefaultsHelpFormatter,
    )
    subparsers = parser.add_subparsers(
        title="subcommands", dest="cmd", required=True
    )
    verify_parser = subparsers.add_parser(
        name="verify", help="Help for subcommand `verify`"
    )
    add_verify_flags(verify_parser)
    add_common_flags(verify_parser)

    benchmark_parser = subparsers.add_parser(
        name="benchmark", help="Help for subcommand `benchmark`"
    )
    add_benchmark_flags(benchmark_parser)
    add_common_flags(benchmark_parser)

    args = parser.parse_args()

    if args.processes <= 0:
        parser.error(f"Number of processes must be > 0, got {args.processes}")

    try:
        match args.cmd:
            case "verify":
                run_verify(args)
            case "benchmark":
                run_benchmark(args)
            case _:
                raise ValueError(f"Unknown command: {args.cmd}")
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    cli()
