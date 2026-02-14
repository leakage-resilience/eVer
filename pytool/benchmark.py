# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from dataclasses import dataclass
import logging
from multiprocessing import cpu_count
import os
import platform
import subprocess
import time
from typing import Dict, Optional, Self, TextIO, Tuple, Type

import pandas as pd
import psutil

from sage.all import GF
from sage.rings.integer_ring import ZZ

from gadget import Gadget
from gadget_list import GADGETS
from observations import ObservationTupleManager
from security import SecurityNotion


MAX_N_THREADS = cpu_count()

# add all the fields you want to benchmark
STR_TO_FIELD = {
    "GF(2^8)": GF(2**8),
    "GF(7)": GF(7),
    "GF(3329)": GF(3329),  # used in ML-KEM (Kyber)
    "ZZ": ZZ,
}


class BenchmarkDisabled(Exception):
    """Raised when the benchmark line is disabled."""

    def __init__(self, message="Benchmark disabled"):
        super().__init__(message)


class BenchmarkInvalidParams(Exception):
    """Raised when the benchmark line contains invalid parameters."""

    def __init__(self, message="Invalid parameters"):
        super().__init__(message)


class BenchmarkGadgetNotFound(Exception):
    """Raised when the benchmark line refers to a gadget that cannot be loaded."""

    def __init__(self, message="Gadget not found"):
        super().__init__(message)


class BenchmarkOther(Exception):
    """
    Raised when the benchmark line encountered an unexpected error.
    """

    def __init__(self, message="Other error"):
        super().__init__(message)


class GadgetBenchmark:
    """
    Represents a benchmark for a specific gadget.
    """

    def __init__(
        self,
        gadget: Type[Gadget],
        d: int,
        e: int,
        k: int,
        t: int,
        field: Type,
        notion: SecurityNotion,
        expect_verif_success: bool,
        expect_verif_timeout: bool,
        row: Dict[str, str],
    ):
        self.gadget = gadget
        self.d = d
        self.e = e
        self.k = k
        self.t = t
        self.field = field
        self.notion = notion
        self.expect_verif_success = expect_verif_success
        self.expect_verif_timeout = expect_verif_timeout
        self.orig_row = row

    def __str__(self: Self) -> str:
        return f"{self.gadget.__name__}(k={self.k}, d={self.d}, e={self.e}, t={self.t}, field={self.field}, notion={self.notion})"


class PseudoBenchmark:
    def __init__(self, row: Dict[str, str], msg: str):
        self.orig_row = row
        self.msg = msg

    def __str__(self: Self) -> str:
        return f"PseudoBenchmark(msg: {self.msg})"


@dataclass
class BenchmarkResult:
    num_tuples: Optional[int] = None
    verification_threads: Optional[int] = None
    verification_time: Optional[float] = None
    verification_timeout: Optional[bool] = None
    verification_result: Optional[bool] = None
    verification_comment: str = ""


# TODO: This is the copy-pasted (partially simplified) version of `verify_security()` from `ever.py`, remove duplicate code later on when there is an interface to obtain the actual number of observations.
def count_observations_in_obsgraph(
    security_notion: SecurityNotion,
    security_order: int,
    g: Gadget,
) -> int:
    obsgraph = g.obsgraph()
    svars = g.secret_vars_symbolic()  # _encoded for PS
    pvars = g.public_vars()
    paravars = g.parameter_vars()

    output_observations = set()
    # ONLY For SNI
    if security_notion == SecurityNotion.SNI:
        output_observations = set(i.ni_obs.get_id() for i in g.output().sharing)

    # 0) lots of well-formedness checking
    all_secrets = set()
    for sv in svars:
        ssv = set(sv)
        all_secrets.update(ssv)

    support_vars_set = set(paravars)

    # 1) Filter out purely public observations (no secrets or randomness)
    tplMgr = ObservationTupleManager(
        obsgraph, security_notion, security_order, svars, output_observations
    )
    _ = tplMgr.filter_public_observations(pvars | support_vars_set, log=False)
    # 1b) Remove duplicate observations to reduce count of tuples
    tplMgr.filter_duplicate_observations(log=False)

    # Build tuples based on security notion
    num_tuples, _ = tplMgr.obs_tuple_iter()
    return num_tuples


# heuristic for number of threads based on the number of observation tuples and an upper bound
def threading_heuristic(num_obstuples: int) -> int:
    if num_obstuples < 1000:
        return 1
    elif num_obstuples < 1000000:
        return min(32, MAX_N_THREADS)
    elif num_obstuples < 10000000:
        return min(64, MAX_N_THREADS)
    else:
        return MAX_N_THREADS


def write_config(
    cfg_file: TextIO,
    timestamp: str,
    timeout: int,
    max_processes: int,
    max_memory_mb: int,
):
    """Write the benchmark configuration to a file for later reference."""

    # obtain system information
    cpu = (
        subprocess.run(["lscpu"], capture_output=True)
        .stdout.decode("utf-8")
        .splitlines()
    )
    model_name = ", ".join(
        map(
            lambda l: l.split(":")[1].strip(),
            filter(lambda l: l.startswith("Model name"), cpu),
        )
    )

    cfg_file.write("# eVer Benchmark Configuration\n")
    cfg_file.write("# System Information\n")
    cfg_file.write(f"timestamp        = {timestamp}\n")
    cfg_file.write(f"machine_name     = {platform.node()}\n")
    cfg_file.write(f"cpu_model        = {model_name}\n")
    cfg_file.write(f"cpu_count        = {os.cpu_count()}\n")
    cfg_file.write(
        f"memory           = {psutil.virtual_memory().total // (1024**3)} GB\n"
    )
    cfg_file.write(f"python_version   = {platform.python_version()}\n")
    cfg_file.write("# Benchmark parameters\n")
    cfg_file.write(f"max_threads      = {max_processes}\n")
    cfg_file.write(f"timeout (s)      = {timeout}\n")
    cfg_file.write(f"max_memory (MB)  = {max_memory_mb}\n")
    cfg_file.write("#\n")
    cfg_file.write(
        "# Benchmark results for the following instances will be generated and stored in the CSV file.\n"
    )
    cfg_file.write("# Each line corresponds to a benchmark instance.\n")
    cfg_file.write("# Format: gadget(k, d, e, field, notion)\n")


def preprocess_row(row: pd.Series) -> pd.Series:
    """ "Takes a raw pd.Series and performs sanity checks."""
    try:
        # skip all rows that should not be verified
        if not row["verify_security"]:
            gadget_str = f"{row['gadget']}(d={row['d']}, e={row['e']}, k={row['k']}, t={row['t']}, field={row['field']}, notion={row['notion']})"
            logging.info(
                f"Skipping {gadget_str}, because verify_security is not set to `true`."
            )
            raise BenchmarkDisabled

        # skip rows with invalid/unsupported gadget names and emit a warning
        if row["gadget"] not in GADGETS:
            logging.warning(f"Unknown gadget {row['gadget']}. Skipping.")
            raise BenchmarkGadgetNotFound

        # skip rows with invalid/unsupported security notions and emit a warning
        if row["notion"] not in SecurityNotion.__members__:
            logging.warning(
                f"Unknown security notion {row['notion']}. Skipping."
            )
            raise BenchmarkInvalidParams

        # skip rows with invalid/unsupported fields and emit a warning
        if row["field"] not in STR_TO_FIELD.keys():
            logging.warning(f"Unknown field {row['field']}. Skipping.")
            raise BenchmarkInvalidParams

        # skip rows with invalid/unsupported parameters d,e,k,t and emit a warning
        if row["d"] <= 0 or row["t"] <= 0:
            logging.warning(
                f"Parameters d, t must be positive integers, but got d={row['d']}, e={row['e']}, k={row['k']}, t={row['t']} for gadget {row['gadget']}."
            )
            raise BenchmarkInvalidParams
        if row["e"] < 0 or row["k"] < 0:
            logging.warning(
                f"Parameters e, k must be non-negative integers, but got d={row['d']}, e={row['e']}, k={row['k']}, t={row['t']} for gadget {row['gadget']}."
            )
            raise BenchmarkInvalidParams

        row["preprocessing_passed"] = True

    except (
        BenchmarkDisabled,
        BenchmarkGadgetNotFound,
        BenchmarkInvalidParams,
        BenchmarkOther,
    ) as e:
        row["verification_comment"] = str(e)
        row["preprocessing_passed"] = False

    return row


def load_gadget(G: Type, d: int, k: int, e: int, F: str) -> Gadget:
    """Loads gadget from file or raises BenchmarkGadgetNotFound."""
    try:
        start = time.time_ns()
        gadget = G.from_file(d=d, k=k, e=e, field=STR_TO_FIELD[F])
        logging.info(
            f"Loaded gadget (took {(time.time_ns() - start) / 1e6:.3f} ms)"
        )
    except Exception:
        logging.warning(f"Could not load gadget from file!")
        raise BenchmarkGadgetNotFound
    return gadget


def benchmark_gadget(
    g: Gadget,
    notion: SecurityNotion,
    t: int,
    timeout: int,
    memory_limit: int,
    num_threads: int,
) -> Tuple[float, bool]:
    start = time.time_ns()
    verification_result = g.verify(
        snotion=notion,
        t=t,
        num_worker=num_threads,
        continue_on_fail=False,
        max_memory_mb=memory_limit,
        timeout=timeout,
        log=False,
    )
    verification_time = (time.time_ns() - start) / 1e9
    return (verification_time, verification_result)


def handle_abort(
    df: pd.DataFrame, row: pd.Series, row_msg: str, other_msg: str
):
    match_col = lambda col: (df[col] == row[col])

    # match all rows where gadget, field, notion and k are equal
    mask = (
        match_col("gadget")
        & match_col("field")
        & match_col("notion")
        & match_col("k")
    )
    # match all rows where additionally d is equal and e is greater
    mask_1 = mask & match_col("d") & (df["e"] > row["e"])
    # match all rows where additionally d is greater and e is greater or equal
    mask_2 = mask & (df["d"] > row["d"]) & (df["e"] >= row["e"])

    # mark given row as timed out
    row["verification_timeout"] = True
    row["verification_comment"] = row_msg

    # disable all further benchmark rows where the above defined masks match
    df.loc[mask_1, "preprocessing_passed"] = False
    df.loc[mask_1, "verification_comment"] = other_msg

    df.loc[mask_2, "preprocessing_passed"] = False
    df.loc[mask_2, "verification_comment"] = other_msg


def destructure_row(
    row: pd.Series,
) -> Tuple[Type[Gadget], int, int, int, int, str, SecurityNotion]:
    G_type = GADGETS[row["gadget"]]
    d = int(row["d"])
    k = int(row["k"])
    e = int(row["e"])
    t = int(row["t"])
    field = row["field"]
    notion = SecurityNotion[row["notion"]]
    return G_type, d, k, e, t, field, notion


def process_one_entry(
    row: pd.Series, timeout: int, max_processes: int, memory_limit_mb: int
) -> pd.Series:
    # Load the gadget with parameters from file
    logging.info(f"Trying to load gadget {row['gadget']}...")
    G_type, d, k, e, t, field, notion = destructure_row(row)
    gadget = load_gadget(
        G_type, d, k, e, field
    )  # might throw: BenchmarkGadgetNotFound
    row["num_tuples"] = count_observations_in_obsgraph(notion, t, gadget)
    row["verification_threads"] = min(
        threading_heuristic(row["num_tuples"]), max_processes
    )

    logging.info(f"Benchmarking verification of gadget {gadget.name()}...")
    verif_time, verif_result = benchmark_gadget(
        gadget, notion, t, timeout, memory_limit_mb, row["verification_threads"]
    )  # might throw: TimeoutError, MemoryError
    logging.info(
        f"Verification benchmark result for {gadget.name()}: secure={verif_result} ({verif_time:.3f} seconds)"
    )

    row["verification_time"] = verif_time
    row["verification_timeout"] = False
    row["verification_result"] = verif_result
    row["verification_comment"] = ""
    return row
