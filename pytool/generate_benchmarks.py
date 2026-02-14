# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
import csv
from itertools import product
import os
from pathlib import Path
import platform
import psutil
import subprocess
import sys
import time
from typing import Sequence, Tuple, Type

from sage.all import GF
from sage.rings.integer_ring import ZZ
from tqdm import tqdm

from encoding import IP_setup
from polymasking_gadgets import (
    make_f_encodings,
    make_f_g_encodings,
    make_h_encodings,
)
from gen_parameter_vars import gen_A_tilde_3D
from ip_masking_gadgets import (
    IPAddGadget,
    IPMultGadget,
    IPRefreshGadget,
    SecIPRefreshGadget,
)
from observations import ObservationTupleManager
from polymasking_gadgets import (
    Gadget,
    BgwMultGadget,
    LaolaMultGadget,
    OptRefresh,
    FOWZ25Refresh,
    RefreshSFRES18,
    SWComp,
    SWPolyAddGadget,
    SWPolyMulGadget,
    SWPolySubGadget,
)
from security import SecurityNotion

# adjust this to your needs
MAX_N_THREADS = 80
TIMEOUT = 15 * 60  # 15 minutes verification timeout
MAX_MEM = 500 * 1024  # max total memory usage

# output directory for the benchmarks
BENCHMARK_DIR = Path("benchmarks")


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


# add all the Gadget classes here that you want to benchmark

GADGETS_SMALL = [
    # # Basic polymasking component gadgets
    SWPolyAddGadget,
    SWPolySubGadget,
    SWPolyMulGadget,
    SWComp,
    # # Zero encodings (have no input)
    # Zenc,
    # SZenc,
    # OptZenc,
    # OptSZenc,
    # ZencSFRES18,
    # # Refresh gadgets
    FOWZ25Refresh,
    OptRefresh,
    RefreshSFRES18,
    # # IP gadgets
    IPAddGadget,
    IPRefreshGadget,
    SecIPRefreshGadget,
    IPMultGadget,
]

GADGETS_EXP = [
    # # multiplication gadgets
    BgwMultGadget,
    LaolaMultGadget,
]


def expected_verification_result(sec_notion, t, gadget):
    # all gadgets should fulfill NI and t-probing, while only some fulfill SNI properties
    EXPECTED_RESULT = {
        # Polymasking gadgets
        SWPolyAddGadget: False if sec_notion is SecurityNotion.SNI else True,
        SWPolySubGadget: False if sec_notion is SecurityNotion.SNI else True,
        SWPolyMulGadget: False if sec_notion is SecurityNotion.SNI else True,
        SWComp: True,
        BgwMultGadget: True,
        LaolaMultGadget: True,
        # Refresh gadgets
        FOWZ25Refresh: True,
        OptRefresh: True,
        RefreshSFRES18: False
        if sec_notion is SecurityNotion.SNI and t > 2
        else True,  # This gadget is not SNI for t>2, but secure otherwise
        # IP gadgets
        IPAddGadget: False if sec_notion is SecurityNotion.SNI else True,
        IPRefreshGadget: False
        if sec_notion is SecurityNotion.SNI and t > 2
        else True,  # This gadget is not SNI for t>2, but secure otherwise
        SecIPRefreshGadget: True,
        IPMultGadget: True,
    }

    return EXPECTED_RESULT[type(gadget)]


GADGETS_ALL = GADGETS_SMALL + GADGETS_EXP
GADGET_LIST = GADGETS_ALL

# add all the fields you want to benchmark
FIELDS = {
    "GF(2^8)": GF(2**8),
    "GF(7)": GF(7),
    "GF(3329)": GF(3329),  # used in ML-KEM (Kyber)
    "ZZ": ZZ,
}

FIELD_STR = {F: F_str for F_str, F in FIELDS.items()}

SNOTIONS = [
    SecurityNotion.NI,
    SecurityNotion.SNI,
    # SecurityNotion.PS # PS seems to be a bit broken, let's ignore it for now?
]

# (d, e, k)
PARAMS_BASE = list(product(range(1, 3), range(4), [1]))
PARAMS_HIGH = list(product(range(3, 7), range(4), [1]))

# k=[2..4], d=[2..4], e=[0...3] für BGW
PARAMS_BGW = list(product(range(2, 5), range(4), range(2, 5)))
# k=2, d=[4], e=[0...3] für LaOla
PARAMS_LAOLA = list(product([4], range(4), [2]))

# (G, F, snotion, (d, e, k))
TEST_CASES = []
TEST_CASES += list(product(GADGETS_SMALL, ["GF(2^8)"], SNOTIONS, PARAMS_BASE))
TEST_CASES += list(product(GADGETS_SMALL, ["GF(2^8)"], SNOTIONS, PARAMS_HIGH))

TEST_CASES += list(product(GADGETS_EXP, ["GF(2^8)"], SNOTIONS, PARAMS_BASE))
TEST_CASES += list(product(GADGETS_EXP, ["GF(2^8)"], SNOTIONS, PARAMS_HIGH))

TEST_CASES += list(product([BgwMultGadget], ["GF(2^8)"], SNOTIONS, PARAMS_BGW))
TEST_CASES += list(
    product([LaolaMultGadget], ["GF(2^8)"], SNOTIONS, PARAMS_LAOLA)
)


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


# ugly way to dynamically keep track of benchmarks to skip (due to timeout)
# (G, F, snotion, (d, e, k))
SKIP_BENCHMARKS = set()


def benchmark(G: Type, k: int, d: int, e: int, snotion: SecurityNotion, F: str):
    global SKIP_BENCHMARKS
    assert issubclass(G, Gadget), f"G is not a gadget type!"
    print(f"Verifying {G.__name__}(k={k}, d={d}, e={e}) in {F}.")

    n = (
        2 * d + e + 1
        if G == BgwMultGadget
        else d + 1
        if G in [IPAddGadget, IPMultGadget, IPRefreshGadget, SecIPRefreshGadget]
        else d + e + 1
    )

    if (G, F, snotion, (d, e, k)) in SKIP_BENCHMARKS:
        print(
            f"Skipping benchmark for {G.__name__}(k={k}, d={d}, e={e}) in {F} due to previous timeout."
        )
        return {
            "gadget": G.__name__,
            "d": d,
            "e": e,
            "k": k,
            "field": "",
            "t": d,
            "notion": snotion.name,
            "result_correct": False,
            "result_secure": False,
            "gen_time": 0.0,
            "check_correctness_time": 0.0,
            "verif_time": 0.0,
            "num_tuples": 0,
            "num_threads": 0,
            "comment": "Skipped benchmark due to previous timeout.",
        }

    start = time.time_ns()

    # FIXME: improve this part of the code later on
    if G in [BgwMultGadget, LaolaMultGadget]:
        F_enc, G_enc, rc = make_f_g_encodings(d, e, n, k, FIELDS[F])
        gadget = G(f=F_enc, g=G_enc, d=d, rc=rc, callloc=None)
    elif G in [SWPolyAddGadget, SWPolySubGadget, SWPolyMulGadget]:
        F_enc, G_enc, rc = make_f_g_encodings(d, e, n, k, FIELDS[F])
        gadget = G(f=F_enc, g=G_enc, callloc=None)
    elif G in [FOWZ25Refresh, RefreshSFRES18]:
        R_enc, ref_rc = make_f_encodings(d, e, n, k, FIELDS[F])
        gadget = G(f=R_enc, d=d, rc=ref_rc, callloc=None)
    elif G in [OptRefresh]:
        R_enc, ref_rc = make_f_encodings(d, e, n, k, FIELDS[F])

        base_ring = R_enc.base_ring
        support_points = R_enc.support_points
        secret_support_points = R_enc.secret_support_points
        # A_tilde
        if k == 1:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, [base_ring.zero()], support_points
            )
        else:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, secret_support_points, support_points
            )

        gadget = G(f=R_enc, d=d, A_tilde=a_tilde, rc=ref_rc, callloc=None)
    elif G in [SWComp]:
        H0, H1, H2, H3, h_rc = make_h_encodings(d, e, n, k, FIELDS[F])
        base_ring = H0.base_ring
        support_points = H0.support_points
        secret_support_points = H0.secret_support_points
        # A_tilde
        if k == 1:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, [base_ring.zero()], support_points
            )
        else:
            a_tilde = gen_A_tilde_3D(
                base_ring, n, d, k, secret_support_points, support_points
            )

        gadget = G(
            H0=H0,
            H1=H1,
            H2=H2,
            H3=H3,
            d=d,
            A_tilde=a_tilde,
            rc=h_rc,
            callloc=None,
        )
    elif G in [IPAddGadget]:
        ip_encodings, rc_ip = IP_setup(
            FIELDS[F], ["x", "y"], n, max_randoms=100
        )
        x_enc = ip_encodings["x"]
        y_enc = ip_encodings["y"]
        gadget = G(x=x_enc, y=y_enc, callloc=None)
    elif G in [IPRefreshGadget, SecIPRefreshGadget]:
        ip_encodings, rc_ip = IP_setup(FIELDS[F], ["x"], n, max_randoms=100)
        x_enc = ip_encodings["x"]
        gadget = G(x_enc, rc=rc_ip, callloc=None)
    elif G in [IPMultGadget]:
        ip_encodings, rc_ip = IP_setup(
            FIELDS[F], ["x", "y"], n, max_randoms=100
        )
        x_enc = ip_encodings["x"]
        y_enc = ip_encodings["y"]
        gadget = G(A=x_enc, B=y_enc, rc=rc_ip, callloc=None)
    else:
        raise ValueError(
            f"Gadget {G.__name__} is not supported yet. Please add the right constructor here!"
        )
    gadget_creation_time = (time.time_ns() - start) / 1e9
    # print(f"Gadget creation took {gadget_creation_time:.2f} seconds.")

    start = time.time_ns()
    gadget.serialize(d, k, e)
    gadget_serialization_time = (time.time_ns() - start) / 1e9
    # print(f"Gadget serialization took {gadget_serialization_time:.2f} seconds.")

    start = time.time_ns()
    correct = True
    try:
        if d < 5:
            correct = gadget.functional_correctness()
    except Exception as exc:
        # SWPolyMul can fail functional testing if there are not enough shares to decode the result with too high of a degree, since n shares can only decode a polynomial of degree n-1
        if type(gadget) is SWPolyMulGadget:
            sys.stderr.write(
                f"Error during functional correctness check for gadget {G.__name__}: {exc}\n"
            )
            correct = False
        else:
            raise exc

    functional_correctness_time = (time.time_ns() - start) / 1e9
    # print(f"Functional correctness check took {functional_correctness_time:.2f} seconds.")

    # Compute number of observation tuples to actually check
    obstuples = count_observations_in_obsgraph(snotion, d, gadget)

    num_threads = threading_heuristic(obstuples)

    start = time.time_ns()
    timed_out = False
    expected_res = expected_verification_result(snotion, t=d, gadget=gadget)
    if snotion == SecurityNotion.NI:
        secure = gadget.verify_t_NI(
            t=d,
            num_worker=num_threads,
            log=False,
            continue_on_fail=False,
            max_memory_mb=MAX_MEM,
            timeout=TIMEOUT,
        )
    elif snotion == SecurityNotion.SNI:
        secure = gadget.verify_t_SNI(
            t=d,
            num_worker=num_threads,
            log=False,
            continue_on_fail=False,
            max_memory_mb=MAX_MEM,
            timeout=TIMEOUT,
        )
    elif snotion == SecurityNotion.PS:
        secure = gadget.verify_t_PS(
            t=d,
            num_worker=num_threads,
            log=False,
            continue_on_fail=False,
            max_memory_mb=MAX_MEM,
            timeout=TIMEOUT,
        )
    else:
        raise ValueError(
            f"Unknown security notion {snotion} for gadget {G.__name__}."
        )
    verification_time = (time.time_ns() - start) / 1e9

    if verification_time < TIMEOUT:
        assert expected_res == secure, (
            f"The outcome of verification of gadget {gadget} with order {d} and notion {snotion} does not match the expected outcome:\n   expected {expected_res}, actual {secure}"
        )

    comment = ""

    if verification_time > TIMEOUT:
        print(
            f"Timeout for {G.__name__}(k={k}, d={d}, e={e}) in {F} with security notion {snotion.name}. Verification time: {verification_time:.2f} seconds."
        )
        comment = "Timeout"
        # If we had a timeout, we skip benchmarks with higher values of e
        if (G, F, snotion, (d, e, k)) in TEST_CASES:
            for i in range(1, 10):  # overapproximation
                print("WILL SKIP BENCHMARK for", (G, k, d, e + i, snotion, F))
                SKIP_BENCHMARKS.add((G, F, snotion, (d, e + i, k)))
            # special case: e=0 already fails, then we can skip all higher d values for arbitrary e as well
            if e == 0:
                for i in range(1, 10):
                    for j in range(10):  # overapproximation
                        print(
                            "WILL SKIP BENCHMARK for",
                            (G, k, d + i, j, snotion, F),
                        )
                        SKIP_BENCHMARKS.add((G, F, snotion, (d + i, j, k)))

    result = {
        "gadget": gadget.name(),
        "d": d,
        "e": e,
        "k": k,
        "field": "",
        "t": d,
        "notion": snotion.name,
        "result_correct": correct,
        "result_secure": secure,
        "gen_time": gadget_creation_time + gadget_serialization_time,
        "check_correctness_time": functional_correctness_time,
        "verif_time": verification_time,
        "num_tuples": obstuples,
        "num_threads": num_threads,
        "comment": comment,
    }

    return result


def generate_benchmarks() -> Sequence[
    Tuple[Type, Type, SecurityNotion, int, int, int]
]:
    return [
        (g, F, snotion, d, e, k) for (g, F, snotion, (d, e, k)) in TEST_CASES
    ]


def run_benchmarks(
    outfile: Path,
    benchmarks: Sequence[Tuple[Type, str, SecurityNotion, int, int, int]],
):
    COLUMNS = [
        "gadget",
        "d",
        "e",
        "k",
        "field",
        "t",
        "notion",
        "result_correct",
        "result_secure",
        "gen_time",
        "check_correctness_time",
        "verif_time",
        "num_tuples",
        "num_threads",
        "comment",
    ]

    with open(outfile, "w") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()

        for gadget, F, snotion, d, e, k in tqdm(benchmarks):
            entry = benchmark(G=gadget, k=k, d=d, e=e, snotion=snotion, F=F)
            entry["field"] = F
            writer.writerow(entry)
            f.flush()


def entry_to_str(
    entry: Tuple[Type, Type, SecurityNotion, int, int, int],
) -> str:
    gadget, F, snotion, d, e, k = entry
    return f"{gadget.__name__}(k={k}, d={d}, e={e}, field={FIELDS[F]}, notion={snotion.name})\n"


def write_config(
    cfg_name: Path,
    timestamp: str,
    benchmarks: Sequence[
        Tuple[Type, Tuple[str, Type], SecurityNotion, int, int, int]
    ],
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

    instances: Sequence[str] = []
    for ctr, instance in enumerate(benchmarks):
        instances.append(f"{ctr:<3}: {entry_to_str(instance)}")

    with open(cfg_name, "w") as cfg_file:
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
        cfg_file.write(f"max_threads      = {MAX_N_THREADS}\n")
        cfg_file.write(
            f"gadget_list      = {', '.join(g.__name__ for g in GADGET_LIST)}\n"
        )
        cfg_file.write(f"fields           = {', '.join(FIELDS.keys())}\n")
        cfg_file.write(
            f"security_notions = {', '.join(sn.name for sn in SNOTIONS)}\n"
        )
        cfg_file.write(f"num_instances    = {len(benchmarks)}\n")
        cfg_file.write("#\n")
        cfg_file.write(
            "# Benchmark results for the following instances will be generated and stored in the CSV file.\n"
        )
        cfg_file.write("# Each line corresponds to a benchmark instance.\n")
        cfg_file.write("# Format: gadget(k, d, e, field, notion)\n")
        cfg_file.write("# Instances:\n")
        cfg_file.writelines(instances)


def main():
    timestamp = time.strftime("%Y%m%d-%H%M%S")
    bench_path = BENCHMARK_DIR / timestamp
    print("Bench path:", bench_path)
    sys.stdout.flush()
    os.makedirs(bench_path, exist_ok=True)

    benchmark_configs: Sequence[
        Sequence[Tuple[Type, Type, SecurityNotion, int, int, int]]
    ] = generate_benchmarks()

    write_config(
        bench_path / "ever_benchmark.conf", timestamp, benchmark_configs
    )
    sys.stdout = open(bench_path / "ever_benchmark.log", "w")
    run_benchmarks(bench_path / "ever_benchmark.csv", benchmark_configs)


main()
