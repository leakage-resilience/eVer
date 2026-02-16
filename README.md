# Overview
This repository contains the codebase belonging to the paper [eVer: Universal and Automated Verification of Side-Channel Security for Additive, Inner Product, Polynomial and General Code-Based Masking](https://eprint.iacr.org/2026/208).
We publish the verification kernel, as well as, all 37 gadgets used to produce the benchmarks in our paper.
If our paper or verification tool proves useful in your work, we kindly ask that you cite the corresponding publication.

## Getting Started
This repository is configured to run inside a VS Code Dev Container based on Debian.

1. Open this folder in VS Code and install the [VS Code Dev Containers extension](https://code.visualstudio.com/docs/remote/containers).
2. When prompted, **Reopen in Container** (or use **Remote-Containers: Reopen in Container** from the Command Palette).

To reproduce the benchmark conducted in the paper in full scope, create the directory `benchmarks` and execute the following command.
```bash
python3 cli.py benchmark -p <max_processes> --bench-file benchmarks.csv --out-dir benchmarks
```
This will create a `benchmark.csv` file which should produce the verification outcomes for the gadgets evaluated in the paper.
To check a subset of these benchmarks remove the corresponding lines in the `.csv`.


Single gadgets can be verified for security using the following command:
```bash
python3 cli.py verify <gadget> -d <d> -e <e> -k <k> -t <t> -n <PS/NI/SNI> -p <num_processes>
```
For example, to verify the inner-product multiplication masked at order 3 for `2-SNI` run this command:
```bash
python3 cli.py verify IPMultGadget -d 3 -e 0 -k 1 -t 2 -n SNI -p <num_processes>
```

To get a list of supported gadgets run
```bash
python3 cli.py verify
```

Single gadgets can in addition be verified for functional correctness using the following command:
```bash
python3 cli.py verify --verify-correctness <gadget> -d <d> -e <e> -k <k> -t <t> -n <PS/NI/SNI> -p <num_processes>
```
For example
```bash

python3 cli.py verify --verify-correctness IPMultGadget -d 3 -e 0 -k 1 -t 2 -n SNI -p <num_processes>
```
The implemented gadgets can be found in:
- [GCM22](GCM_WCG22_gadgets.py)
- [GCM20](GCM_WMCS20_gadgets.py)
- [IPM](ip_masking_gadgets.py)
- [ISW](isw_gadgets.py)
- [PM](polymasking_gadgets.py)

To generate the full suite of gadgets, run:
```bash
python3 generate_gadgets.py
```

## Alternative Getting Started (Experimental)

This project plans to support development environments using [Nix](https://nixos.org/download) with flakes. 
Flakes provide a standardized and reproducible way to manage project dependencies and development environments.

1. Install Nix by following the instructions on the official website. Make sure to [enable flakes support](https://nixos.wiki/wiki/Flakes#Enable_flakes).
2. Once Nix is set up, run the following command in the project's root directory to enter the development shell:
   ```bash
   nix develop 
   ```
3. This will provide a shell with all the project dependencies readily available.
4. You can run the commands as above, but instead of using `python3` you need to use `sage -python`.
