#!/usr/bin/env python3
"""Overnight batch run of BB(6) holdouts through three deciders.

Input:  /tmp/bb6sheet.csv  (community spreadsheet, columns include
        machine, Status, Classification, ...)
        We process rows whose Status is empty (truly undecided as of
        spreadsheet snapshot ~ April 2026).

Per machine, runs three deciders with timeouts:
    Lin_Recur_Detect (30s, 1e6 steps)
    Quick_Sim        (60s, max-loops 10000, recursive)
    CPS              (60s, block-size 30, window 60, max-iters 5000)

Parallelism: 8 worker processes (each spawns subprocesses).

Output:
    ~/src/collatz-cryptid/sim/bb6_run/results.csv      (incremental, flushed)
    ~/src/collatz-cryptid/sim/bb6_run/log.txt          (progress log)
    ~/src/collatz-cryptid/sim/bb6_run/errors.txt       (any worker errors)

This script is designed to be run-and-forget. Survives KeyboardInterrupt
gracefully — results so far are preserved.
"""

from __future__ import annotations

import csv
import os
import re
import signal
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

BB_VENV = "/Users/gotrevor/.venvs/bb/bin/python"
BB_CODE = Path("/Users/gotrevor/src/busy-beaver/Code")
SHEET = Path("/tmp/bb6sheet.csv")
OUT_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim/bb6_run"))

N_WORKERS = 8

DECIDERS = [
    # (name, args after python, timeout seconds)
    ("lin_recur", ["Lin_Recur_Detect.py", "--max-steps", "1000000"], 30),
    ("quick_sim", ["Quick_Sim.py", "--max-loops", "10000", "--recursive", "--quiet"], 60),
    ("cps",       ["CPS.py", "--block-size", "30", "--window-size", "60",
                   "--max-iters", "5000"], 60),
]


def run_decider(name: str, args: list[str], timeout: int, tm: str) -> dict:
    """Run one decider against tm. Returns parsed result + raw tail."""
    cmd = [BB_VENV, str(BB_CODE / args[0]), *args[1:], tm]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, timeout=timeout,
                              text=True)
        return {
            "name": name,
            "timeout": False,
            "elapsed": round(time.time() - t0, 2),
            "stdout": proc.stdout,
            "returncode": proc.returncode,
        }
    except subprocess.TimeoutExpired:
        return {"name": name, "timeout": True,
                "elapsed": timeout, "stdout": "", "returncode": -1}


def parse_lin_recur(stdout: str) -> dict:
    """Lin_Recur prints protobuf-textual result. Look for 'period' field
    indicating recurrence found, vs empty result."""
    if "period:" in stdout:
        period = re.search(r"period:\s*(\d+)", stdout)
        start = re.search(r"start_step:\s*(\d+)", stdout)
        return {
            "lr_decided": True,
            "lr_period": int(period.group(1)) if period else -1,
            "lr_start": int(start.group(1)) if start else -1,
        }
    return {"lr_decided": False, "lr_period": 0, "lr_start": 0}


def parse_quick_sim(stdout: str) -> dict:
    """Quick_Sim output. Look for 'Halted' (machine reaches halt state)
    or 'Maximum number of loops' (ran out of budget)."""
    halted = "Halt" in stdout and ("halted" in stdout.lower() or
                                    "Halting" in stdout)
    proven_inf = "Proven infinite" in stdout or "PROVEN_INFINITE" in stdout
    rules = 0
    m = re.search(r"Collatz rules:\s*(\d+)", stdout)
    if m:
        rules = int(m.group(1))
    nonzeros = -1
    m = re.search(r"Num Nonzeros:\s*([0-9_~^.e+]+)", stdout)
    if m:
        try:
            v = m.group(1).replace("_", "")
            if "^" in v or "~" in v:
                nonzeros = -2  # exponential, didn't parse
            else:
                nonzeros = int(v)
        except (ValueError, TypeError):
            pass
    return {
        "qs_halted": halted,
        "qs_proven_inf": proven_inf,
        "qs_rules": rules,
        "qs_nonzeros": nonzeros,
    }


def parse_cps(stdout: str) -> dict:
    """CPS prints JSON-ish result with 'success' and 'foundInfLoop' fields."""
    success = '"success": true' in stdout.lower()
    inf_loop = '"foundinfloop": true' in stdout.lower()
    num_configs = -1
    m = re.search(r'"numConfigs":\s*"(\d+)"', stdout)
    if m:
        num_configs = int(m.group(1))
    return {
        "cps_success": success,
        "cps_inf_loop": inf_loop,
        "cps_num_configs": num_configs,
    }


PARSERS = {
    "lin_recur": parse_lin_recur,
    "quick_sim": parse_quick_sim,
    "cps": parse_cps,
}


def process_machine(item: tuple[int, str, str]) -> dict:
    """Run all deciders on one machine."""
    idx, tm, classification = item
    res = {"idx": idx, "tm": tm, "classification": classification}
    for name, args, timeout in DECIDERS:
        r = run_decider(name, args, timeout, tm)
        res[f"{name}_elapsed"] = r["elapsed"]
        res[f"{name}_timeout"] = r["timeout"]
        if not r["timeout"]:
            try:
                parsed = PARSERS[name](r["stdout"])
                res.update(parsed)
            except Exception as e:
                res[f"{name}_parse_error"] = str(e)[:100]
    return res


def load_undecided() -> list[tuple[int, str, str]]:
    """Read sheet, return list of (idx, tm, classification) for empty-Status rows."""
    machines: list[tuple[int, str, str]] = []
    with SHEET.open() as f:
        reader = csv.reader(f)
        next(reader)  # header
        for i, row in enumerate(reader):
            if len(row) < 3:
                continue
            tm, status, classification = row[0], row[1], row[2]
            if status.strip() == "":
                machines.append((i, tm, classification))
    return machines


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_csv = OUT_DIR / "results.csv"
    log_path = OUT_DIR / "log.txt"
    err_path = OUT_DIR / "errors.txt"

    machines = load_undecided()
    print(f"Loaded {len(machines):,} undecided BB(6) machines from {SHEET}")

    fieldnames = [
        "idx", "tm", "classification",
        "lin_recur_elapsed", "lin_recur_timeout",
        "lr_decided", "lr_period", "lr_start",
        "quick_sim_elapsed", "quick_sim_timeout",
        "qs_halted", "qs_proven_inf", "qs_rules", "qs_nonzeros",
        "cps_elapsed", "cps_timeout",
        "cps_success", "cps_inf_loop", "cps_num_configs",
        "lin_recur_parse_error", "quick_sim_parse_error",
        "cps_parse_error",
    ]

    t0 = time.time()
    written = 0
    log_f = log_path.open("w", buffering=1)  # line-buffered
    err_f = err_path.open("w", buffering=1)

    with out_csv.open("w", newline="") as fp:
        writer = csv.DictWriter(fp, fieldnames=fieldnames,
                                extrasaction="ignore")
        writer.writeheader()
        fp.flush()

        try:
            with ProcessPoolExecutor(max_workers=N_WORKERS) as ex:
                futs = {ex.submit(process_machine, m): m for m in machines}
                for fut in as_completed(futs):
                    try:
                        res = fut.result()
                        writer.writerow(res)
                        fp.flush()
                        written += 1
                        if written % 10 == 0:
                            elapsed = time.time() - t0
                            rate = written / elapsed
                            eta_sec = (len(machines) - written) / rate \
                                if rate > 0 else 0
                            msg = (f"[{written}/{len(machines)}] "
                                   f"rate={rate*60:.1f}/min "
                                   f"elapsed={elapsed/60:.1f}m "
                                   f"eta={eta_sec/60:.1f}m")
                            print(msg)
                            log_f.write(msg + "\n")
                    except Exception as e:
                        m = futs[fut]
                        err_f.write(f"ERROR on {m[1]}: {e}\n")
        except KeyboardInterrupt:
            print("\nInterrupted - partial results saved.")
            log_f.write("INTERRUPTED\n")

    log_f.write(f"DONE - {written}/{len(machines)} in "
                f"{(time.time()-t0)/60:.1f}m\n")
    log_f.close()
    err_f.close()
    print(f"DONE - {written} results written to {out_csv}")


if __name__ == "__main__":
    main()
