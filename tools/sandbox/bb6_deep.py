#!/usr/bin/env python3
"""Deeper pass of BB(6) holdouts through 6 deciders.

Bigger budgets than the shallow first pass. Goals:
  1. Actually decide a few holdouts at the margins
  2. Capture which deciders catch which class
  3. Compare against shallow pass (delta = newly decided)

Per machine (worst case timeouts in parens):
  Lin_Recur (60s):  max-steps 100M (100x shallow)
  Quick_Sim (180s): max-loops 100000 + recursive + exp-linear-rules
  CPS small (60s):  block 30 window 100 max-iters 20000
  CPS large (90s):  block 60 window 200 max-iters 10000
  CTL2 (30s):       cutoff 10000 block 2 offset 0
  CTL3 (30s):       cutoff 10000 block 2 offset 0

Total max: 450 s. With 12 workers, 1085 machines, realistic 4-8 h wallclock.

Output: ~/src/collatz-cryptid/sim/bb6_deep_run/results.csv (separate dir
from shallow run to preserve both for delta comparison).
"""

from __future__ import annotations

import csv
import os
import re
import subprocess
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

BB_VENV = "/Users/gotrevor/.venvs/bb/bin/python"
BB_CODE = Path("/Users/gotrevor/src/busy-beaver/Code")
SHEET = Path("/tmp/bb6sheet.csv")
OUT_DIR = Path(os.path.expanduser(
    "~/src/collatz-cryptid/sim/bb6_deep_run"))

N_WORKERS = 12

DECIDERS = [
    ("quick_sim",
     ["Quick_Sim.py", "--max-loops", "50000", "--recursive",
      "--exp-linear-rules", "--quiet"],
     120),
    ("cps_small",
     ["CPS.py", "--block-size", "30", "--window-size", "100",
      "--max-iters", "20000", "--max-configs", "50000"],
     90),
    ("cps_large",
     ["CPS.py", "--block-size", "80", "--window-size", "250",
      "--max-iters", "10000", "--max-configs", "50000"],
     120),
    ("ctl2_b2", ["CTL2.py", "{tm}", "10000", "2", "0"], 20),
    ("ctl2_b4", ["CTL2.py", "{tm}", "5000",  "4", "0"], 20),
    ("ctl3_b2", ["CTL3.py", "{tm}", "10000", "2", "0"], 20),
    ("ctl3_b4", ["CTL3.py", "{tm}", "5000",  "4", "0"], 20),
]


def build_cmd(args: list[str], tm: str) -> list[str]:
    """Substitute {tm} placeholder if present, else append tm at end."""
    if any("{tm}" in a for a in args):
        return [BB_VENV, str(BB_CODE / args[0])] + [
            (a.replace("{tm}", tm) if a != args[0] else a) for a in args[1:]
        ]
    return [BB_VENV, str(BB_CODE / args[0]), *args[1:], tm]


def run_decider(name: str, args: list[str], timeout: int, tm: str) -> dict:
    cmd = build_cmd(args, tm)
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True,
                              timeout=timeout, text=True)
        return {
            "name": name,
            "timeout": False,
            "elapsed": round(time.time() - t0, 2),
            "stdout": proc.stdout,
            "stderr": proc.stderr[-300:] if proc.stderr else "",
            "returncode": proc.returncode,
        }
    except subprocess.TimeoutExpired:
        return {"name": name, "timeout": True, "elapsed": timeout,
                "stdout": "", "stderr": "", "returncode": -1}


def parse_lin_recur(stdout: str) -> dict:
    if "period:" in stdout:
        period = re.search(r"period:\s*(\d+)", stdout)
        start = re.search(r"start_step:\s*(\d+)", stdout)
        return {"lr_decided": True,
                "lr_period": int(period.group(1)) if period else -1,
                "lr_start": int(start.group(1)) if start else -1}
    return {"lr_decided": False, "lr_period": 0, "lr_start": 0}


def parse_quick_sim(stdout: str) -> dict:
    halted = ("Halted" in stdout or
              ("Halt" in stdout and "halted" in stdout.lower()))
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
                nonzeros = -2
            else:
                nonzeros = int(v)
        except (ValueError, TypeError):
            pass
    return {"qs_halted": halted, "qs_proven_inf": proven_inf,
            "qs_rules": rules, "qs_nonzeros": nonzeros}


def parse_cps(stdout: str) -> dict:
    success = '"success": true' in stdout.lower()
    inf_loop = '"foundinfloop": true' in stdout.lower()
    num_configs = -1
    m = re.search(r'"numConfigs":\s*"(\d+)"', stdout)
    if m:
        num_configs = int(m.group(1))
    return {"success": success, "inf_loop": inf_loop,
            "num_configs": num_configs}


def parse_ctl(stdout: str) -> dict:
    # CTL prints "Success ..." or "Failure :(" depending on outcome.
    success = "Success" in stdout and "Failure" not in stdout.split(
        "Success", 1)[-1].split("\n", 1)[0]
    iters = -1
    m = re.search(r"in (\d+) iterations", stdout)
    if m:
        iters = int(m.group(1))
    return {"success": success, "iters": iters}


def process_machine(item: tuple[int, str, str]) -> dict:
    idx, tm, classification = item
    res = {"idx": idx, "tm": tm, "classification": classification}
    for name, args, timeout in DECIDERS:
        r = run_decider(name, args, timeout, tm)
        res[f"{name}_elapsed"] = r["elapsed"]
        res[f"{name}_timeout"] = r["timeout"]
        if r["timeout"]:
            continue
        try:
            if name == "lin_recur":
                res.update(parse_lin_recur(r["stdout"]))
            elif name == "quick_sim":
                res.update(parse_quick_sim(r["stdout"]))
            elif name.startswith("cps"):
                p = parse_cps(r["stdout"])
                res[f"{name}_success"] = p["success"]
                res[f"{name}_inf_loop"] = p["inf_loop"]
                res[f"{name}_num_configs"] = p["num_configs"]
            elif name.startswith("ctl"):
                p = parse_ctl(r["stdout"])
                res[f"{name}_success"] = p["success"]
                res[f"{name}_iters"] = p["iters"]
        except Exception as e:
            res[f"{name}_parse_error"] = str(e)[:100]
    return res


def load_undecided() -> list[tuple[int, str, str]]:
    machines: list[tuple[int, str, str]] = []
    with SHEET.open() as f:
        reader = csv.reader(f)
        next(reader)
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
    print(f"Deep pass: {len(machines):,} undecided BB(6) machines")
    print(f"Workers: {N_WORKERS}  Output: {out_csv}")

    fieldnames = [
        "idx", "tm", "classification",
        "quick_sim_elapsed", "quick_sim_timeout",
        "qs_halted", "qs_proven_inf", "qs_rules", "qs_nonzeros",
        "cps_small_elapsed", "cps_small_timeout",
        "cps_small_success", "cps_small_inf_loop", "cps_small_num_configs",
        "cps_large_elapsed", "cps_large_timeout",
        "cps_large_success", "cps_large_inf_loop", "cps_large_num_configs",
        "ctl2_b2_elapsed", "ctl2_b2_timeout", "ctl2_b2_success", "ctl2_b2_iters",
        "ctl2_b4_elapsed", "ctl2_b4_timeout", "ctl2_b4_success", "ctl2_b4_iters",
        "ctl3_b2_elapsed", "ctl3_b2_timeout", "ctl3_b2_success", "ctl3_b2_iters",
        "ctl3_b4_elapsed", "ctl3_b4_timeout", "ctl3_b4_success", "ctl3_b4_iters",
    ]

    t0 = time.time()
    written = 0
    decided_so_far = 0
    log_f = log_path.open("w", buffering=1)
    err_f = err_path.open("w", buffering=1)

    def is_decided(r: dict) -> bool:
        return (r.get("qs_halted") or
                r.get("qs_proven_inf") or
                r.get("cps_small_success") or r.get("cps_large_success") or
                r.get("ctl2_b2_success") or r.get("ctl2_b4_success") or
                r.get("ctl3_b2_success") or r.get("ctl3_b4_success"))

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
                        if is_decided(res):
                            decided_so_far += 1
                            msg = (f"  ⭐ DECIDED: {res['tm']}  "
                                   f"class={res.get('classification', '')[:40]}")
                            print(msg)
                            log_f.write(msg + "\n")
                        if written % 25 == 0:
                            elapsed = time.time() - t0
                            rate = written / elapsed
                            eta = (len(machines) - written) / rate \
                                if rate > 0 else 0
                            msg = (f"[{written}/{len(machines)}] "
                                   f"decided={decided_so_far} "
                                   f"rate={rate*60:.1f}/min "
                                   f"elapsed={elapsed/60:.1f}m "
                                   f"eta={eta/60:.1f}m")
                            print(msg)
                            log_f.write(msg + "\n")
                    except Exception as e:
                        m = futs[fut]
                        err_f.write(f"ERROR on {m[1]}: {e}\n")
        except KeyboardInterrupt:
            print("\nInterrupted.")
            log_f.write("INTERRUPTED\n")

    log_f.write(f"DONE - {written}/{len(machines)} decided={decided_so_far} "
                f"in {(time.time()-t0)/60:.1f}m\n")
    log_f.close()
    err_f.close()
    print(f"DONE - {written} results, {decided_so_far} decided "
          f"({decided_so_far/written*100:.2f}%)  -> {out_csv}")


if __name__ == "__main__":
    main()
