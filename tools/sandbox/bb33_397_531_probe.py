#!/usr/bin/env python3
"""Probe BB(3,3) holdouts 397 and 531 with aggressive Quick_Sim settings.

Try multiple block sizes + recursive prover + larger loop budgets.
Capture rules found, then run h153_analyze on verbose traces.
"""
import subprocess
import os
import sys
from pathlib import Path

QS = os.path.expanduser("~/src/busy-beaver/Code/Quick_Sim.py")
PY = os.path.expanduser("~/.venvs/bb/bin/python")
SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))
SIM_DIR.mkdir(exist_ok=True)

HOLDOUTS = {
    "397": "1RB1LB2LC_1LA2RB1RB_---0LA2LA",
    "531": "1RB2LA1LA_2LA0RA2RC_---0LC2RA",
}


def run(tag, tm, args, max_loops=20000, timeout=300):
    out = SIM_DIR / f"{tag}.txt"
    cmd = [PY, QS, "--max-loops", str(max_loops), *args, tm]
    print(f"[run] {tag}: {' '.join(args)} --max-loops {max_loops}", flush=True)
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        out.write_text(r.stdout + ("\n\n=== STDERR ===\n" + r.stderr if r.stderr else ""))
        print(f"  -> {out} ({len(r.stdout)} bytes)")
        return r.stdout
    except subprocess.TimeoutExpired:
        print(f"  TIMEOUT after {timeout}s")
        return ""


def summarize(output):
    """Pull headline metrics."""
    metrics = {}
    for line in output.splitlines():
        s = line.strip()
        for key in ("Diff rules proven", "Linear rules proven", "Collatz rules",
                    "Exponential rules proven", "General rules proven",
                    "Failed proofs", "Tape copies", "Num Nonzeros"):
            if s.startswith(key):
                # Extract number
                parts = s.split(":")
                if len(parts) >= 2:
                    metrics[key] = parts[1].strip().split()[0]
    return metrics


def main():
    configs = [
        # (tag-suffix, args, max_loops, timeout)
        ("default", [], 20000, 120),
        ("recursive", ["--recursive"], 20000, 120),
        ("rec_b2", ["--recursive", "--block-size", "2"], 20000, 120),
        ("rec_b3", ["--recursive", "--block-size", "3"], 20000, 120),
        ("rec_b4", ["--recursive", "--block-size", "4"], 20000, 120),
        ("rec_b5", ["--recursive", "--block-size", "5"], 20000, 120),
        ("rec_b6", ["--recursive", "--block-size", "6"], 20000, 120),
        ("rec_long", ["--recursive"], 100000, 300),
    ]

    summary = []
    for hid, tm in HOLDOUTS.items():
        for tag_suffix, args, loops, timeout in configs:
            tag = f"H{hid}_{tag_suffix}"
            out = run(tag, tm, args, max_loops=loops, timeout=timeout)
            m = summarize(out)
            summary.append((hid, tag_suffix, m))

    # Print compact table
    print("\n=== SUMMARY ===")
    print(f"{'holdout':<8} {'config':<14} {'Diff':<5} {'Lin':<5} {'Col':<5} {'Exp':<5} {'Gen':<5} {'Fail':<6} {'Copies':<8} {'Nonzeros':<10}")
    for hid, cfg, m in summary:
        print(f"{hid:<8} {cfg:<14} "
              f"{m.get('Diff rules proven', '-'):<5} "
              f"{m.get('Linear rules proven', '-'):<5} "
              f"{m.get('Collatz rules', '-'):<5} "
              f"{m.get('Exponential rules proven', '-'):<5} "
              f"{m.get('General rules proven', '-'):<5} "
              f"{m.get('Failed proofs', '-'):<6} "
              f"{m.get('Tape copies', '-'):<8} "
              f"{m.get('Num Nonzeros', '-'):<10}")


if __name__ == "__main__":
    main()
