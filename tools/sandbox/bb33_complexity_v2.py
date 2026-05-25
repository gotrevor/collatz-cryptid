#!/usr/bin/env python3
"""Per-snapshot complexity statistics across the whole trace.

Compute c(8) for each snapshot's irregular-side word. Look at the
distribution: max, mean, percentiles.

This refines the headline finding: 397's *final* word at 200k loops
had c(n) plateauing at 20. Does that hold across ALL snapshots, or
just the final one?
"""
import argparse
import re
import sys
from pathlib import Path
from bb33_complexity import (
    HOLDOUTS, SIM_DIR, run_long_trace,
    parse_configs, token_to_symbol, factor_complexity,
)


def per_snapshot_stats(label: str, tm: str, side: str, max_loops: int):
    trace = run_long_trace(tm, label, max_loops)
    words = []
    for left, head, right in parse_configs(trace):
        chosen = left if side == "left" else right
        words.append(tuple(token_to_symbol(t) for t in chosen))

    print(f"\n=== {label} side={side} max_loops={max_loops} ===")
    print(f"  total snapshots: {len(words)}")

    # Length distribution
    lens = [len(w) for w in words]
    print(f"  word length: min={min(lens)} max={max(lens)} mean={sum(lens)/len(lens):.1f}")

    # For words long enough to have factor c(n) defined, gather c(n) for various n
    for target_n in (3, 5, 8, 12):
        cn_values = []
        for w in words:
            if len(w) >= target_n:
                c = factor_complexity(w, max_n=target_n)
                cn_values.append(c[target_n - 1])
        if not cn_values:
            print(f"  c({target_n}): no words of sufficient length")
            continue
        cn_values.sort()
        n = len(cn_values)
        print(f"  c({target_n}) across {n} snapshots: "
              f"min={cn_values[0]} max={cn_values[-1]} "
              f"median={cn_values[n//2]} p90={cn_values[int(n*0.9)]} "
              f"p99={cn_values[int(n*0.99)]}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-loops", type=int, default=200000)
    parser.add_argument("--holdout", choices=list(HOLDOUTS.keys()) + ["all"],
                        default="all")
    args = parser.parse_args()
    targets = HOLDOUTS if args.holdout == "all" else {args.holdout: HOLDOUTS[args.holdout]}
    for label, (tm, side) in targets.items():
        per_snapshot_stats(label, tm, side, args.max_loops)


if __name__ == "__main__":
    main()
