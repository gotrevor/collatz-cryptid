#!/usr/bin/env python3
"""Sweep-run analysis for holdout 397.

Findings so far:
  - All edits at right boundary (pushdown).
  - Action (push/pop) NOT a function of top-k stack symbols (conflict
    rate ~50% even at k=6).
  - But: looking at consecutive transitions, pushes come in runs and
    pops come in runs (eyeball: t=200..230 showed pop-run length 6,
    then push-run length 8, then pop-run length 7).

If the underlying dynamics are a sweep TM, we expect:
  - Alternating runs of pushes (sweep extends stack) and pops (sweep
    retracts).
  - Run lengths may drift slowly (Collatz-like control).
  - The hidden state is the sweep direction, not visible in the stack
    contents alone.

This script characterizes run-length distribution and whether 397
admits a sweep-automaton model.
"""

import argparse
import os
import sys
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/tools/sandbox"))
sys.path.insert(0, str(SCRIPT_DIR))
from bb33_complexity import parse_configs, token_to_symbol  # noqa: E402
from bb33_397_stack_behavior import edit_diagnosis  # noqa: E402

SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))


def load_words(trace_path, side="left", limit=None):
    words = []
    for left, head, right in parse_configs(trace_path):
        chosen = left if side == "left" else right
        words.append(tuple(token_to_symbol(t) for t in chosen))
        if limit is not None and len(words) >= limit:
            break
    return words


def action_kind(W, Wp):
    kind, pos, sym = edit_diagnosis(W, Wp)
    if kind in ("push", "pop"):
        return kind
    # Treat same/replace/complex as "neutral" - count toward neither run
    return None


def find_runs(words, max_pairs):
    """Return list of (kind, length) tuples for maximal runs of pushes
    or pops, ignoring intervening 'neutral' steps."""
    actions = []
    for t in range(min(max_pairs, len(words) - 1)):
        k = action_kind(words[t], words[t+1])
        if k is not None:
            actions.append(k)

    runs = []
    if not actions:
        return runs
    cur_kind = actions[0]
    cur_len = 1
    for k in actions[1:]:
        if k == cur_kind:
            cur_len += 1
        else:
            runs.append((cur_kind, cur_len))
            cur_kind = k
            cur_len = 1
    runs.append((cur_kind, cur_len))
    return runs


def analyze_runs(runs):
    push_runs = [r[1] for r in runs if r[0] == "push"]
    pop_runs = [r[1] for r in runs if r[0] == "pop"]

    print(f"\n  Total runs: {len(runs)} (pushes: {len(push_runs)}, pops: {len(pop_runs)})")

    # Strict alternation check
    alternations = sum(1 for i in range(len(runs) - 1)
                       if runs[i][0] != runs[i+1][0])
    print(f"  Strict alternation: {alternations}/{len(runs)-1} run boundaries "
          f"({100*alternations/max(len(runs)-1,1):.1f}%)")

    for label, vals in (("push", push_runs), ("pop", pop_runs)):
        if not vals:
            continue
        vals_sorted = sorted(vals)
        n = len(vals_sorted)
        print(f"\n  {label}-run length: "
              f"min={vals_sorted[0]} max={vals_sorted[-1]} "
              f"mean={sum(vals)/n:.2f} "
              f"median={vals_sorted[n//2]} "
              f"p90={vals_sorted[int(n*0.9)]} "
              f"p99={vals_sorted[int(n*0.99)]}")
        # Histogram
        h = Counter(vals)
        print(f"    histogram (top 10 lengths):")
        for L, c in sorted(h.most_common(10)):
            print(f"      len={L:4d}: {c}")


def run_pair_drift(runs):
    """Look at consecutive (push-run, pop-run) pairs. Does (push - pop)
    drift slowly (martingale-like) or is it bounded?"""
    print(f"\n  Push-Pop run-length pairing:")
    pairs = []
    for i in range(len(runs) - 1):
        a, la = runs[i]
        b, lb = runs[i+1]
        if a == "push" and b == "pop":
            pairs.append((la, lb))
        elif a == "pop" and b == "push":
            pairs.append((lb, la))
    diffs = [p - q for p, q in pairs]
    if not diffs:
        return
    diffs_sorted = sorted(diffs)
    n = len(diffs_sorted)
    print(f"    pairs: {n}")
    print(f"    push-run - pop-run: "
          f"min={diffs_sorted[0]} max={diffs_sorted[-1]} "
          f"mean={sum(diffs)/n:.3f} median={diffs_sorted[n//2]}")
    print(f"    cumulative sum of (push-pop) per cycle is the net stack growth.")
    # Cumulative
    cum = 0
    cums = []
    for d in diffs:
        cum += d
        cums.append(cum)
    print(f"    cumulative net push after {n} cycles: {cums[-1]}")
    print(f"    rate (net push per cycle): {cums[-1]/n:.4f}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace",
                        default=str(SIM_DIR / "complexity_397_b2_l200000.txt"))
    parser.add_argument("--side", default="left")
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--max-pairs", type=int, default=200000)
    args = parser.parse_args()

    trace_path = Path(args.trace)
    print(f"Loading trace: {trace_path}")
    words = load_words(trace_path, side=args.side, limit=args.limit)
    print(f"Loaded {len(words)} words")

    print("\n== Sweep-run analysis ==")
    runs = find_runs(words, args.max_pairs)
    analyze_runs(runs)
    run_pair_drift(runs)

    # Show the first 20 runs explicitly
    print(f"\n  First 30 runs:")
    for kind, length in runs[:30]:
        print(f"    {kind:5s}  len={length}")


if __name__ == "__main__":
    main()
