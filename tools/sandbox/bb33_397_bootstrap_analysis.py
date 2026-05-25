#!/usr/bin/env python3
"""Analyze bootstrap words across all sweep-reversal snapshots.

For each reversal snapshot:
  - Decompose left side as [bootstrap] (P_left)^a [cap].
  - Decompose right side as [cap] (P_right)^b [bootstrap].
  - Record (head_sig, P_left, a, P_right, b, left_bootstrap, right_bootstrap).

Then per head signature:
  - Show the lookup-table (P_left, P_right) — are they constant?
  - Histogram bootstrap words — does the reachable set saturate or grow?
  - Are bootstraps the SAME at peaks vs valleys for the same head sig?
"""

import argparse
import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

BLOCK = re.compile(r"^([0-9]+)\^[\d_]+$")


def tok_sym(t):
    m = BLOCK.match(t)
    return m.group(1) if m else t


def find_longest_periodic_window(tokens, max_period=4):
    syms = [tok_sym(t) for t in tokens]
    n = len(syms)
    best = (None, None, 0, None)
    for p in range(1, max_period + 1):
        for start in range(max(0, n - p)):
            i = start
            while i + p < n and syms[i] == syms[i + p]:
                i += 1
            run_len = i - start + p
            if run_len > best[2]:
                pattern = tuple(syms[start:start+p])
                best = (p, start, run_len, pattern)
    return best


def decompose(side_tokens, side_name, max_period=4):
    if len(side_tokens) < 4:
        return {"period": None, "pattern": None, "N": 0, "body_len": 0,
                "bootstrap": tuple(tok_sym(t) for t in side_tokens), "cap": ()}
    period, start, run_len, pattern = find_longest_periodic_window(side_tokens, max_period)
    if period is None or run_len < 2:
        return {"period": None, "pattern": None, "N": 0, "body_len": 0,
                "bootstrap": tuple(tok_sym(t) for t in side_tokens), "cap": ()}
    if side_name == "left":
        bootstrap = tuple(tok_sym(t) for t in side_tokens[:start])
        cap = tuple(tok_sym(t) for t in side_tokens[start + run_len:])
    else:
        cap = tuple(tok_sym(t) for t in side_tokens[:start])
        bootstrap = tuple(tok_sym(t) for t in side_tokens[start + run_len:])
    N = run_len // period
    return {"period": period, "pattern": pattern, "body_len": run_len, "N": N,
            "bootstrap": bootstrap, "cap": cap}


def analyze(snapshots, label):
    by_head = defaultdict(list)
    for s in snapshots:
        sig = (s["head_dir"], s["head_state"], s["cell"])
        tokens = s["tokens"]
        # split at head
        i_head = None
        for i, t in enumerate(tokens):
            if t.startswith("<") or t.endswith(">"):
                i_head = i
                break
        if i_head is None:
            continue
        if tokens[i_head].startswith("<"):
            left = tokens[:i_head]
            right = tokens[i_head + 2:]
        else:
            left = tokens[:i_head - 1]
            right = tokens[i_head + 1:]
        L = decompose(left, "left")
        R = decompose(right, "right")
        by_head[sig].append((s["loop"], L, R))

    print(f"\n========== {label} snapshots: {len(snapshots)} total ==========")
    for sig in sorted(by_head.keys()):
        rows = by_head[sig]
        n_rows = len(rows)
        if n_rows < 5:
            continue
        # Pattern consistency
        P_left_set = Counter(r[1]["pattern"] for r in rows if r[1]["pattern"])
        P_right_set = Counter(r[2]["pattern"] for r in rows if r[2]["pattern"])
        # Bootstrap saturation
        L_boots = Counter(r[1]["bootstrap"] for r in rows)
        R_boots = Counter(r[2]["bootstrap"] for r in rows)
        # N evolution
        a_vals = [r[1]["N"] for r in rows]
        b_vals = [r[2]["N"] for r in rows]
        boot_lens = [len(r[1]["bootstrap"]) for r in rows]

        print(f"\n  Head <{sig[0]} {sig[1]}, cell={sig[2]}>  ({n_rows} snapshots)")
        print(f"    P_left:   {dict(P_left_set)}")
        print(f"    P_right:  {dict(P_right_set)}")
        print(f"    a (N_left)  range: [{min(a_vals)}, {max(a_vals)}]  "
              f"final: {a_vals[-1]}")
        print(f"    b (N_right) range: [{min(b_vals)}, {max(b_vals)}]  "
              f"final: {b_vals[-1]}")
        print(f"    L_bootstrap: {len(L_boots)} distinct words "
              f"({100*len(L_boots)/n_rows:.0f}% unique)  "
              f"length range [{min(boot_lens)},{max(boot_lens)}]")
        print(f"    R_bootstrap: {len(R_boots)} distinct words "
              f"({100*len(R_boots)/n_rows:.0f}% unique)")

        # Top bootstraps
        print(f"    Top L_bootstrap words (count, len, preview):")
        for boot, cnt in L_boots.most_common(3):
            preview = ' '.join(boot[:15]) + ('...' if len(boot) > 15 else '')
            print(f"      {cnt:3d}x  len={len(boot):2d}  {preview}")
        # Cumulative novelty: by snapshot index, how many distinct bootstraps seen?
        seen = set()
        novelty = []
        for r in rows:
            seen.add(r[1]["bootstrap"])
            novelty.append(len(seen))
        # Sample novelty curve
        ix = [int(n_rows * f / 10) for f in range(1, 11)]
        ix = sorted(set(min(i, n_rows - 1) for i in ix))
        print(f"    L_bootstrap novelty curve:")
        for i in ix:
            print(f"      after {i+1:4d} snapshots: {novelty[i]} distinct")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp",
                    default=str(Path(os.path.expanduser(
                        "~/src/collatz-cryptid/sim/397_reversals.json"))))
    args = ap.parse_args()
    d = json.load(open(args.inp))
    analyze(d["peaks"], "PEAKS")
    analyze(d["valleys"], "VALLEYS")


if __name__ == "__main__":
    main()
