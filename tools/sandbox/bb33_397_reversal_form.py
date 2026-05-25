#!/usr/bin/env python3
"""Extract sweep-reversal configurations for holdout 397 and look for
the parametric (a, b, c)-style reduction.

Observation from trace:
  loop  100:  ... <C (20) 21^1 00^inf       (right side: (2220)^0 21)
  loop 1000:  ... <C (20) (2220)^6 21^1 00^inf

So the right side has explicit form `(2220)^N 21^1 00^inf` with N a
counter. At sweep-reversal moments, the head is at <C (20) sitting
just left of this right block.

The left stack is the irregular word W we've been studying. The
question: is W at sweep-reversal moments a *parametric* function of
some small finite number of integers - i.e., does 397 admit a clean
Bigfoot-style 3-counter reduction?

This script:
  1. Parses each indexed config line ('     K  <config> (s, t)').
  2. For each macro-loop, extracts (head_state, head_dir, cell, left_word,
     right_word, right_counter_N).
  3. Detects sweep-reversal points by Delta(|left_word|) sign change.
  4. Reports the reversal configurations in a parametric-friendly form.
"""

import argparse
import os
import re
import sys
from collections import Counter
from pathlib import Path

SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))

# Indexed config line:
#   "     K  00^inf <tokens> 00^inf (steps_in_loop, total_steps)"
INDEXED = re.compile(
    r"^\s*(\d+)\s+0+\^inf\s+(.+?)\s+0+\^inf\s+\((\d+),\s*(\d+)\)\s*$"
)
BLOCK = re.compile(r"^([0-9]+)\^[\d_]+$")
CELL = re.compile(r"^\(([0-9]+)\)$")
HEAD_LEFT = re.compile(r"^<([ABC])$")
HEAD_RIGHT = re.compile(r"^([ABC])>$")


def block_count(token):
    """For a token like '22^1' or '22^1_234', return the integer count.
    Underscores are thousand separators."""
    m = BLOCK.match(token)
    if not m:
        return None
    suffix = token.split("^")[1].replace("_", "")
    return int(suffix)


def parse_config(tokens):
    """Return (head_state, head_dir, cell, left_tokens, right_tokens)
    or None if structure unrecognized."""
    for i, t in enumerate(tokens):
        m = HEAD_LEFT.match(t)
        if m:
            # <X (Y) ...
            if i + 1 < len(tokens) and CELL.match(tokens[i+1]):
                cell = CELL.match(tokens[i+1]).group(1)
                return (m.group(1), "<", cell, tokens[:i], tokens[i+2:])
        m = HEAD_RIGHT.match(t)
        if m:
            # ... (Y) X>
            if i > 0 and CELL.match(tokens[i-1]):
                cell = CELL.match(tokens[i-1]).group(1)
                return (m.group(1), ">", cell, tokens[:i-1], tokens[i+1:])
    return None


def count_right_pattern(right_tokens, pattern=("22", "20")):
    """Count maximal prefix '(22)(20)'-pairs from the start of the
    right side, then return (count_N, suffix_tokens)."""
    n = 0
    i = 0
    while i + len(pattern) <= len(right_tokens):
        ok = True
        for j, sym in enumerate(pattern):
            m = BLOCK.match(right_tokens[i + j])
            if not m or m.group(1) != sym:
                ok = False
                break
        if ok:
            # Verify counts are 1 each
            if all(block_count(right_tokens[i + j]) == 1 for j in range(len(pattern))):
                n += 1
                i += len(pattern)
            else:
                break
        else:
            break
    return n, right_tokens[i:]


def parse_trace(path):
    """Yield (loop_index, head_state, head_dir, cell, left_tokens,
    right_tokens) for each indexed config line."""
    with open(path) as f:
        for line in f:
            m = INDEXED.match(line)
            if not m:
                continue
            k = int(m.group(1))
            tokens = m.group(2).split()
            parsed = parse_config(tokens)
            if parsed is None:
                continue
            head_state, head_dir, cell, left, right = parsed
            yield k, head_state, head_dir, cell, left, right


def token_to_symbol(t):
    m = BLOCK.match(t)
    if m:
        return m.group(1)
    m = CELL.match(t)
    if m:
        return m.group(1)
    return t


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace",
                        default=str(SIM_DIR / "complexity_397_b2_l200000.txt"))
    parser.add_argument("--max-reversals", type=int, default=40)
    parser.add_argument("--max-loops", type=int, default=200000)
    args = parser.parse_args()

    trace = Path(args.trace)
    configs = []
    head_signatures = Counter()
    for k, hs, hd, cell, left, right in parse_trace(trace):
        if k > args.max_loops:
            break
        head_signatures[(hs, hd, cell)] += 1
        # Convert left/right to symbol sequences for length tracking
        left_syms = [token_to_symbol(t) for t in left]
        right_syms = [token_to_symbol(t) for t in right]
        N, right_suffix = count_right_pattern(right)
        configs.append({
            "k": k,
            "head": (hs, hd, cell),
            "left": tuple(left_syms),
            "right_N": N,
            "right_suffix": tuple(token_to_symbol(t) for t in right_suffix),
            "right_full": right,
        })

    print(f"Parsed {len(configs)} configs from {trace.name}")
    print(f"\nHead-signature distribution (top 10):")
    for sig, c in head_signatures.most_common(10):
        print(f"  {sig}: {c}")

    # Detect sweep reversals: a transition where d|left| changes sign,
    # OR equivalently where the macro-loop's edit-type changes.
    # We'll detect by left-length: a reversal happens at a local extremum.
    print(f"\n=== Sweep-reversal extraction ===")
    reversals = []
    for i in range(1, len(configs) - 1):
        a = len(configs[i-1]["left"])
        b = len(configs[i]["left"])
        c = len(configs[i+1]["left"])
        if (b > a and b > c) or (b < a and b < c):
            reversals.append(i)
        elif b == a and b > c:
            reversals.append(i)
        elif b == c and b > a:
            reversals.append(i)
    print(f"  {len(reversals)} reversal points detected")

    # Categorize: peaks (local max in |left|) = end-of-push / valleys (local min) = end-of-pop
    peaks = []
    valleys = []
    for i in reversals:
        a = len(configs[i-1]["left"])
        b = len(configs[i]["left"])
        c = len(configs[i+1]["left"])
        if b >= a and b >= c:
            peaks.append(i)
        elif b <= a and b <= c:
            valleys.append(i)
    print(f"  peaks (end-of-push): {len(peaks)}")
    print(f"  valleys (end-of-pop): {len(valleys)}")

    # Show first N peaks
    print(f"\n=== First {args.max_reversals} PEAK configurations ===")
    for j, i in enumerate(peaks[:args.max_reversals]):
        c = configs[i]
        right_suffix_str = ' '.join(c["right_suffix"]) if c["right_suffix"] else "(empty)"
        print(f"  cycle {j+1} (loop {c['k']:6d}): "
              f"head={c['head']!s:18s}  "
              f"|left|={len(c['left']):4d}  "
              f"right=N={c['right_N']:4d} · {right_suffix_str}")

    print(f"\n=== First {min(10, len(peaks))} PEAK left-stack words ===")
    for j, i in enumerate(peaks[:10]):
        c = configs[i]
        print(f"\n  cycle {j+1} (loop {c['k']}, |left|={len(c['left'])}):")
        print(f"    left = {' '.join(c['left'])}")

    print(f"\n=== First {args.max_reversals} VALLEY configurations ===")
    for j, i in enumerate(valleys[:args.max_reversals]):
        c = configs[i]
        right_suffix_str = ' '.join(c["right_suffix"]) if c["right_suffix"] else "(empty)"
        print(f"  cycle {j+1} (loop {c['k']:6d}): "
              f"head={c['head']!s:18s}  "
              f"|left|={len(c['left']):4d}  "
              f"right=N={c['right_N']:4d} · {right_suffix_str}")

    print(f"\n=== First {min(10, len(valleys))} VALLEY left-stack words ===")
    for j, i in enumerate(valleys[:10]):
        c = configs[i]
        print(f"\n  cycle {j+1} (loop {c['k']}, |left|={len(c['left'])}):")
        print(f"    left = {' '.join(c['left']) if c['left'] else '(empty)'}")

    # Right-counter N evolution at peaks and valleys
    print(f"\n=== N(cycle) trajectory at peaks ===")
    peak_Ns = [configs[i]["right_N"] for i in peaks]
    valley_Ns = [configs[i]["right_N"] for i in valleys]
    print(f"  peaks: N evolution (first 30): {peak_Ns[:30]}")
    print(f"  valleys: N evolution (first 30): {valley_Ns[:30]}")
    if peak_Ns:
        deltas = [peak_Ns[i+1] - peak_Ns[i] for i in range(len(peak_Ns)-1)]
        dc = Counter(deltas)
        print(f"\n  N peak-to-peak deltas (top 5): {dc.most_common(5)}")


if __name__ == "__main__":
    main()
