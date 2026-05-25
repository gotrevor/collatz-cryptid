#!/usr/bin/env python3
"""Factor complexity analysis on BB(3,3) holdouts 397 and 531.

For each holdout:
  1. Run Quick_Sim with verbose-simulator, capture every config.
  2. Extract the "irregular side" block sequence as a word.
     - 397: LEFT side (right has growing homogeneous block).
     - 531: RIGHT side (left has growing homogeneous block).
  3. Compute factor complexity c(n) = number of distinct length-n subwords.
  4. Compare against canonical shapes:
        Sturmian:        c(n) = n + 1
        Periodic, p:     c(n) → p
        Substitutive:    c(n) polynomial
        Random over k:   c(n) → k^n
"""
import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from collections import Counter

PY = os.path.expanduser("~/.venvs/bb/bin/python")
QS = os.path.expanduser("~/src/busy-beaver/Code/Quick_Sim.py")
SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))


HOLDOUTS = {
    "397": ("1RB1LB2LC_1LA2RB1RB_---0LA2LA", "left"),
    "531": ("1RB2LA1LA_2LA0RA2RC_---0LC2RA", "right"),
}


CONFIG_LINE = re.compile(r"^0+\^inf\s+(.+?)\s+0+\^inf$")
BLOCK = re.compile(r"^([0-9]+)\^[\d_]+$")  # counts may contain underscores (1_001 etc.)
CELL = re.compile(r"^\(([0-9]+)\)$")
HEAD_LEFT = re.compile(r"^<([ABC])$")
HEAD_RIGHT = re.compile(r"^([ABC])>$")


def split_at_head(tokens):
    """Return (left_tokens, head_tokens, right_tokens)."""
    for i, t in enumerate(tokens):
        if HEAD_LEFT.match(t):
            # <X (YZ) - head occupies 2 tokens
            return tokens[:i], tokens[i:i + 2], tokens[i + 2:]
        if HEAD_RIGHT.match(t) and i > 0 and CELL.match(tokens[i - 1]):
            # (YZ) X> - head occupies tokens[i-1:i+1]
            return tokens[:i - 1], tokens[i - 1:i + 1], tokens[i + 1:]
    return tokens, [], []


def extract_irregular_side(config_str: str, side: str):
    """Pull out the block-label sequence of the 'irregular' side.

    Skip the homogeneous-block 'sweep target' if any. Returns list of
    (block_label, count) tuples - we keep counts for diagnostic but
    use just labels for complexity.
    """
    tokens = config_str.split()
    left, head, right = split_at_head(tokens)
    chosen = left if side == "left" else right
    # Drop the homogeneous-block target. For 397 the right has a `2022^N`
    # with large N; for 531 the left has `12^N` with large N. We just
    # take ALL block labels on the irregular side - the homogeneous
    # block isn't on the irregular side.
    out = []
    for t in chosen:
        m = BLOCK.match(t)
        if m:
            out.append(m.group(1))
            continue
        m = CELL.match(t)
        if m:
            out.append(m.group(1))
            continue
        # Skip head decorations like `<A` and `A>` if present (shouldn't be)
    return out


def run_long_trace(tm: str, label: str, max_loops: int, block_size: int = 2) -> Path:
    out_path = SIM_DIR / f"complexity_{label}_b{block_size}_l{max_loops}.txt"
    if out_path.exists() and out_path.stat().st_size > 1000:
        print(f"  cached: {out_path}")
        return out_path
    args = [
        PY, QS,
        "--recursive",
        "--verbose-simulator",
        "--print-loops", "1",
        "--max-loops", str(max_loops),
        "--block-size", str(block_size),
        tm,
    ]
    print(f"  running max_loops={max_loops}: {' '.join(args[2:])}", flush=True)
    r = subprocess.run(args, capture_output=True, text=True, timeout=600)
    out_path.write_text(r.stdout)
    return out_path


def parse_configs(trace_path: Path):
    """Yield (left, head, right) for each config line."""
    with open(trace_path) as f:
        for line in f:
            line = line.strip()
            m = CONFIG_LINE.match(line)
            if not m:
                continue
            middle = m.group(1)
            tokens = middle.split()
            left, head, right = split_at_head(tokens)
            yield left, head, right


def token_to_symbol(t: str):
    """Map a tape token to a block-label symbol (count stripped)."""
    m = BLOCK.match(t)
    if m:
        return m.group(1)
    m = CELL.match(t)
    if m:
        return m.group(1)
    return t  # fallback


def all_irregular_words(trace_path: Path, side: str):
    """Return a list of words (each a tuple of block labels), one per config."""
    words = []
    for left, head, right in parse_configs(trace_path):
        chosen = left if side == "left" else right
        words.append(tuple(token_to_symbol(t) for t in chosen))
    return words


def factor_complexity(word: tuple, max_n: int = 8) -> list:
    """c(n) = number of distinct length-n contiguous subwords of `word`."""
    L = len(word)
    result = []
    for n in range(1, max_n + 1):
        if n > L:
            result.append(None)
            continue
        factors = set()
        for i in range(L - n + 1):
            factors.add(word[i:i + n])
        result.append(len(factors))
    return result


def analyze(label: str, tm: str, side: str, max_loops_list=(2000, 10000, 50000)):
    print(f"\n=== {label} (irregular side: {side}) ===")
    for max_loops in max_loops_list:
        trace = run_long_trace(tm, label, max_loops)
        words = all_irregular_words(trace, side)
        if not words:
            print(f"  no configs parsed at max_loops={max_loops}")
            continue

        final = words[-1]
        alphabet = sorted(set(t for w in words for t in w))
        print(f"\n  max_loops={max_loops}")
        print(f"    configs parsed: {len(words)}")
        print(f"    final word length: {len(final)}")
        print(f"    alphabet ({len(alphabet)}): {alphabet}")
        print(f"    word-length growth: first={len(words[0])} mid={len(words[len(words)//2])} last={len(final)}")

        # Complexity function of final word
        c = factor_complexity(final, max_n=8)
        print(f"    c(n) of final word:")
        for n, cn in enumerate(c, start=1):
            if cn is None:
                continue
            k = len(alphabet)
            print(f"      c({n}) = {cn:5}   "
                  f"(Sturmian-shape n+1={n+1}, random {k}^n={k**n})")

        # How many distinct words across the whole trace?
        distinct_words = len(set(words))
        print(f"    distinct full words across trace: {distinct_words} / {len(words)}")

        # Are any words exact repeats?
        word_counts = Counter(words)
        repeats = [(w, c) for w, c in word_counts.most_common(3) if c > 1]
        if repeats:
            print(f"    top repeated words:")
            for w, c in repeats:
                print(f"      {c}×  len={len(w)}  {w[:8]}{'...' if len(w)>8 else ''}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-loops", type=int, nargs="+",
                        default=[2000, 10000, 50000],
                        help="Loop budgets to try")
    parser.add_argument("--holdout", choices=list(HOLDOUTS.keys()) + ["all"],
                        default="all")
    args = parser.parse_args()

    targets = HOLDOUTS if args.holdout == "all" else {args.holdout: HOLDOUTS[args.holdout]}
    for label, (tm, side) in targets.items():
        analyze(label, tm, side, max_loops_list=args.max_loops)


if __name__ == "__main__":
    main()
