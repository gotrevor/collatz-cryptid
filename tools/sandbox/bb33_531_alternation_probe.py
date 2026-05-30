#!/usr/bin/env -S uv run python3
"""Test the 'alternating prefix + suffix-anchor' hypothesis for 531's
R-bootstrap word language.

The top-5 most-frequent R-bootstrap words at 531 peaks (notes/21) look
like:

    ()             — empty
    (20)           — just the anchor
    (12 20)        — single-step alternation
    (21 12 20)     — two-step alternation starting with 21
    (12 21 12 20)  — three-step alternation starting with 12
    (21 12 21 12 20) — four-step alternation starting with 21

This script tests how much of the full distinct-word language fits the
pattern  (12 | 21)*  [12]?  20  (or equivalently, an arbitrary number of
alternating 12/21 followed by terminal 20), and characterizes the
*non-fitting* words by which "rare" symbols they contain (22, 11, 10).

Output: by-occurrence-count breakdown (a single common word counts more
than a thousand rare ones).
"""

import argparse
import json
import re
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
                pattern = tuple(syms[start:start + p])
                best = (p, start, run_len, pattern)
    return best


def decompose_right(side_tokens, max_period=4):
    """Return (bootstrap, periodic body, cap) for the right side."""
    if len(side_tokens) < 4:
        return tuple(tok_sym(t) for t in side_tokens)
    period, start, run_len, _ = find_longest_periodic_window(side_tokens, max_period)
    if period is None or run_len < 2:
        return tuple(tok_sym(t) for t in side_tokens)
    return tuple(tok_sym(t) for t in side_tokens[start + run_len:])


def split_left_right(tokens):
    for i, t in enumerate(tokens):
        if t.startswith("<") and i + 1 < len(tokens):
            return tokens[:i], tokens[i + 2:]
        if t.endswith(">") and i > 0:
            return tokens[:i - 1], tokens[i + 1:]
    return None, None


def classify(word):
    """Return one of: 'alt' (matches alternation pattern), 'rare' (contains
    22/11/10), 'other' (no rare syms but doesn't match alternation), 'empty'."""
    if not word:
        return "empty"
    rare = {"22", "11", "10"}
    if any(s in rare for s in word):
        return "rare"
    # Check alternation pattern: (12|21)* (12)? 20
    # Equivalently: word[-1] == '20', and word[:-1] is strict (12,21)-alternation
    if word[-1] != "20":
        return "other"
    prefix = word[:-1]
    if any(s not in {"12", "21"} for s in prefix):
        return "other"
    # Check strict alternation (no two consecutive same)
    for i in range(len(prefix) - 1):
        if prefix[i] == prefix[i + 1]:
            return "other"
    return "alt"


def alt_subtype(word):
    """For alt-classified words, return (k, starts_with): k = number of
    leading 12/21 tokens, starts_with = first token (or 'terminal-only')."""
    if not word:
        return None
    prefix = word[:-1]
    k = len(prefix)
    if k == 0:
        return (0, "terminal-only")
    return (k, prefix[0])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp",
                    default=str(Path("~/src/collatz-cryptid/sim/531_burn_10M.reversals.json").expanduser()))
    ap.add_argument("--kind", choices=("peaks", "valleys", "both"), default="both")
    args = ap.parse_args()

    data = json.load(open(args.inp))
    kinds = ("peaks", "valleys") if args.kind == "both" else (args.kind,)

    for kind in kinds:
        snapshots = data[kind]
        word_count = Counter()
        for s in snapshots:
            _, right = split_left_right(s["tokens"])
            if right is None:
                continue
            word_count[decompose_right(right)] += 1

        by_class_distinct = Counter()
        by_class_occurrences = Counter()
        alt_subtypes_distinct = Counter()
        alt_subtypes_occurrences = Counter()
        rare_examples = []
        other_examples = []

        for word, cnt in word_count.items():
            cls = classify(word)
            by_class_distinct[cls] += 1
            by_class_occurrences[cls] += cnt
            if cls == "alt":
                sub = alt_subtype(word)
                alt_subtypes_distinct[sub] += 1
                alt_subtypes_occurrences[sub] += cnt
            elif cls == "rare" and len(rare_examples) < 5:
                rare_examples.append((word, cnt))
            elif cls == "other" and len(other_examples) < 5:
                other_examples.append((word, cnt))

        total_dist = sum(by_class_distinct.values())
        total_occ = sum(by_class_occurrences.values())
        print(f"\n========== {kind.upper()} ==========")
        print(f"  Total distinct words: {total_dist}")
        print(f"  Total occurrences:    {total_occ}")
        print()
        print(f"  By class (distinct / occurrences):")
        for cls in ("empty", "alt", "rare", "other"):
            d = by_class_distinct[cls]
            o = by_class_occurrences[cls]
            print(f"    {cls:8s}  {d:5d} distinct ({100*d/total_dist:5.1f}%)  "
                  f"{o:6d} occurrences ({100*o/total_occ:5.1f}%)")
        print()
        print(f"  Alt-subtype breakdown (k, starts_with) → (distinct, occurrences):")
        for sub, cnt in sorted(alt_subtypes_distinct.items(), key=lambda x: x[0]):
            occ = alt_subtypes_occurrences[sub]
            print(f"    {sub}  →  {cnt} distinct, {occ} occurrences")
        if rare_examples:
            print()
            print(f"  Rare-symbol example words:")
            for w, c in rare_examples[:5]:
                print(f"    ({c}x) {' '.join(w)}")
        if other_examples:
            print()
            print(f"  Other (no-rare-but-not-alt) example words:")
            for w, c in other_examples[:5]:
                print(f"    ({c}x) {' '.join(w)}")


if __name__ == "__main__":
    main()
