#!/usr/bin/env python3
"""Probe 397's stack-like edit structure.

The substitution-hunt (bb33_397_substitution.py) showed that 397's
left-side macro word evolves by Delta(len) = +/-1 in ~95% of macro-
steps. This refutes the substitution hypothesis from notes/12 and
suggests a stack/pushdown structure: at each macro-step, one symbol
is pushed or popped near the boundary with the growing right block.

This script characterizes:
  - WHERE the edit happens (which position?)
  - WHAT is pushed/popped (which symbol?)
  - Does the edit pattern repeat? (push-pop alternation period?)
  - Is the "non-edited" portion fully stable (sweep prefix) or does
    it have its own slow drift?
"""

import argparse
import os
import sys
from collections import Counter, defaultdict
from pathlib import Path

SCRIPT_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/tools/sandbox"))
sys.path.insert(0, str(SCRIPT_DIR))
from bb33_complexity import parse_configs, token_to_symbol  # noqa: E402

SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))


def load_words(trace_path, side="left", limit=None):
    words = []
    for left, head, right in parse_configs(trace_path):
        chosen = left if side == "left" else right
        words.append(tuple(token_to_symbol(t) for t in chosen))
        if limit is not None and len(words) >= limit:
            break
    return words


def edit_diagnosis(W, Wp):
    """Given consecutive words, return (kind, pos, symbol) describing
    the edit. kind in {'push', 'pop', 'replace', 'same', 'complex'}.
    pos is the position of the edit (in Wp for push, in W for pop, in
    both for replace). symbol is the inserted/removed symbol."""
    if W == Wp:
        return ("same", None, None)
    dl = len(Wp) - len(W)
    if dl == 0 and len(W) > 0:
        # one-symbol replace?
        diffs = [i for i in range(len(W)) if W[i] != Wp[i]]
        if len(diffs) == 1:
            return ("replace", diffs[0], (W[diffs[0]], Wp[diffs[0]]))
        return ("complex", len(diffs), None)
    if dl == 1:
        # Find longest common prefix and suffix
        p = 0
        while p < len(W) and W[p] == Wp[p]:
            p += 1
        s = 0
        while s < len(W) - p and W[-1 - s] == Wp[-1 - s]:
            s += 1
        # If p + s == len(W), then Wp has W with one extra symbol at position p
        if p + s == len(W):
            return ("push", p, Wp[p])
        return ("complex", None, None)
    if dl == -1:
        p = 0
        while p < len(Wp) and W[p] == Wp[p]:
            p += 1
        s = 0
        while s < len(Wp) - p and W[-1 - s] == Wp[-1 - s]:
            s += 1
        if p + s == len(Wp):
            # W has the extra symbol at position p
            return ("pop", p, W[p])
        return ("complex", None, None)
    return ("complex", None, None)


def analyze(words, max_pairs=10000):
    print(f"\nAnalyzing {min(max_pairs, len(words)-1)} consecutive pairs")

    kinds = Counter()
    push_positions = Counter()  # position from RIGHT end (so 0 = end)
    pop_positions = Counter()
    push_symbols = Counter()
    pop_symbols = Counter()
    push_pos_abs = Counter()  # absolute position from left
    pop_pos_abs = Counter()
    push_sym_by_pos = defaultdict(Counter)  # symbol at position from right
    pop_sym_by_pos = defaultdict(Counter)
    complex_examples = []

    for t in range(min(max_pairs, len(words) - 1)):
        W = words[t]
        Wp = words[t+1]
        kind, pos, sym = edit_diagnosis(W, Wp)
        kinds[kind] += 1
        if kind == "push":
            push_positions[len(Wp) - 1 - pos] += 1  # from right
            push_pos_abs[pos] += 1
            push_symbols[sym] += 1
            push_sym_by_pos[len(Wp) - 1 - pos][sym] += 1
        elif kind == "pop":
            pop_positions[len(W) - 1 - pos] += 1
            pop_pos_abs[pos] += 1
            pop_symbols[sym] += 1
            pop_sym_by_pos[len(W) - 1 - pos][sym] += 1
        elif kind == "complex":
            if len(complex_examples) < 5:
                complex_examples.append((t, W, Wp))

    total = sum(kinds.values())
    print(f"\nEdit kind distribution:")
    for k, c in kinds.most_common():
        print(f"  {k}: {c} ({100*c/total:.1f}%)")

    print(f"\n=== PUSH analysis ({sum(push_positions.values())} pushes) ===")
    print(f"Position from RIGHT end (0 = last position):")
    for r in sorted(push_positions.keys())[:8]:
        print(f"  pos -{r}: {push_positions[r]} pushes "
              f"({100*push_positions[r]/sum(push_positions.values()):.1f}%) "
              f"-- symbols at this slot: {dict(push_sym_by_pos[r].most_common())}")
    print(f"Symbols pushed (overall): {dict(push_symbols.most_common())}")

    print(f"\n=== POP analysis ({sum(pop_positions.values())} pops) ===")
    print(f"Position from RIGHT end (0 = last position):")
    for r in sorted(pop_positions.keys())[:8]:
        print(f"  pos -{r}: {pop_positions[r]} pops "
              f"({100*pop_positions[r]/sum(pop_positions.values()):.1f}%) "
              f"-- symbols at this slot: {dict(pop_sym_by_pos[r].most_common())}")
    print(f"Symbols popped (overall): {dict(pop_symbols.most_common())}")

    if complex_examples:
        print(f"\n=== COMPLEX edit examples ===")
        for t, W, Wp in complex_examples:
            print(f"  t={t}: |W|={len(W)} -> |W'|={len(Wp)}")
            print(f"    W  = {' '.join(W)}")
            print(f"    W' = {' '.join(Wp)}")


def stack_evolution_trace(words, start=100, length=40):
    """Show how the stack evolves over a small window: print word
    lengths and the edit at each step. Helps eyeball the pattern."""
    print(f"\n=== Stack-evolution trace (t={start}..{start+length-1}) ===")
    for t in range(start, min(start + length, len(words) - 1)):
        W = words[t]
        Wp = words[t+1]
        kind, pos, sym = edit_diagnosis(W, Wp)
        if kind == "push":
            mark = f"+{sym} @ pos {pos} (={len(Wp)-1-pos} from right)"
        elif kind == "pop":
            mark = f"-{sym} @ pos {pos} (={len(W)-1-pos} from right)"
        elif kind == "replace":
            mark = f"~{sym[0]}->{sym[1]} @ pos {pos}"
        elif kind == "same":
            mark = "(no change)"
        else:
            mark = "COMPLEX"
        print(f"  t={t:4d}: |W|={len(W):3d}  {mark}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace",
                        default=str(SIM_DIR / "complexity_397_b2_l200000.txt"))
    parser.add_argument("--side", default="left")
    parser.add_argument("--limit", type=int, default=20000)
    parser.add_argument("--max-pairs", type=int, default=20000)
    args = parser.parse_args()
    trace_path = Path(args.trace)
    print(f"Loading trace: {trace_path}")
    words = load_words(trace_path, side=args.side, limit=args.limit)
    print(f"Loaded {len(words)} words")
    analyze(words, max_pairs=args.max_pairs)
    stack_evolution_trace(words, start=200, length=30)


if __name__ == "__main__":
    main()
