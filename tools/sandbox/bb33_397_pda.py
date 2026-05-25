#!/usr/bin/env python3
"""Test 397 as a deterministic pushdown automaton (PDA).

We have established:
  - All edits to 397's left-side word are at the RIGHT boundary.
  - Edit kinds: push / pop / replace-top / no-change.

This is the signature of a stack machine. To make 397 *decidable* we
need the next action to be a deterministic function of (some finite
amount of) state visible to the stack. The natural candidates:

  - The TOP k symbols of the stack.
  - Plus possibly a finite "control" state (residue mod some K).

If the action is deterministic as a function of TOP_k for some small
k, the stack evolution is a deterministic pushdown system over a
finite alphabet, and reachability / non-halting can be analyzed via
known algorithms (DPDA emptiness, saturated graphs of stack contents,
or summarization-based fixed-point computation).

We sweep k = 1, 2, 3, 4, ... and at each k, check the conditional
entropy of the next action given the top-k. Goal: find smallest k for
which the action is deterministic (zero conflicts).
"""

import argparse
import os
import sys
from collections import Counter, defaultdict
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


def action_of(W, Wp):
    """Return a canonical action token describing the edit."""
    kind, pos, sym = edit_diagnosis(W, Wp)
    if kind == "push":
        return ("push", sym)
    if kind == "pop":
        return ("pop", sym)
    if kind == "replace":
        return ("replace", sym)
    if kind == "same":
        return ("same",)
    return ("complex", pos)


def conditional_determinism(words, k, max_pairs):
    """Group transitions by top-k symbols of W. For each group, what
    actions occur? Conflict count = sum over groups of (|distinct
    actions in group| - 1)."""
    by_top = defaultdict(Counter)
    for t in range(min(max_pairs, len(words) - 1)):
        W = words[t]
        Wp = words[t+1]
        if len(W) < k:
            continue
        top = W[-k:] if k > 0 else ()
        act = action_of(W, Wp)
        by_top[top][act] += 1

    n_groups = len(by_top)
    n_transitions = sum(sum(c.values()) for c in by_top.values())
    deterministic_groups = sum(1 for c in by_top.values() if len(c) == 1)
    nondeterministic_groups = n_groups - deterministic_groups
    # "Conflicts" = transitions that disagree with the majority action in their group
    total_conflicts = 0
    for top, acts in by_top.items():
        if len(acts) > 1:
            mc = acts.most_common(1)[0][1]
            total_conflicts += sum(acts.values()) - mc
    print(f"\n  k={k}: {n_groups} distinct top-{k} contexts, "
          f"{n_transitions} transitions")
    print(f"    deterministic contexts: {deterministic_groups}/{n_groups} "
          f"({100*deterministic_groups/max(n_groups,1):.1f}%)")
    print(f"    minority transitions (= conflicts): "
          f"{total_conflicts}/{n_transitions} "
          f"({100*total_conflicts/max(n_transitions,1):.2f}%)")

    if nondeterministic_groups and nondeterministic_groups <= 8:
        print(f"    nondeterministic contexts:")
        for top, acts in by_top.items():
            if len(acts) > 1:
                fmt_top = ' '.join(top)
                fmt_acts = ', '.join(f"{a!s}:{c}" for a, c in acts.most_common())
                print(f"      top=[{fmt_top}]: {fmt_acts}")
    elif nondeterministic_groups:
        # Print 5 worst
        print(f"    top 5 most-conflicted contexts:")
        worst = sorted(by_top.items(),
                       key=lambda kv: sum(kv[1].values()) - kv[1].most_common(1)[0][1],
                       reverse=True)[:5]
        for top, acts in worst:
            fmt_top = ' '.join(top)
            fmt_acts = ', '.join(f"{a!s}:{c}" for a, c in acts.most_common())
            print(f"      top=[{fmt_top}]: {fmt_acts}")
    return total_conflicts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace",
                        default=str(SIM_DIR / "complexity_397_b2_l200000.txt"))
    parser.add_argument("--side", default="left")
    parser.add_argument("--limit", type=int, default=50000)
    parser.add_argument("--max-pairs", type=int, default=50000)
    parser.add_argument("--k-max", type=int, default=8)
    args = parser.parse_args()

    trace_path = Path(args.trace)
    print(f"Loading trace: {trace_path}")
    words = load_words(trace_path, side=args.side, limit=args.limit)
    print(f"Loaded {len(words)} words")

    print(f"\n== Deterministic-PDA test ==")
    print(f"Question: for each k, is the next action a deterministic function "
          f"of the top-k stack symbols?")
    for k in range(1, args.k_max + 1):
        conditional_determinism(words, k, args.max_pairs)


if __name__ == "__main__":
    main()
