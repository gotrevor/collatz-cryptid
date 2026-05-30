#!/usr/bin/env python3
"""Map reachable (pat, a, b mod M) states + k_min per (pat, a) over V6 orbit.

Goal: determine whether reachable b mod M at small a is a FINITE set —
which would let us state the cascade-closing invariants as InvB clauses
of the form "P1 ∧ a = X → b mod M ∈ S" for specific (X, M, S).

Output per (pat, a):
  - distinct b mod 12 residues observed
  - distinct b mod 24 residues observed
  - k_min observed at this (pat, a)
  - count of visits
"""

import sys
from pathlib import Path
from collections import defaultdict

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bigfoot_v6_pure_rule import step, INITIAL


def run_collect(n_cycles, a_max=30):
    """Run V6 for n_cycles, collect b residues + k_min per (pat, a)."""
    state = INITIAL
    # state_data[(pat, a)] = {
    #   'b_mod12': set, 'b_mod24': set, 'k_min': int,
    #   'count': int, 'sample_b': list[int]
    # }
    data = defaultdict(lambda: {
        'b_mod12': set(), 'b_mod24': set(), 'b_mod48': set(),
        'k_min': float('inf'),
        'count': 0,
        'b_samples': []  # first few b values
    })

    def record(s):
        k, a, b, pat = s
        if a > a_max:
            return
        d = data[(pat, a)]
        d['b_mod12'].add(b % 12)
        d['b_mod24'].add(b % 24)
        d['b_mod48'].add(b % 48)
        if k < d['k_min']:
            d['k_min'] = k
        d['count'] += 1
        if len(d['b_samples']) < 10:
            d['b_samples'].append((k, b))

    record(state)

    for _ in range(n_cycles):
        result = step(state)
        if result[0] is None:
            print(f"** HALT: {state}")
            return None
        state, _ = result
        record(state)

    return data


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000_000
    a_max = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    print(f"\n===== V6 reachable b-residues + k_min: {n:,} cycles, a ≤ {a_max} =====\n")

    data = run_collect(n, a_max=a_max)
    if data is None:
        return

    # Print P1 states first, then P2
    for pat_filter in ['P1', 'P2']:
        print(f"\n=== {pat_filter} states ===")
        keys = sorted([(p, a) for (p, a) in data if p == pat_filter])
        if not keys:
            print(f"  (none with a ≤ {a_max})")
            continue
        print(f"  {'(pat, a)':<10}  {'count':>10}  {'k_min':>5}  "
              f"{'b%12':<30}  {'b%24':<40}  {'first b samples (k, b)'}")
        for (pat, a) in keys:
            d = data[(pat, a)]
            mod12 = sorted(d['b_mod12'])
            mod24 = sorted(d['b_mod24'])
            samples = ", ".join(f"({k},{b})" for k, b in d['b_samples'][:3])
            print(f"  ({pat}, {a:>2})    {d['count']:>10}  {d['k_min']:>5}  "
                  f"{str(mod12):<30}  {str(mod24):<40}  {samples}")


if __name__ == "__main__":
    main()
