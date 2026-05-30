#!/usr/bin/env python3
"""V6 k_pos cascade analysis: empirical structure of D-W and B-coll inputs.

Goal: test the hypothesis that D-W (a=3) and B-coll (a=9) input b values
are restricted to "safe" mod-N residue classes that lead to k-recovery
before another decrement. If so, the k_pos cascade in V6KPos.lean may
close with additional structural InvB clauses.

Output:
  - histograms of D-W/B-coll input b values mod 12, 24, 36
  - k trajectory min/max
  - distinct reachable (pat, a, b) states (ignoring k)
  - sequences of consecutive decrement firings without intervening Q-W/Q-kpp

Usage: sandbox bigfoot_v6_kpos_analysis.py [N_cycles]
"""

import sys
from pathlib import Path
from collections import Counter, defaultdict

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bigfoot_v6_pure_rule import step, INITIAL


def analyze(n_cycles, track_shapes=True):
    """Run V6 for n_cycles and tabulate decrement firings + k extremes."""
    state = INITIAL
    dw_firings = []            # list of (step, k, b)
    bcoll_firings = []         # list of (step, k, b)
    k_min = state[0]
    k_max = state[0]
    k_min_state = state
    shapes = set() if track_shapes else None  # (pat, a, b) ignoring k
    parity_violations = 0      # count of (a+b) odd
    ab_parity_set = set()      # observed (a+b) % 2

    if track_shapes:
        shapes.add((state[3], state[1], state[2]))
    ab_parity_set.add((state[1] + state[2]) % 2)

    decrement_rules = {"B-coll", "D-W"}
    increment_rules = {"Q-W", "Q-kpp"}

    # Track decrement gaps (decrement steps with no intervening increment)
    last_increment_step = 0
    decrements_since_increment = 0
    max_decrements_in_a_row = 0
    max_decrement_gap_state = None

    for cyc in range(1, n_cycles + 1):
        k, a, b, pat = state
        # Record decrement inputs BEFORE stepping
        if pat == "P1":
            if a == 3:
                dw_firings.append((cyc, k, b))
            elif a == 9:
                bcoll_firings.append((cyc, k, b))
        # Parity check
        if (a + b) % 2 != 0:
            parity_violations += 1
        ab_parity_set.add((a + b) % 2)

        result = step(state)
        if result[0] is None:
            print(f"** HALT at cycle {cyc}: state={state}, rule={result[1]}")
            return None
        state, rule = result

        if rule in decrement_rules:
            decrements_since_increment += 1
            if decrements_since_increment > max_decrements_in_a_row:
                max_decrements_in_a_row = decrements_since_increment
                max_decrement_gap_state = (cyc, state, rule)
        elif rule in increment_rules:
            decrements_since_increment = 0
            last_increment_step = cyc

        k_now = state[0]
        if k_now < k_min:
            k_min = k_now
            k_min_state = (cyc, state, rule)
        if k_now > k_max:
            k_max = k_now

        if track_shapes:
            shapes.add((state[3], state[1], state[2]))

    return {
        "dw_firings": dw_firings,
        "bcoll_firings": bcoll_firings,
        "k_min": k_min,
        "k_min_state": k_min_state,
        "k_max": k_max,
        "shapes": shapes,
        "max_decrements_in_a_row": max_decrements_in_a_row,
        "max_decrement_gap_state": max_decrement_gap_state,
        "final_state": state,
        "parity_violations": parity_violations,
        "ab_parity_set": ab_parity_set,
    }


def hist_mod(values, M):
    """Histogram of values mod M, returned as ordered list."""
    c = Counter(v % M for v in values)
    return [(r, c.get(r, 0)) for r in range(M)]


def print_mod_table(label, values, mods=(12, 24, 36, 48)):
    if not values:
        print(f"  {label}: (no firings)")
        return
    print(f"  {label}: {len(values)} firings, b range [{min(values)}, {max(values)}]")
    for M in mods:
        h = hist_mod(values, M)
        hit = [(r, n) for r, n in h if n > 0]
        miss = [r for r, n in h if n == 0]
        print(f"    mod {M:2d}: HIT residues = {[r for r, _ in hit]}")
        print(f"            MISSED         = {miss}")
        # show counts for hits
        for r, n in hit:
            pct = 100.0 * n / len(values)
            print(f"              r={r:2d}: {n:>8} ({pct:5.2f}%)")


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    print(f"\n===== V6 k_pos analysis: {n:,} cycles =====")
    print(f"Initial: {INITIAL}\n")

    res = analyze(n, track_shapes=(n <= 10_000_000))
    if res is None:
        return

    print(f"\n--- (a+b) parity invariant ---")
    print(f"  observed (a+b)%2 values: {sorted(res['ab_parity_set'])}")
    print(f"  parity violations: {res['parity_violations']}"
          f" {'✓ NONE — clean invariant' if res['parity_violations'] == 0 else '⚠️'}")

    print(f"\n--- k trajectory ---")
    print(f"  k_min: {res['k_min']}  at  {res['k_min_state']}")
    print(f"  k_max: {res['k_max']}")
    print(f"  final state: {res['final_state']}")
    print(f"  max consecutive decrements (no intervening Q-W/Q-kpp): "
          f"{res['max_decrements_in_a_row']}")
    if res['max_decrement_gap_state']:
        print(f"    last such gap ended at: {res['max_decrement_gap_state']}")

    if res['shapes'] is not None:
        dw_shapes = {(p, a, b) for (p, a, b) in res['shapes']
                     if p == 'P1' and a == 3}
        bcoll_shapes = {(p, a, b) for (p, a, b) in res['shapes']
                        if p == 'P1' and a == 9}
        print(f"\n--- distinct reachable (P, a, b) shapes ---")
        print(f"  total: {len(res['shapes'])}")
        print(f"  (P1, a=3, ·): {len(dw_shapes)} distinct b values, "
              f"first 20: {sorted(b for _, _, b in dw_shapes)[:20]}")
        print(f"  (P1, a=9, ·): {len(bcoll_shapes)} distinct b values, "
              f"first 20: {sorted(b for _, _, b in bcoll_shapes)[:20]}")

    print(f"\n--- D-W (a=3) firings (step, k, b, b%12) ---")
    for step_, kk, bb in res['dw_firings']:
        print(f"  step {step_:>10}  k={kk:>3}  b={bb:>15}  b%12={bb%12:>2}")

    print(f"\n--- B-coll (a=9) firings (step, k, b, b%12) ---")
    for step_, kk, bb in res['bcoll_firings']:
        print(f"  step {step_:>10}  k={kk:>3}  b={bb:>15}  b%12={bb%12:>2}")

    print(f"\n--- D-W input b mod 12 histogram ---")
    print_mod_table("D-W", [b for _, _, b in res['dw_firings']], mods=(12, 24))

    print(f"\n--- Cascade analysis: k at \"dangerous\" D-W firings ---")
    # b mod 12 = 5 → post-D-W chain ends at B-coll (transient k=k-2)
    # b mod 12 = 11 → post-D-W chain ends at D-W (sustained k=k-2)
    # Need k >= 3 at b%12=5 (so k-2 >= 1 transiently then recovers)
    # Need k >= 3 at b%12=11 AND further bound for next D-W
    dangerous5 = [(s, k, b) for s, k, b in res['dw_firings'] if b % 12 == 5]
    dangerous11 = [(s, k, b) for s, k, b in res['dw_firings'] if b % 12 == 11]
    print(f"  D-W with b%12 = 5 (→ post-chain B-coll, transient k=k-2):")
    for s, k, b in dangerous5:
        print(f"    step={s} k={k} b={b}  {'⚠️ k<3' if k < 3 else '✓ k>=3'}")
    print(f"  D-W with b%12 = 11 (→ post-chain D-W, sustained k=k-2):")
    for s, k, b in dangerous11:
        print(f"    step={s} k={k} b={b}  {'⚠️ k<3' if k < 3 else '✓ k>=3'}")


if __name__ == "__main__":
    main()
