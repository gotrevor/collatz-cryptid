#!/usr/bin/env python3
"""Verify the V6 ↔ Shawn algebraic bijection.

Conjecture from bigfoot_compare_v6_shawn.py output: at every Shawn boundary
S = (a_s, b_s, c_s), the V6 state at the NEXT V6 super-cycle is

    V_after(S) = (k = a_s, a_v = 2*b_s - 1, b_v = 2*c_s + 1, pat = P1)

This script:
  1. Iterates Shawn Dyn from initial.
  2. Maps each Shawn state to a V6 state via the bijection.
  3. Iterates V6 pure rule from initial.
  4. For each Shawn step, finds the corresponding V6 step in the orbit and
     confirms the bijection holds.
  5. Records how many V6 super-cycles per Shawn step.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bigfoot_shawn_dyn import shawn_step, INITIAL as SHAWN_INIT
from bigfoot_v6_pure_rule import step as v6_step, INITIAL as V6_INIT


def phi(a_s, b_s, c_s):
    """Map Shawn (a, b, c) to V6 (k, a, b, pat) per the conjectured bijection."""
    return (a_s, 2 * b_s - 1, 2 * c_s + 1, "P1")


def main():
    # Walk Shawn forward, record states.
    shawn_states = [SHAWN_INIT]
    s = SHAWN_INIT
    for _ in range(20):
        result, _ = shawn_step(s)
        if result is None:
            break
        s = result
        shawn_states.append(s)

    # Walk V6 forward, record states.
    v6_states = [V6_INIT]
    v = V6_INIT
    for _ in range(60):
        result, _ = v6_step(v)
        if result is None:
            break
        v = result
        v6_states.append(v)

    # For each Shawn state, find its expected V6 state and search for it in the orbit.
    print(f"{'#':>3} {'Shawn (a,b,c)':<18} {'φ → V6':<28} {'found at V step':<16} {'Δ from prev':<10}")
    prev_idx = -1
    for i, ss in enumerate(shawn_states):
        target = phi(*ss)
        found = None
        for j in range(prev_idx + 1, len(v6_states)):
            if v6_states[j] == target:
                found = j
                break
        delta = (found - prev_idx) if (found is not None and prev_idx >= 0) else "—"
        print(f"{i:>3}  {str(ss):<18} {str(target):<28} "
              f"{str(found):<16} {delta}")
        if found is not None:
            prev_idx = found

    # Reverse direction: which V6 states map back to a Shawn state?
    print("\n--- V6 states (first 25) ---")
    for j, vs in enumerate(v6_states[:25]):
        k, a_v, b_v, pat = vs
        if pat == "P1" and a_v % 2 == 1 and b_v % 2 == 1:
            a_s = k
            b_s = (a_v + 1) // 2
            c_s = (b_v - 1) // 2
            print(f"  V step {j:>2}: {vs}  invertible → Shawn ({a_s},{b_s},{c_s})")
        else:
            print(f"  V step {j:>2}: {vs}  (not invertible)")


if __name__ == "__main__":
    main()
