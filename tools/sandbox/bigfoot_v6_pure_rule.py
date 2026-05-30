#!/usr/bin/env python3
"""Bigfoot v6: pure-rule iterator. No TM simulation.

The (k, a, b, pattern) recurrence derived in v5_stress is:

    P2(k, a, b)  ->  P1(k, a-4, b+4)

    P1, a even:
        a >= 4:   S       P1(k,   a-3,  b+5)
        a == 2:   W       P1(k,   b+4,  0)
        a == 0:   ???     (not yet seen)

    P1, a odd:
        a >= 11:  B       P1(k,   a-9,  b+11)
        a == 9:   B-coll  P1(k-1, 1,    b+12)
        a == 7:   Q-W     P1(k+1, b+7,  0)
        a == 5:   Q-same  P2(k,   b+7,  2)
        a == 3:   D-W     P1(k-1, b+7,  0)
        a == 1:   Q-kpp   P2(k+1, b,    3)

Each rule preserves footprint = 2k + a + b + (2 if P1 else 0) + 2,
incremented by 2 per cycle.

This iterator runs the rule alone (no TM). Verification against v5 (which
itself is verified against v1 at 200 cycles) happens at sparse checkpoints.

Use it to:
  - push to 100k, 1M, 10M cycles cheaply
  - confirm no anomalies emerge at large iteration counts
  - look for halt configurations
  - study orbital structure
"""

import sys
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path(__file__).resolve().parent))


def step(state):
    """Apply ONE rule step. state = (k, a, b, pat). Returns new state and rule name."""
    k, a, b, pat = state
    if pat == "P2":
        return (k, a - 4, b + 4, "P1"), "P2->P1"
    # P1
    if a % 2 == 0:
        if a >= 4:
            return (k, a - 3, b + 5, "P1"), "S"
        elif a == 2:
            return (k, b + 4, 0, "P1"), "W"
        elif a == 0:
            return None, "HALT (a=0 unknown)"
    else:
        if a >= 11:
            return (k, a - 9, b + 11, "P1"), "B"
        elif a == 9:
            return (k - 1, 1, b + 12, "P1"), "B-coll"
        elif a == 7:
            return (k + 1, b + 7, 0, "P1"), "Q-W"
        elif a == 5:
            return (k, b + 7, 2, "P2"), "Q-same"
        elif a == 3:
            return (k - 1, b + 7, 0, "P1"), "D-W"
        elif a == 1:
            return (k + 1, b, 3, "P2"), "Q-kpp"


# Initial state from v5 at cycle 5 (first stable P1 cycle that fits the rule)
# v5 output: C5  k=2 a=1 b=5  pat=P1
INITIAL = (2, 1, 5, "P1")


def run(initial, n_cycles, verify_against_v5=False, sparse_checkpoints=None):
    """Iterate the rule starting from `initial` for n_cycles.

    Returns dict with rule histogram, halt info, final state, optional
    list of (cycle, state) checkpoints.
    """
    state = initial
    rule_counts = Counter()
    states_log = [(0, state)]  # cycle 0 = initial
    halt_at = None
    for cyc in range(1, n_cycles + 1):
        result = step(state)
        if result[0] is None:
            halt_at = (cyc, state, result[1])
            print(f"\n** halt at cycle {cyc}: state={state}, rule={result[1]}")
            break
        state, rule = result
        rule_counts[rule] += 1
        if sparse_checkpoints and cyc in sparse_checkpoints:
            states_log.append((cyc, state))
    if halt_at is None:
        states_log.append((n_cycles, state))
    return {
        "final_state": state,
        "halt_at": halt_at,
        "rule_counts": rule_counts,
        "checkpoints": states_log,
    }


def verify_against_v5(n_cycles=200):
    """Sanity check: run pure rule alongside v5 simulator, compare at every cycle."""
    from bigfoot_v5_tape_inspect import BigfootV5
    from bigfoot_v5_extract import parse_tape

    bf = BigfootV5()
    bf.bootstrap_to_first_b_end()

    # Get v5's state for cycles 1..n_cycles
    v5_states = []
    for cyc in range(1, n_cycles + 1):
        info = bf.super_cycle_v4()
        if info is None:
            break
        parse = parse_tape(bf)
        if not parse["valid"]:
            v5_states.append((cyc, None, parse))
            continue
        v5_states.append((cyc, (parse["k"], parse["a"], parse["b"],
                                parse["pattern"]), None))

    # Build a map: cycle_number -> v5_state
    v5_map = {cyc: st for cyc, st, _ in v5_states if st is not None}
    # Find first stable cycle whose state matches our INITIAL
    start_cyc = None
    for cyc in sorted(v5_map.keys()):
        if v5_map[cyc] == INITIAL:
            start_cyc = cyc
            break
    if start_cyc is None:
        return False, f"v5 never reached INITIAL state {INITIAL}"
    print(f"  v5 reached INITIAL state {INITIAL} at cycle {start_cyc}")

    # Iterate the rule starting from cycle start_cyc, compare to v5 at each step
    state = INITIAL
    cyc = start_cyc
    n_check = 1  # cycle start_cyc itself is "checked" trivially
    n_mismatch = 0
    while cyc + 1 in v5_map:
        result = step(state)
        if result[0] is None:
            print(f"  rule halted at cycle {cyc+1}: {result[1]}")
            return n_mismatch == 0, f"halted after {n_check} cycles"
        state, _ = result
        cyc += 1
        v5_st = v5_map[cyc]
        if v5_st != state:
            n_mismatch += 1
            if n_mismatch <= 5:
                print(f"  MISMATCH at cycle {cyc}: v5={v5_st}, rule={state}")
        n_check += 1
    return n_mismatch == 0, f"{n_check} cycles checked, {n_mismatch} mismatches"


def main():
    print("===== Bigfoot v6: pure-rule iterator =====")
    print(f"INITIAL state: {INITIAL}\n")

    # Step 1: verify against v5 at 1000 cycles
    print("=== Step 1: verify rule matches v5 simulator over 1000 cycles ===")
    ok, msg = verify_against_v5(n_cycles=1000)
    print(f"  result: {'PASS' if ok else 'FAIL'} -- {msg}\n")
    if not ok:
        return

    # Step 2: push to 100k cycles with the pure rule
    print("=== Step 2: pure rule for 100,000 cycles ===")
    res = run(INITIAL, 100_000)
    print(f"  final state: {res['final_state']}")
    print(f"  halt: {res['halt_at']}")
    print(f"  rule counts:")
    for rule, n in res["rule_counts"].most_common():
        print(f"    {rule:>8}: {n:>7}")

    # Step 3: push to 1M cycles
    print("\n=== Step 3: pure rule for 1,000,000 cycles ===")
    res = run(INITIAL, 1_000_000)
    print(f"  final state: {res['final_state']}")
    print(f"  halt: {res['halt_at']}")
    print(f"  rule counts:")
    for rule, n in res["rule_counts"].most_common():
        print(f"    {rule:>8}: {n:>7}")

    # Step 4: push to 10M cycles
    print("\n=== Step 4: pure rule for 10,000,000 cycles ===")
    res = run(INITIAL, 10_000_000)
    print(f"  final state: {res['final_state']}")
    print(f"  halt: {res['halt_at']}")
    print(f"  rule counts:")
    for rule, n in res["rule_counts"].most_common():
        print(f"    {rule:>8}: {n:>7}")

    # Step 5: push to 100M cycles
    print("\n=== Step 5: pure rule for 100,000,000 cycles ===")
    import time
    t0 = time.time()
    res = run(INITIAL, 100_000_000)
    elapsed = time.time() - t0
    print(f"  final state: {res['final_state']}")
    print(f"  halt: {res['halt_at']}")
    print(f"  wall time: {elapsed:.1f}s")
    print(f"  rule counts:")
    for rule, n in res["rule_counts"].most_common():
        print(f"    {rule:>8}: {n:>10}")

    # Step 6: push to 1B cycles
    print("\n=== Step 6: pure rule for 1,000,000,000 cycles ===")
    t0 = time.time()
    res = run(INITIAL, 1_000_000_000)
    elapsed = time.time() - t0
    print(f"  final state: {res['final_state']}")
    print(f"  halt: {res['halt_at']}")
    print(f"  wall time: {elapsed:.1f}s")
    print(f"  rule counts:")
    for rule, n in res["rule_counts"].most_common():
        print(f"    {rule:>8}: {n:>11}")


if __name__ == "__main__":
    main()
