#!/usr/bin/env python3
"""Shawn Ligocki's Bigfoot (a, b, c) Dyn rule, ported from Dynamics.lean.

Source: https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html
Lean version: lean/Collatz/Bigfoot/Dynamics.lean

Rules (verbatim from Ligocki 2023):
    A(a, 6k,   c) → A(a,   8k + c - 1, 2)
    A(a, 6k+1, c) → A(a+1, 8k + c - 1, 3)
    A(a, 6k+2, c) → A(a-1, 8k + c + 3, 2)    when a > 0
    A(a, 6k+3, c) → A(a,   8k + c + 1, 5)
    A(a, 6k+4, c) → A(a+1, 8k + c + 3, 2)
    A(a, 6k+5, c) → A(a,   8k + c + 5, 3)
    A(0, 6k+2, c) → Halt(16k + 2c + 7)        (the halting branch)

Initial state: A(2, 1, 2). Empirically: never reaches halt.

Tape encoding (also from Dynamics.lean / Encoding.lean):
    0^∞ 12^a 11^b <A 11^c 0^∞
where 12^a means "12 repeated a times" (length 2a) and 11^b means
"11 repeated b times" (length 2b). Head sits at the LAST cell of
the 11^b block (position 2a + 2b - 1), facing left.

One Dyn step corresponds to one "phase" of TM execution; per
Encoding.lean's `bigfootCost`, that's 24·c + 176 TM micro-steps
(for b ≥ 7; small-b values have their own counts).
"""

from collections import Counter


def shawn_step(state):
    """Apply ONE Dyn step. state = (a, b, c). Returns (new_state, rule_name)
    or (None, 'HALT') on halt branch."""
    a, b, c = state
    k = b // 6
    r = b % 6
    if r == 0:
        return (a, 8*k + c - 1, 2), "r0"
    if r == 1:
        return (a + 1, 8*k + c - 1, 3), "r1"
    if r == 2:
        if a == 0:
            return None, "HALT"
        return (a - 1, 8*k + c + 3, 2), "r2"
    if r == 3:
        return (a, 8*k + c + 1, 5), "r3"
    if r == 4:
        return (a + 1, 8*k + c + 3, 2), "r4"
    # r == 5
    return (a, 8*k + c + 5, 3), "r5"


# Shawn's initial state, per Dynamics.lean Dyn.init.
INITIAL = (2, 1, 2)


def run(initial, n_steps, log_first=0):
    """Iterate Shawn's rule. Returns dict with halt info, rule histogram, log."""
    state = initial
    rule_counts = Counter()
    log = [(0, state, None)]
    halt_at = None
    for step in range(1, n_steps + 1):
        result, rule = shawn_step(state)
        if result is None:
            halt_at = (step, state, rule)
            break
        state = result
        rule_counts[rule] += 1
        if step <= log_first:
            log.append((step, state, rule))
    return {
        "final": state,
        "halt_at": halt_at,
        "rule_counts": rule_counts,
        "log": log,
    }


def main():
    print("===== Shawn Bigfoot Dyn rule (a, b, c) =====")
    print(f"INITIAL: A{INITIAL}\n")

    # First 20 steps in detail
    print("=== First 20 steps ===")
    res = run(INITIAL, 20, log_first=20)
    for step, state, rule in res["log"]:
        print(f"  step {step:>3}: A{state}  via {rule}")

    # 100k steps for rule histogram
    print("\n=== 100,000 steps: rule histogram ===")
    res = run(INITIAL, 100_000)
    print(f"  final: A{res['final']}")
    print(f"  halt: {res['halt_at']}")
    for rule, n in sorted(res["rule_counts"].items()):
        print(f"    {rule}: {n}")

    # 1M steps for stability check
    print("\n=== 1,000,000 steps ===")
    res = run(INITIAL, 1_000_000)
    print(f"  final: A{res['final']}")
    print(f"  halt: {res['halt_at']}")


if __name__ == "__main__":
    main()
