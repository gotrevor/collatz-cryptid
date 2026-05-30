#!/usr/bin/env python3
"""Bigfoot via Shawn Ligocki's (a, b, c) reduction.

From sligocki.com/2023/10/16/bb-3-3-is-hard.html and our existing
Lean encoding (lean/Collatz/Bigfoot/Dynamics.lean):

  A(a, 6k,   c) -> A(a,   8k + c - 1, 2)
  A(a, 6k+1, c) -> A(a+1, 8k + c - 1, 3)
  A(a, 6k+2, c) -> A(a-1, 8k + c + 3, 2)  when a > 0
  A(a, 6k+3, c) -> A(a,   8k + c + 1, 5)
  A(a, 6k+4, c) -> A(a+1, 8k + c + 3, 2)
  A(a, 6k+5, c) -> A(a,   8k + c + 5, 3)

  HALT when a = 0 and b mod 6 = 2.

Initial state: A(2, 1, 2). Open question: does the orbit ever halt?
"""


def shawn_step(a, b, c):
    """One step. Returns (a', b', c') or None on halt."""
    k = b // 6
    r = b % 6
    if r == 0:
        return (a, 8 * k + c - 1, 2)
    if r == 1:
        return (a + 1, 8 * k + c - 1, 3)
    if r == 2:
        if a == 0:
            return None
        return (a - 1, 8 * k + c + 3, 2)
    if r == 3:
        return (a, 8 * k + c + 1, 5)
    if r == 4:
        return (a + 1, 8 * k + c + 3, 2)
    # r == 5
    return (a, 8 * k + c + 5, 3)


INITIAL = (2, 1, 2)


def run(n_steps, log_every=None):
    state = INITIAL
    history = [state]
    for i in range(1, n_steps + 1):
        nxt = shawn_step(*state)
        if nxt is None:
            print(f"HALT at step {i}: {state}")
            return history, i
        state = nxt
        if log_every and i % log_every == 0:
            history.append(state)
    history.append(state)
    return history, None


def main():
    print(f"INITIAL: {INITIAL}\n")
    print("First 30 steps:")
    state = INITIAL
    for i in range(1, 31):
        nxt = shawn_step(*state)
        if nxt is None:
            print(f"  step {i}: HALT from {state}")
            break
        print(f"  step {i:3d}: a={state[0]:4d} b={state[1]:7d} c={state[2]} "
              f"-> a={nxt[0]:4d} b={nxt[1]:7d} c={nxt[2]}  "
              f"(r=b%6={state[1] % 6})")
        state = nxt

    print("\n=== run 100k steps, look for halt and track stats ===")
    import sys
    sys.set_int_max_str_digits(1_000_000)

    state = INITIAL
    min_a = state[0]
    max_a = state[0]
    a_zero_count = 0
    b_mod6_dist = [0] * 6
    c_dist = {}
    a_min_per_r2 = []  # a value at every r=2 event
    a_trajectory = [state[0]]
    for i in range(1, 100001):
        nxt = shawn_step(*state)
        if nxt is None:
            print(f"HALT at step {i}: {state}")
            return
        # Pre-step b residue determines r
        a, b, c = state
        r = b % 6
        if r == 2:
            a_min_per_r2.append(a)
        state = nxt
        a_after = state[0]
        min_a = min(min_a, a_after)
        max_a = max(max_a, a_after)
        if a_after == 0:
            a_zero_count += 1
        b_mod6_dist[r] += 1
        c_dist[state[2]] = c_dist.get(state[2], 0) + 1
        if i % 1000 == 0:
            a_trajectory.append(state[0])
    print(f"  100k steps completed without halt.")
    print(f"  min a: {min_a}  max a: {max_a}")
    print(f"  a == 0 count: {a_zero_count}")
    print(f"  b mod 6 distribution: {b_mod6_dist}")
    print(f"  c distribution: {c_dist}")
    print(f"  at r=2 events: count={len(a_min_per_r2)}  "
          f"min a (pre-decrement) = {min(a_min_per_r2)}  "
          f"(if min > 0, halt impossible at these events)")
    print(f"  a-value sample every 1k steps: {a_trajectory[:20]} ... {a_trajectory[-5:]}")


if __name__ == "__main__":
    main()
