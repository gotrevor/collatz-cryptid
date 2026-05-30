#!/usr/bin/env python3
"""Hunt for invariants in Shawn's (a, b, c) Bigfoot dynamics.

Specifically: how close does the orbit come to the halt branch
(a=0, b mod 6 = 2)? Find consecutive r=2 streaks, lowest a, etc.
"""

import sys
sys.set_int_max_str_digits(1_000_000)

from bigfoot_shawn_rule import shawn_step, INITIAL


def main():
    state = INITIAL
    a_history = [state[0]]
    r_history = []
    r_consecutive_streak = 0
    max_r2_streak = 0
    r_streak_examples = {}  # streak length -> first occurrence step
    min_a_after_r2 = float('inf')
    a_under_pressure = []  # times when a was small AND r=2 was about to fire

    N = 1_000_000
    for i in range(1, N + 1):
        a, b, c = state
        r = b % 6
        r_history.append(r)
        if r == 2:
            r_consecutive_streak += 1
            max_r2_streak = max(max_r2_streak, r_consecutive_streak)
            if r_consecutive_streak not in r_streak_examples:
                r_streak_examples[r_consecutive_streak] = (i, state)
            if a <= 5:
                a_under_pressure.append((i, a, r_consecutive_streak))
        else:
            r_consecutive_streak = 0

        nxt = shawn_step(*state)
        if nxt is None:
            print(f"HALT at step {i}: {state}")
            return
        state = nxt
        a_history.append(state[0])

        if i % 100_000 == 0:
            print(f"  step {i}: a={state[0]}, max r=2 streak so far = {max_r2_streak}")

    print(f"\n=== Summary over {N} steps ===")
    print(f"Final a: {state[0]}")
    print(f"Min a overall: {min(a_history)}")
    print(f"Max r=2 streak: {max_r2_streak}")
    print(f"r=2 streak first-occurrence examples:")
    for streak_len in sorted(r_streak_examples.keys()):
        step_at, state_at = r_streak_examples[streak_len]
        print(f"  streak={streak_len}: first at step {step_at}, a={state_at[0]}")

    # Lowest a after a sequence of r=2 events
    print(f"\nTimes a was ≤ 5 during r=2 events (could be halt-precursor):")
    for step, a, streak in a_under_pressure[:30]:
        print(f"  step {step}: a={a}, current r=2 streak = {streak}")
    print(f"  total such events: {len(a_under_pressure)}")

    # Look for "a equals 2 at an r=2 event" - that would mean halt-in-2-steps
    print(f"\nTimes a == 2 at an r=2 event (halt-in-2-steps risk):")
    danger = [(step, a, streak) for step, a, streak in a_under_pressure if a == 2]
    for step, a, streak in danger[:10]:
        print(f"  step {step}: a=2, streak={streak}")
    print(f"  total: {len(danger)}")

    print(f"\nTimes a == 1 at an r=2 event (halt-in-1-step):")
    danger1 = [(step, a, streak) for step, a, streak in a_under_pressure if a == 1]
    for step, a, streak in danger1[:10]:
        print(f"  step {step}: a=1, streak={streak}")
    print(f"  total: {len(danger1)}")

    # Run length histogram for r=2 streaks
    streaks_by_len = {}
    cur = 0
    for r in r_history:
        if r == 2:
            cur += 1
        else:
            if cur > 0:
                streaks_by_len[cur] = streaks_by_len.get(cur, 0) + 1
            cur = 0
    if cur > 0:
        streaks_by_len[cur] = streaks_by_len.get(cur, 0) + 1
    print(f"\nr=2 streak length distribution:")
    for length, count in sorted(streaks_by_len.items()):
        print(f"  streaks of length {length}: {count}")


if __name__ == "__main__":
    main()
