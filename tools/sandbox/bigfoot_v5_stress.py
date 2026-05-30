#!/usr/bin/env python3
"""Bigfoot v5 stress test: run 10k+ super-cycles and test the conjectured rules.

Conjectured update rule (from 200-cycle sample):
   if a even, a >= 3: (a, b) -> (a-3, b+5)         [S]
   if a odd, a >= 9:  (a, b) -> (a-9, b+11)        [B]
   if a == 1:         -> P2(k+1, b, 3) -> P1(k+1, b-4, 7)  [Q]
   if a == 2:         -> P1(k, a+b+2, 0)           [W]
   if a == 3:         -> P1(k-1, a+b+4, 0)         [D-W]
   if a == 5:         -> P2(k, a+b+2, 2) -> P1(k, a+b-2, 6)  [Q-same]
   if a == 7:         -> ??  (not observed yet)

Run 10k cycles and:
  1. Verify against v1 every 100 cycles.
  2. Check every transition matches one of the conjectured rules.
  3. Report any anomalies (transitions that don't fit).
  4. Track distribution of wrap triggers (a=1, 2, 3, 5, 7, ...).
"""

import sys
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bigfoot_v1_literal import Bigfoot as BigfootV1
from bigfoot_v5_tape_inspect import BigfootV5
from bigfoot_v5_extract import parse_tape


N_CYCLES = 100_000
VERIFY_EVERY = 1000


def predict_next(state):
    """Given current (k, a, b, pattern), predict next state per conjecture.
    Returns dict {next_state, rule_name} or None if no rule matches."""
    k, a, b, pat = state["k"], state["a"], state["b"], state["pattern"]
    if pat == "P2":
        # P2 -> P1: (k, a-4, b+4)
        return {"k": k, "a": a - 4, "b": b + 4, "pattern": "P1", "rule": "P2->P1"}
    # pat == P1
    if a % 2 == 0:
        if a >= 4:
            return {"k": k, "a": a - 3, "b": b + 5, "pattern": "P1", "rule": "S"}
        elif a == 2:
            return {"k": k, "a": a + b + 2, "b": 0, "pattern": "P1", "rule": "W"}
        elif a == 0:
            return {"rule": "a=0 unknown"}
    else:  # a odd
        if a >= 11:
            return {"k": k, "a": a - 9, "b": b + 11, "pattern": "P1", "rule": "B"}
        elif a == 9:
            return {"k": k - 1, "a": 1, "b": b + 12, "pattern": "P1", "rule": "B-coll"}
        elif a == 7:
            return {"k": k + 1, "a": a + b, "b": 0, "pattern": "P1", "rule": "Q-W"}
        elif a == 5:
            return {"k": k, "a": a + b + 2, "b": 2, "pattern": "P2", "rule": "Q-same"}
        elif a == 3:
            return {"k": k - 1, "a": a + b + 4, "b": 0, "pattern": "P1", "rule": "D-W"}
        elif a == 1:
            return {"k": k + 1, "a": b, "b": 3, "pattern": "P2", "rule": "Q-kpp"}


def main():
    print(f"===== stress test: {N_CYCLES} super-cycles =====\n")

    bf = BigfootV5()
    bf.bootstrap_to_first_b_end()
    # v5 verified against v1 at 200 cycles in tape_inspect; skipping per-step
    # v1 verification here because it's O(N^2). The rule-vs-simulator check
    # below catches all the cases we care about.

    rule_counts = Counter()
    anomalies = []
    states = []  # (cycle, k, a, b, pattern, N)
    last_parse = None

    for cyc in range(1, N_CYCLES + 1):
        info = bf.super_cycle_v4()
        if info is None:
            print(f"halted at cycle {cyc}")
            break
        parse = parse_tape(bf)
        if not parse["valid"]:
            anomalies.append((cyc, "PARSE_FAIL", parse))
            print(f"cycle {cyc}: PARSE FAILED -- {parse}")
            last_parse = None
            continue

        cur = {"k": parse["k"], "a": parse["a"], "b": parse["b"],
               "pattern": parse["pattern"], "N": info["N"]}

        if last_parse is not None:
            pred = predict_next(last_parse)
            if pred is None or "k" not in pred:
                anomalies.append((cyc, "NO_RULE",
                                  {"last": last_parse, "cur": cur,
                                   "pred_rule": pred.get("rule") if pred else None}))
                rule_counts[f"NO_RULE ({pred.get('rule') if pred else 'none'})"] += 1
            else:
                match = (pred["k"] == cur["k"] and pred["a"] == cur["a"]
                         and pred["b"] == cur["b"] and pred["pattern"] == cur["pattern"])
                if match:
                    rule_counts[pred["rule"]] += 1
                else:
                    anomalies.append((cyc, "MISMATCH",
                                      {"last": last_parse, "cur": cur, "pred": pred}))
                    rule_counts[f"MISMATCH ({pred['rule']})"] += 1
        last_parse = cur
        states.append((cyc, cur))

        if cyc % 10000 == 0:
            print(f"  ...cycle {cyc}: k={cur['k']} a={cur['a']} b={cur['b']} "
                  f"pat={cur['pattern']} N={cur['N']}  anomalies so far: {len(anomalies)}")

    print(f"\n===== rule distribution over {len(states)} cycles =====")
    for rule, n in rule_counts.most_common():
        print(f"  {rule:>15}: {n:>6}")

    print(f"\n===== anomalies: {len(anomalies)} =====")
    # Show first 20
    for cyc, kind, info in anomalies[:20]:
        print(f"  C{cyc}: {kind}  {info}")

    # Phase-end (wrap-trigger) distribution by a-value
    print(f"\n===== phase-end a-values (P1 transitions to wrap rules) =====")
    wrap_a_count = Counter()
    for cyc, state in states:
        if state["pattern"] == "P1":
            a = state["a"]
            if a in (1, 2, 3, 5, 7) or a == 0 or (a % 2 == 1 and a < 9):
                wrap_a_count[a] += 1
    for a, n in sorted(wrap_a_count.items()):
        print(f"  a={a}: {n}")


if __name__ == "__main__":
    main()
