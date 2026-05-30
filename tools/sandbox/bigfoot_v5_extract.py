#!/usr/bin/env python3
"""Bigfoot v5 (extractor): parse (k, a, b, pattern) from tape at super-cycle boundaries.

Hypothesis from v5_tape_inspect: at end of each super-cycle, tape is
   0^inf  (1 2)^k  1^a  2^b  TAIL  0^inf
where TAIL is one of:
   P1: `1 2`     (head on the trailing 1)         — has b ≥ 0
   P2:            (head inside 2^b)               — no separate tail
   P3: `2`       (head inside 1^a, no 2^b middle) — b=0 implicit

This script parses each super-cycle boundary into (k, a, b, pattern,
N) and dumps a table; then looks for the (a,b)→(a',b') recurrence.

Verification: equivalence-checked against v1.
"""

import sys
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bigfoot_v1_literal import Bigfoot as BigfootV1
from bigfoot_v5_tape_inspect import BigfootV5


def parse_tape(bf):
    """Parse end-of-super-cycle tape into (k, a, b, type).

    Canonical forms (parse from RIGHT to avoid (1 2)^k | 1^a ambiguity):
      P1: 0^inf  (1 2)^k  1^a  2^b  1  2  0^inf       head at the trailing 1
      P2: 0^inf  (1 2)^k  1^a  2^b               0^inf  head inside the 2^b
                                                       (cells end with 2 2)

    P3 (head inside 1^a, trailing single 2) is encoded as P1 with b=0:
      `(1 2)^k 1^(a+1) 2` ≡ P1(k, a, 0) with TAIL=`1 2`.
    """
    nonzero = sorted(i for i, v in bf.tape.items() if v != 0)
    if not nonzero:
        return {"valid": False, "reason": "empty tape"}
    lo, rb = nonzero[0], nonzero[-1]
    cells = [bf.tape[i] for i in range(lo, rb + 1)]
    n = len(cells)
    if cells[-1] != 2:
        return {"valid": False, "reason": f"rb cell = {cells[-1]}, expected 2"}
    if n < 2:
        return {"valid": False, "reason": "tape too small"}

    head_pos = bf.pos

    # Decide P1 vs P2 by the cell just before rb.
    if cells[-2] == 1:
        # P1 candidate. Strip trailing "1 2".
        body = cells[:-2]
        ptype = "P1"
    else:
        # cells[-2] == 2: P2 candidate (head inside trailing 2-block).
        body = cells[:]
        ptype = "P2"

    # Count trailing 2s in body  ->  b
    b = 0
    while b < len(body) and body[-1 - b] == 2:
        b += 1
    # Count trailing 1s (before the 2-block)  ->  a
    a = 0
    idx = len(body) - 1 - b
    while idx >= 0 and body[idx] == 1:
        a += 1
        idx -= 1
    # Remaining prefix should be (1 2)^k strict alternation.
    prefix = body[: idx + 1]
    if len(prefix) % 2 != 0:
        return {"valid": False, "reason": f"prefix len {len(prefix)} odd",
                "prefix": prefix, "ptype": ptype, "a": a, "b": b}
    k = len(prefix) // 2
    ok = all(prefix[2 * j] == 1 and prefix[2 * j + 1] == 2 for j in range(k))
    if not ok:
        return {"valid": False, "reason": f"prefix not (1 2)^k",
                "prefix": prefix, "ptype": ptype, "a": a, "b": b, "k": k}

    # Sanity check head position for P1: should be at lo + 2k + a + b.
    if ptype == "P1":
        expected_head = lo + 2 * k + a + b
        if head_pos != expected_head:
            return {"valid": False, "reason": f"P1 head at {head_pos}, "
                    f"expected {expected_head}",
                    "k": k, "a": a, "b": b, "ptype": ptype}
    else:  # P2
        # Head should be inside trailing 2-block: lo + 2k + a <= head_pos <= rb
        head_lo = lo + 2 * k + a
        if not (head_lo <= head_pos <= rb):
            return {"valid": False, "reason": f"P2 head at {head_pos}, "
                    f"expected in [{head_lo}, {rb}]",
                    "k": k, "a": a, "b": b, "ptype": ptype}

    return {
        "valid": True,
        "k": k,
        "a": a,
        "b": b,
        "pattern": ptype,
        "head_pos": head_pos,
        "footprint": n,
        "lo": lo,
        "rb": rb,
    }


def main():
    print("===== extract (k, a, b, pattern) from 200 super-cycles =====\n")

    bf = BigfootV5()
    bf.bootstrap_to_first_b_end()

    rows = []
    for cyc in range(1, 201):
        info = bf.super_cycle_v4()
        if info is None:
            print(f"halted at cycle {cyc}")
            break
        parse = parse_tape(bf)
        if not parse["valid"]:
            print(f"cycle {cyc}: PARSE FAILED -- {parse}")
            continue
        row = {
            "C": cyc,
            "N": info["N"],
            "drop": info["drop"],
            "bounces": info["bounces"],
            **parse,
        }
        rows.append(row)

    # Print summary table
    print(f"{'C':>4} {'k':>3} {'a':>4} {'b':>4} {'pat':>5} {'N':>4} {'drop':>5} "
          f"{'non0_bites':>15} {'sum_bites':>10}")
    print("-" * 75)
    for r in rows:
        non0_bites = [b for b in r["bounces"] if b != 0] + (
            [r["drop"]] if r["drop"] != 0 else [])
        sum_bites = sum(r["bounces"]) + r["drop"]
        non0_str = (str(non0_bites)[:13] if len(str(non0_bites)) <= 13
                    else str(non0_bites)[:11] + "..")
        print(f"{r['C']:>4} {r['k']:>3} {r['a']:>4} {r['b']:>4} "
              f"{r['pattern']:>5} {r['N']:>4} {r['drop']:>5} "
              f"{non0_str:>15} {sum_bites:>10}")

    # Pattern distribution
    print(f"\npattern distribution:")
    pat_count = Counter(r["pattern"] for r in rows)
    for p, n in pat_count.most_common():
        print(f"  {p}: {n}")

    # k distribution
    print(f"\nk distribution:")
    k_count = Counter(r["k"] for r in rows)
    for k, n in sorted(k_count.items()):
        print(f"  k={k}: {n}")

    # Look at (a, b) transitions for consecutive P1 cycles with same k
    print(f"\n(a, b) transitions, P1 → P1 with same k:")
    diffs = []
    for i in range(len(rows) - 1):
        r1, r2 = rows[i], rows[i + 1]
        if r1["pattern"] == "P1" and r2["pattern"] == "P1" and r1["k"] == r2["k"]:
            da = r2["a"] - r1["a"]
            db = r2["b"] - r1["b"]
            diffs.append((r1["C"], r1["k"], (r1["a"], r1["b"]),
                          (r2["a"], r2["b"]), (da, db)))
            print(f"  C{r1['C']} → C{r2['C']}: k={r1['k']}  "
                  f"({r1['a']:3d},{r1['b']:3d}) → ({r2['a']:3d},{r2['b']:3d})  "
                  f"Δ=({da:+3d},{db:+3d})")

    # Histogram of (Δa, Δb)
    print(f"\nP1→P1 (Δa, Δb) histogram:")
    diff_count = Counter((d[4][0], d[4][1]) for d in diffs)
    for (da, db), n in sorted(diff_count.items(), key=lambda x: -x[1]):
        print(f"  ({da:+3d}, {db:+3d}): {n}")

    # Inspect bite APs for cycles with non-zero bites
    print(f"\nbite APs (non-zero bite vectors) in first 50 cycles with bites:")
    count = 0
    for r in rows:
        non0 = [b for b in r["bounces"] if b != 0] + (
            [r["drop"]] if r["drop"] != 0 else [])
        if non0:
            count += 1
            if count > 50:
                break
            # Check AP
            ap_diff = None
            is_ap = False
            if len(non0) >= 2:
                ap_diff = non0[1] - non0[0]
                is_ap = all(non0[j + 1] - non0[j] == ap_diff
                            for j in range(len(non0) - 1))
            print(f"  C{r['C']:3d}: k={r['k']} a={r['a']} b={r['b']} "
                  f"pat={r['pattern']:5s}  bites={non0}  "
                  f"{'AP diff=' + str(ap_diff) if is_ap else 'not AP'}")


if __name__ == "__main__":
    main()
