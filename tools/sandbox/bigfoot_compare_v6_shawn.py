#!/usr/bin/env python3
"""Run literal Bigfoot TM and tabulate every Shawn / V6 boundary.

Goal: figure out the granularity relation between
  - Shawn's Dyn step boundary: state A, head facing left at the seam between
    `12^a 11^b` and `11^c 0^∞`.
  - V6's super-cycle boundary: state C (just after a B-sweep), tape shape
    `(1 2)^k 1^a 2^b TAIL`.

If they occur at the SAME TM step (same tape moment), one V6 = one Shawn.
If they alternate, one V6 super-cycle = two Shawn Dyn steps (or some pattern).
If their cumulative TM-step counts differ wildly, granularities differ.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bigfoot_v1_literal import Bigfoot


def parse_shawn(bf):
    """Try parsing the current tape as Shawn (a, b, c) at his boundary:
      0^∞ 12^a 11^b <A 11^c 0^∞     (state A, head facing left after 11^b)

    The head is at the last cell of the 11^b block. Since we don't track
    "facing", we use: state == A AND tape[pos] == 1 AND tape[pos-1] == 1
    AND tape[pos+1] == 1 (in the 11^c block).

    Returns (a, b, c) or None.
    """
    if bf.state != "A":
        return None
    nonzero = sorted(i for i, v in bf.tape.items() if v != 0)
    if not nonzero:
        return None
    lo, rb = nonzero[0], nonzero[-1]
    cells = [bf.tape[i] for i in range(lo, rb + 1)]
    n = len(cells)

    # Parse leading alternating 1-2-1-2-... block
    a = 0
    i = 0
    while i + 1 < n and cells[i] == 1 and cells[i + 1] == 2:
        a += 1
        i += 2
    # After the alternating block, all remaining cells should be 1
    if not all(c == 1 for c in cells[i:]):
        return None
    rest = n - i  # number of trailing 1s
    if rest == 0:
        return None
    # head position relative to `lo`:
    head_rel = bf.pos - lo
    # Shawn boundary: head at position 2a + 2b - 1 within the tape span starting at lo.
    # So head_rel = 2a + 2b - 1, giving b = (head_rel + 1) / 2 - a.
    # And b + c = rest / 2 (the trailing 1s are 11^(b+c), length 2(b+c)).
    # But the trailing 1s start at position 2a; head_rel is within them.
    # Need to ensure b >= 0 and c >= 0.
    h = head_rel - 2 * a  # position within the 11-block (0-indexed from its start)
    # head at last cell of 11^b means h = 2b - 1, so b = (h + 1) / 2
    if h < 0 or (h + 1) % 2 != 0:
        return None
    b = (h + 1) // 2
    twice_bc = rest  # length of 11^b 11^c block (in cells)
    if twice_bc % 2 != 0:
        return None
    bplusc = twice_bc // 2
    c = bplusc - b
    if c < 0:
        return None
    return (a, b, c)


def parse_v6(bf):
    """Try parsing as V6 boundary: state C, tape `(1 2)^k 1^a 2^b TAIL`.

    P1: TAIL = `1 2`, head at the trailing 1 (position rb - 1).
    P2: TAIL = empty, head inside the trailing 2-block.

    Returns (k, a, b, pat) or None.
    """
    if bf.state != "C":
        return None
    nonzero = sorted(i for i, v in bf.tape.items() if v != 0)
    if not nonzero:
        return None
    lo, rb = nonzero[0], nonzero[-1]
    cells = [bf.tape[i] for i in range(lo, rb + 1)]
    n = len(cells)
    if cells[-1] != 2:
        return None
    if n < 2:
        return None

    if cells[-2] == 1:
        body = cells[:-2]
        pat = "P1"
        head_expected_rel = rb - 1 - lo
    else:
        body = cells[:]
        pat = "P2"
        # head is somewhere inside the trailing 2-block; we check after parse.
        head_expected_rel = None

    # Count trailing 2s -> b
    b = 0
    while b < len(body) and body[-1 - b] == 2:
        b += 1
    # Count trailing 1s -> a
    a = 0
    idx = len(body) - 1 - b
    while idx >= 0 and body[idx] == 1:
        a += 1
        idx -= 1
    prefix = body[: idx + 1]
    if len(prefix) % 2 != 0:
        return None
    k = len(prefix) // 2
    if not all(prefix[2 * j] == 1 and prefix[2 * j + 1] == 2 for j in range(k)):
        return None

    # Head position check
    head_rel = bf.pos - lo
    if pat == "P1":
        if head_rel != head_expected_rel:
            return None
    else:  # P2
        # Head must be inside the 2-block: positions in [2k + a, 2k + a + b)
        start = 2 * k + a
        if not (start <= head_rel < start + b):
            return None

    return (k, a, b, pat)


def main():
    bf = Bigfoot()
    # Bootstrap to TM step 69
    for _ in range(69):
        bf.step()
    print(f"TM step 69: state={bf.state}, pos={bf.pos}")
    shawn = parse_shawn(bf)
    v6 = parse_v6(bf)
    print(f"  Shawn parse: {shawn}")
    print(f"  V6 parse:    {v6}")

    # Walk forward, log every Shawn / V6 boundary
    max_steps = 2000
    boundaries = []
    for tm_step in range(70, max_steps + 1):
        if not bf.step():
            print(f"TM halt at step {tm_step}")
            break
        shawn = parse_shawn(bf)
        v6 = parse_v6(bf)
        if shawn is not None:
            boundaries.append((tm_step, "S", shawn))
        if v6 is not None:
            boundaries.append((tm_step, "V", v6))

    # Print first ~60 boundaries
    print(f"\nFirst 60 boundaries (of {len(boundaries)} total in {max_steps} TM steps):")
    for tm_step, kind, st in boundaries[:60]:
        print(f"  step {tm_step:>6}  {kind}  {st}")

    # Count by kind
    counts = {"S": 0, "V": 0}
    for _, kind, _ in boundaries:
        counts[kind] += 1
    print(f"\nTotals over {max_steps} TM steps: Shawn={counts['S']}, V6={counts['V']}")

    # Inter-boundary intervals
    if len(boundaries) >= 2:
        print("\nInter-boundary intervals (first 20):")
        for i in range(1, min(21, len(boundaries))):
            prev = boundaries[i-1]
            cur = boundaries[i]
            dt = cur[0] - prev[0]
            print(f"  {prev[1]}@{prev[0]:>4} -> {cur[1]}@{cur[0]:>4}  (Δ={dt})")


if __name__ == "__main__":
    main()
