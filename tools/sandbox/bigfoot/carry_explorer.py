#!/usr/bin/env -S uv run python3
"""Carry explorer: parses cycles with the parametric simulator's worldview
(fossil = leftmost 6 cells in steady state) so we can read carries cleanly,
then dumps every transition with a kind label.

Tracks fossil_left over time -- the fossil's left edge moves leftward when
min_nonzero decreases. Fossil length stays 6 unless we explicitly observe
it shifting (e.g., post-carry fossil truncation).

Kinds:
  (-3,+5)  -- normal X=1, b even
  (-9,+11) -- normal X=1, b odd
  (-4,+6)  -- X=2 -> X=1 recovery step
  CARRY    -- anything else (a would underflow normal law)
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bigfoot_v5_tape_inspect import BigfootV5


class FossilAwareParser:
    """Tracks fossil position over time; parses (a, b, X) given fossil bounds."""

    def __init__(self):
        # Set lazily on first observation
        self.fossil_left = None
        self.fossil_len = 6  # steady-state assumption; may be wrong early

    def update_from_bootstrap(self, bf):
        """After bootstrap, set initial fossil bounds."""
        nonzero = [i for i, v in bf.tape.items() if v != 0]
        if not nonzero:
            self.fossil_left = 0
            return
        self.fossil_left = min(nonzero)
        # Initially the fossil is whatever exists. After early cycles it
        # settles at length 6.

    def parse(self, bf):
        """Parse current tape, allowing the fossil left edge to extend leftward."""
        nonzero = [i for i, v in bf.tape.items() if v != 0]
        if not nonzero:
            return None
        cur_lo = min(nonzero)
        # Fossil left edge moves leftward when min_nonzero does
        if self.fossil_left is None or cur_lo < self.fossil_left:
            self.fossil_left = cur_lo

        head = bf.pos
        # Determine the actual rightmost fossil cell by walking right from
        # fossil_left until we either (a) leave alternation or (b) hit the
        # leftmost cell of an a>=2 1-block or a b>=2 2-block.
        fossil = []
        expected = 1
        i = self.fossil_left
        while i <= head:
            if bf.tape[i] != expected:
                break
            fossil.append(bf.tape[i])
            # Lookahead: if next cell is same value, we've entered a
            # length-2+ block (active region). Stop AFTER appending this cell.
            if i + 1 <= head and bf.tape[i + 1] == expected:
                i += 1
                break
            i += 1
            expected = 3 - expected
        fossil_len = len(fossil)

        # If the walker stopped on a length-2+ run of the next-expected value
        # (e.g. fossil ended in 2 and next is 2-block start), we may have
        # UNDER-counted fossil by 1 (the fossil's true rightmost cell got
        # absorbed into the active block). Detect via: the cell right after
        # fossil has value == (3 - expected_at_break), AND that cell is part
        # of a length>=2 run. In that case, bump fossil_len by 1.
        # The parametric law's view: fossil L=6 is the steady state. If our
        # walker reports L=5 and we're in steady state, assume the missing
        # cell got absorbed.
        if fossil_len == 5 and self.fossil_len == 6:
            # The fossil's true rightmost-2 got merged into the active 2-block.
            fossil_len = 6
            # Don't append the inferred fossil cell to `fossil` list (it's
            # already in the tape, just bookkeeping)

        # Update our running fossil_len if walker found more than known
        if fossil_len > self.fossil_len:
            self.fossil_len = fossil_len

        active_start = self.fossil_left + fossil_len
        # Parse 1^a, 2^b, X starting at active_start
        i = active_start
        a = 0
        while i < head and bf.tape[i] == 1:
            a += 1
            i += 1
        b = 0
        while i < head and bf.tape[i] == 2:
            b += 1
            i += 1
        # i should equal head now; X is tape[head]
        if i != head:
            # Active region doesn't match expected shape; fall back
            return {"a": -1, "b": -1, "X": bf.tape[head], "L": fossil_len,
                    "ok": False}
        X = bf.tape[head]
        return {"a": a, "b": b, "X": X, "L": fossil_len, "ok": True}


def classify_transition(pre, post, N):
    """Classify the transition kind based on (a, b, X) before and after."""
    da = post["a"] - pre["a"]
    db = post["b"] - pre["b"]
    dX = (pre["X"], post["X"])

    if dX == (1, 1):
        if da == -3 and db == 5:
            return "(-3,+5)"
        if da == -9 and db == 11:
            return "(-9,+11)"
        return f"CARRY (X=1->1, da={da:+d}, db={db:+d})"
    if dX == (2, 1):
        if da == -4 and db == 6:
            return "(-4,+6)"
        return f"X2->1 ({da:+d},{db:+d})"
    if dX == (1, 2):
        return f"CARRY X1->2 ({da:+d},{db:+d})"
    return f"OTHER ({da:+d},{db:+d}, X={dX})"


def main():
    bf = BigfootV5()
    bf.bootstrap_to_first_b_end()

    parser = FossilAwareParser()
    parser.update_from_bootstrap(bf)
    prev = parser.parse(bf)

    print(f"{'k':>3}  {'(a,b,X)':>11}  {'L':>2}  {'N':>4}  {'drop':>4}  {'kind':<22}  nonzero bites")
    print("-" * 100)

    for k in range(1, 80):
        info = bf.super_cycle_v4()
        if info is None:
            print(f"halted at cycle {k}")
            break
        cur = parser.parse(bf)
        kind = classify_transition(prev, cur, info["N"])
        bites = sorted(b for b in info["bounces"] + [info["drop"]] if b > 0)
        print(f"{k:>3}  ({cur['a']:>2},{cur['b']:>2},{cur['X']})  {cur['L']:>2}  "
              f"{info['N']:>4}  {info['drop']:>4}  {kind:<22}  {bites}")
        prev = cur


if __name__ == "__main__":
    main()
