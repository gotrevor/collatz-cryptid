#!/usr/bin/env -S uv run python3
"""Parse Bigfoot's super-cycle-boundary tape into (a, b, X) parameters and
tabulate them next to N and the dance bite vector. Built on
bigfoot_v5_tape_inspect (your "Path A" starter).

Conjectured parametric form at every super-cycle boundary
(state == C, just after a B-sweep, head at rb-1):

    0^inf  [fossil: alternating 1 2, length L]  1^a  2^b  X  2  0^inf
                                                          ^head, X in {1,2}

The trailing 2 is what B just wrote at rb. Walking left from head-1:
the 2-block has length b, then the 1-block has length a, then the rest
is the fossil. If the recurrence (a, b, X) -> (a', b', X') closes, we
have Bigfoot's halting question in three integers.

If the fossil ever fails the alternation check, we flag it -- that's a
sign the parametric form needs another knob.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bigfoot_v5_tape_inspect import BigfootV5


class BigfootParametric(BigfootV5):

    def parse_parametric(self):
        """Parse current tape into the (a, b, X) form above. Returns a dict."""
        nonzero = sorted(i for i, v in self.tape.items() if v != 0)
        assert nonzero, "tape is empty"
        lo, hi = nonzero[0], nonzero[-1]
        head = self.pos
        assert hi == head + 1, f"expected rb=head+1, got rb={hi}, head={head}"
        assert self.tape[hi] == 2, f"expected 2 at rb, got {self.tape[hi]}"

        X = self.tape[head]
        # Walk left from head-1 collecting the 2-block, then the 1-block.
        i = head - 1
        b = 0
        while i >= lo and self.tape[i] == 2:
            b += 1
            i -= 1
        a = 0
        while i >= lo and self.tape[i] == 1:
            a += 1
            i -= 1
        # Whatever's left of i should be the alternating fossil.
        fossil = [self.tape[j] for j in range(lo, i + 1)]
        fossil_ok = (all(c in (1, 2) for c in fossil) and
                     all(fossil[k] != fossil[k + 1]
                         for k in range(len(fossil) - 1)))
        return {"a": a, "b": b, "X": X,
                "L": len(fossil), "fossil_ok": fossil_ok,
                "fossil": fossil}


def main():
    n_cycles = 60

    bf = BigfootParametric()
    bf.bootstrap_to_first_b_end()
    init = bf.parse_parametric()
    print(f"After bootstrap: a={init['a']} b={init['b']} X={init['X']} "
          f"L={init['L']} fossil={init['fossil']}")

    rows = []
    for k in range(1, n_cycles + 1):
        info = bf.super_cycle_v4()
        if info is None:
            print(f"halted at cycle {k}")
            break
        p = bf.parse_parametric()
        bites = list(info["bounces"]) + [info["drop"]]
        nonzero_bites = sorted(b for b in bites if b > 0)
        rows.append({
            "k": k, "a": p["a"], "b": p["b"], "X": p["X"],
            "L": p["L"], "ok": p["fossil_ok"],
            "N": info["N"], "drop": info["drop"],
            "nonzero_bites": nonzero_bites,
        })

    print()
    print(f"{'k':>3} | {'a':>3} {'b':>3} X  L | {'N':>3} {'drop':>4} | nonzero bites (sorted)")
    print("-" * 70)
    for r in rows:
        bites_str = ", ".join(str(b) for b in r["nonzero_bites"])
        flag = " ! fossil broken" if not r["ok"] else ""
        print(f"{r['k']:>3} | {r['a']:>3} {r['b']:>3} {r['X']}  {r['L']:>2} | "
              f"{r['N']:>3} {r['drop']:>4} | {bites_str}{flag}")

    # Transitions: how does (a, b, X) evolve cycle-to-cycle?
    print()
    print(f"transitions:")
    print(f"{'k':>3} -> {'k+1':>3} | {'(a,b,X)':>10} -> {'(a,b,X)':>10} | "
          f"{'da':>4} {'db':>4} dX | {'N_{k+1}':>7}")
    print("-" * 70)
    for i in range(len(rows) - 1):
        r, s = rows[i], rows[i + 1]
        da, db = s["a"] - r["a"], s["b"] - r["b"]
        dX = f"{r['X']}->{s['X']}" if r["X"] != s["X"] else "  "
        print(f"{r['k']:>3} -> {s['k']:>3} | "
              f"({r['a']:>2},{r['b']:>2},{r['X']}) -> ({s['a']:>2},{s['b']:>2},{s['X']}) | "
              f"{da:>+4} {db:>+4} {dX:>4} | {s['N']:>7}")


if __name__ == "__main__":
    main()
