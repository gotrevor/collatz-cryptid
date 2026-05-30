#!/usr/bin/env python3
"""Bigfoot TM, v5: behaviorally identical to v4, cleaned up.

v4's dance_step return dict tracked unused 'macros' and 'micros' fields;
this version returns only what callers consume. The '??' fallback for
unexpected A_skim termination is now an assert (the docstring contract
makes it unreachable). main() runs the simulation once and slices the
result instead of double-running. The v1 catch-up loop is a helper.

Hypothesis (unchanged from v4):

   dance = (C_step, A_skim) repeated N+1 times
         = N "bounces" (A_skim ends in C) + 1 "drop" (A_skim ends in B)

Each (C_step, A_skim) pair bites k >= 0 ones before terminating; k is
the relevant integer state per pair.

   dance shape = [(b_1, "bounce"), ..., (b_N, "bounce"), (b_drop, "drop")]
"""

import sys
from collections import Counter
from pathlib import Path

# v1 and v3 live in the parent sandbox dir
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bigfoot_v1_literal import Bigfoot as BigfootV1
from bigfoot_v3_supercycle import BigfootV3


class BigfootV5(BigfootV3):

    def dance_step(self):
        """Execute one (C_step, A_skim) pair from inside the dance.

        Pre-condition:  state == C.
        Post-condition: bounce -> state == C; drop -> state == B; halt -> done.

        Returns {"kind": "bounce"|"drop"|"halt", "bites": int}. 'bites' is
        the number of 1s the A_skim ate before terminating (0 for halt).
        """
        assert self.state == "C", f"dance_step requires C, got {self.state}"
        if not self.macro_step():
            return {"kind": "halt", "bites": 0}
        assert self.state == "A", f"C should hand off to A, got {self.state}"
        a_micros_before = self.micro_count
        if not self.macro_step():
            return {"kind": "halt", "bites": 0}
        # A_skim micros = 1 terminal transition + bites (1s eaten)
        bites = (self.micro_count - a_micros_before) - 1
        if self.state == "C":
            return {"kind": "bounce", "bites": bites}
        if self.state == "B":
            return {"kind": "drop", "bites": bites}
        assert False, f"A_skim ended in unexpected state {self.state}"

    def super_cycle_v5(self):
        """Run the dance to completion, then the post-dance B-sweep.

        Returns a summary dict, or None if the machine halted.
        """
        bounces = []
        while True:
            info = self.dance_step()
            if info["kind"] == "halt":
                return None
            if info["kind"] == "bounce":
                bounces.append(info["bites"])
            else:  # drop
                drop_bites = info["bites"]
                break
        # state == B; run the B-sweep
        prev_micro = self.micro_count
        if not self.macro_step():
            return None
        b_sweep_micros = self.micro_count - prev_micro
        nonzero = [i for i, v in self.tape.items() if v != 0]
        return {
            "bounces": bounces,
            "drop": drop_bites,
            "N": len(bounces),
            "b_sweep_micros": b_sweep_micros,
            "right_boundary": max(nonzero) if nonzero else 0,
        }


def _catch_up_v1(v1, target_micro):
    """Advance v1 by single steps until step_count >= target_micro (or halt)."""
    while v1.step_count < target_micro:
        if not v1.step():
            return


def verify_v5_against_v1(n_super_cycles=200):
    v1 = BigfootV1()
    v5 = BigfootV5()
    if v5.bootstrap_to_first_b_end() is None:
        return False, "v5 halted in bootstrap"
    _catch_up_v1(v1, v5.micro_count)
    for i in range(n_super_cycles):
        if v5.super_cycle_v5() is None:
            return True, f"halted at super-cycle {i+1}"
        _catch_up_v1(v1, v5.micro_count)
        v1_cells = {i: v for i, v in v1.tape.items() if v != 0}
        v5_cells = {i: v for i, v in v5.tape.items() if v != 0}
        if v1.pos != v5.pos or v1.state != v5.state or v1_cells != v5_cells:
            return False, f"mismatch after super-cycle {i+1}"
    return True, "ok"


def fmt(seq, n=50):
    return ", ".join(str(x) for x in seq[:n])


def main():
    print("===== verify v5 == v1 over 200 super-cycles =====")
    ok, msg = verify_v5_against_v1(200)
    print(f"verification: {'PASS' if ok else 'FAIL'} -- {msg}")

    bf = BigfootV5()
    boot_macros, boot_micros = bf.bootstrap_to_first_b_end()
    print(f"\nbootstrap: {boot_macros} macros / {boot_micros} micros to first B-sweep end")

    cycles = []
    for _ in range(300):
        info = bf.super_cycle_v5()
        if info is None:
            break
        cycles.append(info)

    print("\n===== first 30 super-cycles, dance breakdown =====")
    for k, c in enumerate(cycles[:30]):
        bites = c["bounces"] + [c["drop"]]
        print(f"  cycle {k+1:3d}:  N={c['N']:3d}  b_sweep={c['b_sweep_micros']:3d}  "
              f"sum_bites={sum(bites):3d}  bites={bites}")

    print("\n===== extracted integer sequences =====")
    Ns        = [c["N"] for c in cycles]
    drops     = [c["drop"] for c in cycles]
    sum_bites = [sum(c["bounces"]) + c["drop"] for c in cycles]
    max_bites = [max(c["bounces"] + [c["drop"]]) for c in cycles]

    print(f"\nN (bounce count) per cycle, first 50:\n  {fmt(Ns)}")
    print(f"\ndrop bites per cycle, first 50:\n  {fmt(drops)}")
    print(f"\ntotal bites per cycle, first 50:\n  {fmt(sum_bites)}")
    print(f"\nmax single-bounce bites per cycle, first 50:\n  {fmt(max_bites)}")

    all_bites = []
    for c in cycles:
        all_bites.extend(c["bounces"])
        all_bites.append(c["drop"])
    h = Counter(all_bites)
    print(f"\nbite-count distribution across all dance steps:")
    print(f"  total dance steps: {len(all_bites)}")
    print(f"  bite-count histogram:")
    for k in sorted(h.keys())[:20]:
        print(f"    bites={k:3d}: {h[k]} ({100*h[k]/len(all_bites):.1f}%)")

    print(f"\nfirst few full bite vectors:")
    for k, c in enumerate(cycles[:10]):
        print(f"  cycle {k+1}: {c['bounces'] + [c['drop']]}")


if __name__ == "__main__":
    main()
