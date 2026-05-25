#!/usr/bin/env python3
"""Bigfoot TM, v4: same behavior as v1/v2/v3, dance-internals granularity.

Building on v3's observation that the program is

   loop forever:
       dance       (A↔C ping-pong inside the fossil)
       B_sweep     (one big macro scanning the right region)

v4 drills into the dance. Hypothesis from staring at the per-cycle
numbers: every dance decomposes as

   dance = (C_step, A_skim) repeated N+1 times

where the first N (C_step, A_skim) pairs are "BOUNCES" (A_skim
terminates on a 2 → re-enters C) and the LAST pair is the "DROP"
(A_skim terminates on a 0 → enters B, ending the dance).

For each pair, the A_skim can "bite" k≥0 ones before terminating.
The bite count k is the relevant integer state - it's how far A
walked right through the fossil before bouncing or dropping.

   dance shape = [(b_1, "bounce"), (b_2, "bounce"), ..., (b_N, "bounce"), (b_drop, "drop")]

   dance_macros = 2(N+1)
   dance_micros = sum(b_i) + 2(N+1)

We verify the hypothesis by checking dance_macros is always even and
the (C,A) pairing is clean. Then we extract per-cycle (N, [b_1, ...,
b_N, b_drop]) and look at the sequence.
"""

import os
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bigfoot_v1_literal import Bigfoot as BigfootV1
from bigfoot_v3_supercycle import BigfootV3


class BigfootV4(BigfootV3):

    def dance_step(self):
        """Execute ONE (C_step, A_skim) pair from inside the dance.

        Pre-condition: state == C, reading a 1 or 2 (else we'd halt).
        Returns a dict: {
          "kind": "bounce" | "drop" | "halt",
          "bites": int  (number of 1s eaten by the A_skim),
          "macros": 2,
          "micros": int,
        }

        After a "bounce", state == C again (ready for next dance pair).
        After a "drop", state == B (ready for the post-dance B-sweep).
        """
        assert self.state == "C", f"dance_step requires C, got {self.state}"
        micros_before = self.micro_count
        # C step
        alive = self.macro_step()
        if not alive:
            return {"kind": "halt", "bites": 0, "macros": 1,
                    "micros": self.micro_count - micros_before}
        assert self.state == "A", f"C should hand off to A, got {self.state}"
        # A_skim
        a_micros_before = self.micro_count
        alive = self.macro_step()
        if not alive:
            return {"kind": "halt", "bites": 0, "macros": 2,
                    "micros": self.micro_count - micros_before}
        # A_skim's micros = 1 (terminal transition) + bites (1s eaten)
        a_micros = self.micro_count - a_micros_before
        bites = a_micros - 1
        if self.state == "C":
            kind = "bounce"
        elif self.state == "B":
            kind = "drop"
        else:
            kind = "??"
        return {"kind": kind, "bites": bites, "macros": 2,
                "micros": self.micro_count - micros_before}

    def super_cycle_v4(self):
        """Run the dance as a sequence of dance_steps, then the
        post-dance B-sweep. Returns:
          {
            "bounces": [b_1, b_2, ...],   # bite counts of bounce pairs
            "drop": b_drop,
            "N": len(bounces),
            "b_sweep_micros": int,
            "right_boundary": int,
          }
        """
        bounces = []
        while True:
            info = self.dance_step()
            if info["kind"] == "halt":
                return None
            if info["kind"] == "bounce":
                bounces.append(info["bites"])
            elif info["kind"] == "drop":
                drop_bites = info["bites"]
                break
            else:
                raise RuntimeError(f"unexpected dance_step kind: {info['kind']}")
        # Now state == B; run the B-sweep
        prev_micro = self.micro_count
        alive = self.macro_step()
        if not alive:
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


def verify_v4_against_v1(n_super_cycles=200):
    v1 = BigfootV1()
    v4 = BigfootV4()
    boot = v4.bootstrap_to_first_b_end()
    if boot is None:
        return False, "v4 halted in bootstrap"
    while v1.step_count < v4.micro_count:
        if not v1.step():
            break
    for i in range(n_super_cycles):
        info = v4.super_cycle_v4()
        if info is None:
            return True, f"halted at super-cycle {i+1}"
        while v1.step_count < v4.micro_count:
            if not v1.step():
                break
        v1_cells = {i: v for i, v in v1.tape.items() if v != 0}
        v4_cells = {i: v for i, v in v4.tape.items() if v != 0}
        if v1.pos != v4.pos or v1.state != v4.state or v1_cells != v4_cells:
            return False, f"mismatch after super-cycle {i+1}"
    return True, "ok"


def fmt(seq, n=30):
    return ", ".join(str(x) for x in seq[:n])


def main():
    print("===== verify v4 == v1 over 200 super-cycles =====")
    ok, msg = verify_v4_against_v1(200)
    print(f"verification: {'PASS' if ok else 'FAIL'} -- {msg}")

    print("\n===== first 30 super-cycles, dance breakdown =====")
    bf = BigfootV4()
    boot = bf.bootstrap_to_first_b_end()
    print(f"bootstrap: {boot[0]} macros / {boot[1]} micros to first B-sweep end")

    cycles = []
    for k in range(30):
        info = bf.super_cycle_v4()
        if info is None:
            print(f"halted at super-cycle {k+1}")
            break
        cycles.append(info)
        N = info["N"]
        bites = info["bounces"] + [info["drop"]]
        sum_b = sum(bites)
        print(f"  cycle {k+1:3d}:  N={N:3d}  b_sweep={info['b_sweep_micros']:3d}  "
              f"sum_bites={sum_b:3d}  bites={bites}")

    print("\n===== extracted integer sequences =====")
    bf2 = BigfootV4()
    bf2.bootstrap_to_first_b_end()
    cycles2 = []
    for _ in range(300):
        info = bf2.super_cycle_v4()
        if info is None:
            break
        cycles2.append(info)

    Ns = [c["N"] for c in cycles2]
    drops = [c["drop"] for c in cycles2]
    b_sweeps = [c["b_sweep_micros"] for c in cycles2]
    sum_bites = [sum(c["bounces"]) + c["drop"] for c in cycles2]
    max_bites = [max(c["bounces"] + [c["drop"]]) for c in cycles2]

    print(f"\nN (bounce count) per cycle, first 50:")
    print(f"  {fmt(Ns, 50)}")
    print(f"\ndrop bites per cycle, first 50:")
    print(f"  {fmt(drops, 50)}")
    print(f"\ntotal bites per cycle, first 50:")
    print(f"  {fmt(sum_bites, 50)}")
    print(f"\nmax single-bounce bites per cycle, first 50:")
    print(f"  {fmt(max_bites, 50)}")

    # Histograms
    print(f"\nbite-count distribution across all dance steps:")
    all_bites = []
    for c in cycles2:
        all_bites.extend(c["bounces"])
        all_bites.append(c["drop"])
    h = Counter(all_bites)
    print(f"  total dance steps: {len(all_bites)}")
    print(f"  bite-count histogram:")
    for k in sorted(h.keys())[:20]:
        print(f"    bites={k:3d}: {h[k]} ({100*h[k]/len(all_bites):.1f}%)")

    # Cycle 5 quirk: 17 micros in 8 macros means high bites
    if cycles:
        print(f"\nfirst few full bite vectors:")
        for k, c in enumerate(cycles[:10]):
            bites = c["bounces"] + [c["drop"]]
            print(f"  cycle {k+1}: {bites}")


if __name__ == "__main__":
    main()
