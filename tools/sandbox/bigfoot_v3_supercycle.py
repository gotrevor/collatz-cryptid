#!/usr/bin/env python3
"""Bigfoot TM, v3: same behavior as v2/v1, super-cycle granularity.

Building on v2's observation that the program decomposes into
"B-sweep right" + "A<->C dance" alternating forever:

   bootstrap (one-time)
   loop forever:
       A<->C dance         (some macros of A/C ping-pong)
       B-sweep right       (one big macro)

We define one SUPER-CYCLE = one dance + one B-sweep. Each super-cycle
ends just after a B-sweep completes (head is in state C, reading a 1
or 2 just left of the right boundary).

We record per-super-cycle stats:
   d_k = number of A/C dance macros (before the B-sweep)
   m_k = micro-steps consumed by the dance
   b_k = micro-steps consumed by the k-th B-sweep
   p_k = head position at end of super-cycle (i.e., right boundary - 1)

If the SEQUENCE of (d_k, m_k, b_k, p_k) satisfies a simple
recurrence, we've found the (a, b, c) integer-counter system that
Shawn Ligocki derived for Bigfoot.

Also includes equivalence verification against v1.
"""

import os
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bigfoot_v1_literal import Bigfoot as BigfootV1
from bigfoot_v2_macro import BigfootV2


class BigfootV3(BigfootV2):
    """Inherits v2's macro_step. Adds super_cycle and bootstrap_to_first_b
    methods."""

    def bootstrap_to_first_b_end(self):
        """Run macro steps from the initial state until we've just
        completed the FIRST B-sweep. After this, state == C and the
        most-recent macro was a B-sweep. Returns (macros_used,
        micros_used)."""
        macros_before = self.macro_count
        micros_before = self.micro_count
        # Run until state transitions from B to C
        while True:
            prev_state = self.state
            prev_micro = self.micro_count
            alive = self.macro_step()
            if not alive:
                return None
            if prev_state == "B" and self.state == "C":
                # Just finished a B-sweep
                return (self.macro_count - macros_before,
                        self.micro_count - micros_before)

    def super_cycle(self):
        """Assumes we're at state C just after a B-sweep.

        Runs the A/C dance until we enter state B (the start of the
        next B-sweep), then runs that B-sweep, ending again at state
        C. Returns dict with per-super-cycle stats.

        Returns None on halt."""
        dance_macros = 0
        dance_micros = 0
        while self.state != "B":
            prev_micro = self.micro_count
            alive = self.macro_step()
            if not alive:
                return None
            dance_macros += 1
            dance_micros += self.micro_count - prev_micro
        # Now state == B, about to run B-sweep
        prev_micro = self.micro_count
        alive = self.macro_step()
        if not alive:
            return None
        b_sweep_micros = self.micro_count - prev_micro
        # Compute right boundary: rightmost nonzero cell
        nonzero_positions = [i for i, v in self.tape.items() if v != 0]
        right_boundary = max(nonzero_positions) if nonzero_positions else 0
        return {
            "dance_macros": dance_macros,
            "dance_micros": dance_micros,
            "b_sweep_micros": b_sweep_micros,
            "total_micros": dance_micros + b_sweep_micros,
            "head_pos_end": self.pos,
            "right_boundary": right_boundary,
        }


def verify_v3_against_v1(n_super_cycles=100):
    """Run v3 by super-cycles, v1 by micro-steps in parallel. Confirm
    they match at every super-cycle boundary."""
    v1 = BigfootV1()
    v3 = BigfootV3()
    boot = v3.bootstrap_to_first_b_end()
    if boot is None:
        return False, "v3 halted in bootstrap"
    # Advance v1 to match v3.micro_count
    while v1.step_count < v3.micro_count:
        if not v1.step():
            break
    # Verify
    v1_cells = {i: v for i, v in v1.tape.items() if v != 0}
    v3_cells = {i: v for i, v in v3.tape.items() if v != 0}
    if v1.pos != v3.pos or v1.state != v3.state or v1_cells != v3_cells:
        return False, f"mismatch after bootstrap"
    # Super-cycle loop
    for i in range(n_super_cycles):
        info = v3.super_cycle()
        if info is None:
            return True, f"halted at super-cycle {i+1}"
        while v1.step_count < v3.micro_count:
            if not v1.step():
                break
        v1_cells = {i: v for i, v in v1.tape.items() if v != 0}
        v3_cells = {i: v for i, v in v3.tape.items() if v != 0}
        if v1.pos != v3.pos or v1.state != v3.state or v1_cells != v3_cells:
            return False, (f"mismatch after super-cycle {i+1}: "
                           f"v1=(pos={v1.pos},state={v1.state}), "
                           f"v3=(pos={v3.pos},state={v3.state})")
    return True, "ok"


def fmt_int_seq(seq, n=30):
    """Format the first n ints with commas."""
    return ", ".join(str(x) for x in seq[:n])


def diff_seq(seq):
    """First differences."""
    return [seq[i+1] - seq[i] for i in range(len(seq) - 1)]


def main():
    print("===== verify v3 == v1 over 200 super-cycles =====")
    ok, msg = verify_v3_against_v1(200)
    print(f"verification: {'PASS' if ok else 'FAIL'} -- {msg}")

    print("\n===== first 30 super-cycles =====")
    bf = BigfootV3()
    boot = bf.bootstrap_to_first_b_end()
    print(f"bootstrap to first B-sweep end: {boot[0]} macros, {boot[1]} micros")

    cycles = []
    for k in range(30):
        info = bf.super_cycle()
        if info is None:
            print(f"halted at super-cycle {k+1}")
            break
        cycles.append(info)
        print(f"  cycle {k+1:3d}:  dance_macros={info['dance_macros']:4d}  "
              f"dance_micros={info['dance_micros']:4d}  "
              f"b_sweep_micros={info['b_sweep_micros']:4d}  "
              f"right_boundary={info['right_boundary']:5d}")

    print("\n===== many more super-cycles, just key sequences =====")
    bf2 = BigfootV3()
    bf2.bootstrap_to_first_b_end()
    cycles2 = []
    for _ in range(200):
        info = bf2.super_cycle()
        if info is None:
            break
        cycles2.append(info)

    b_sweeps = [c["b_sweep_micros"] for c in cycles2]
    dances = [c["dance_micros"] for c in cycles2]
    dance_macros = [c["dance_macros"] for c in cycles2]
    boundaries = [c["right_boundary"] for c in cycles2]

    print(f"\nb_sweep_micros (first 30): {fmt_int_seq(b_sweeps)}")
    print(f"first differences: {fmt_int_seq(diff_seq(b_sweeps), 30)}")
    print(f"\ndance_micros (first 30): {fmt_int_seq(dances)}")
    print(f"first differences: {fmt_int_seq(diff_seq(dances), 30)}")
    print(f"\ndance_macros (first 30): {fmt_int_seq(dance_macros)}")
    print(f"first differences: {fmt_int_seq(diff_seq(dance_macros), 30)}")
    print(f"\nright_boundary (first 30): {fmt_int_seq(boundaries)}")
    print(f"first differences: {fmt_int_seq(diff_seq(boundaries), 30)}")

    # Cumulative stats
    print(f"\nover {len(cycles2)} super-cycles total:")
    print(f"  total dance macros: {sum(dance_macros):,}")
    print(f"  total dance micros: {sum(dances):,}")
    print(f"  total b-sweep micros: {sum(b_sweeps):,}")
    print(f"  total micros: {sum(dances) + sum(b_sweeps):,}")
    print(f"  final right boundary: {boundaries[-1]:,}")
    print(f"  average b-sweep length: {sum(b_sweeps)/len(b_sweeps):.1f}")
    print(f"  average dance length (macros): {sum(dance_macros)/len(dance_macros):.1f}")


if __name__ == "__main__":
    main()
