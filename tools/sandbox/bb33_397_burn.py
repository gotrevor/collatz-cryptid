#!/usr/bin/env python3
"""Stream Quick_Sim on 397 for very long traces, extracting only the
metrics we need - in O(1) memory and writing periodic checkpoints.

This avoids the gigabyte-scale trace file the naive approach would
produce. We track:
  - Per-macro-loop left-stack length, computed by re-parsing the
    config line and counting tokens to the left of the head.
  - Push/pop runs (sign of length delta).
  - Head-signature histogram.
  - Right-side counter N (= count of the head-state-specific 2-symbol
    repeating pattern on the right side).
  - Snapshots of FULL configs at every Kth sweep-cycle boundary, for
    later (a,b,c) extraction.

Output: checkpoints written every CHECKPOINT_LOOPS macro-loops, plus
final summary. Format: JSON.

Usage:
  sandbox bb33_397_burn.py --max-loops 10000000 --out 397_burn_10M.json
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

QS = os.path.expanduser("~/src/busy-beaver/Code/Quick_Sim.py")
PY_BB = os.path.expanduser("~/.venvs/bb/bin/python")
TM_397 = "1RB1LB2LC_1LA2RB1RB_---0LA2LA"
OUT_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))

INDEXED = re.compile(
    r"^\s*(\d+)\s+0+\^inf\s+(.+?)\s+0+\^inf\s+\((\d+),\s*(\d+)\)\s*$"
)
HEAD_LEFT = re.compile(r"^<([ABC])$")
HEAD_RIGHT = re.compile(r"^([ABC])>$")
CELL = re.compile(r"^\(([0-9]+)\)$")
BLOCK = re.compile(r"^([0-9]+)\^[\d_]+$")


def split_at_head(tokens):
    for i, t in enumerate(tokens):
        if HEAD_LEFT.match(t):
            if i + 1 < len(tokens) and CELL.match(tokens[i+1]):
                hs = HEAD_LEFT.match(t).group(1)
                cell = CELL.match(tokens[i+1]).group(1)
                return ("left", hs, cell, i, i+2)
        if HEAD_RIGHT.match(t):
            if i > 0 and CELL.match(tokens[i-1]):
                hs = HEAD_RIGHT.match(t).group(1)
                cell = CELL.match(tokens[i-1]).group(1)
                return ("right", hs, cell, i-1, i+1)
    return None


def count_right_pattern(right_tokens, pattern_pair):
    """Count maximal leading pairs of (s1, s2) in right_tokens."""
    s1, s2 = pattern_pair
    n = 0
    i = 0
    while i + 1 < len(right_tokens):
        m1 = BLOCK.match(right_tokens[i])
        m2 = BLOCK.match(right_tokens[i+1])
        if (m1 and m1.group(1) == s1 and m2 and m2.group(1) == s2):
            n += 1
            i += 2
        else:
            break
    return n


# Per-head-state right-side pattern guess from earlier inspection.
# (head_dir, head_state, cell) -> (right_pattern_pair)
RIGHT_PATTERN = {
    ("left", "C", "20"): ("22", "20"),
    ("left", "C", "22"): ("20", "22"),
    ("left", "A", "02"): ("22", "02"),
    ("left", "A", "22"): ("02", "22"),
    ("right", "B", "11"): ("20", "22"),
    ("right", "B", "21"): ("22", "02"),
    ("right", "B", "22"): ("20", "22"),
    ("right", "B", "12"): None,  # unknown / transient
}


class Burn:
    def __init__(self, out_path, checkpoint_every=500_000, snapshot_every=200_000):
        self.out_path = out_path
        self.checkpoint_every = checkpoint_every
        self.snapshot_every = snapshot_every
        self.last_left_len = None
        self.last_action = None
        self.cur_run_kind = None
        self.cur_run_len = 0
        self.push_runs = []
        self.pop_runs = []
        self.head_count = Counter()
        self.loop_count = 0
        self.start_time = time.time()
        self.N_history = []  # (loop, head_state, N)
        self.snapshots = []  # full config strings at snapshot points
        self.length_history = []  # (loop, |left|, |right|) sampled every snapshot_every

    def feed(self, loop, tokens, raw_line):
        info = split_at_head(tokens)
        if info is None:
            return
        head_dir, head_state, cell, hi_start, hi_end = info
        left = tokens[:hi_start]
        right = tokens[hi_end:]
        left_len = len(left)
        right_len = len(right)

        self.head_count[(head_dir, head_state, cell)] += 1

        # Action detection
        if self.last_left_len is not None:
            dl = left_len - self.last_left_len
            if dl > 0:
                action = "push"
            elif dl < 0:
                action = "pop"
            else:
                action = None  # 'same' or 'replace'

            if action is not None:
                if action == self.cur_run_kind:
                    self.cur_run_len += 1
                else:
                    if self.cur_run_kind == "push":
                        self.push_runs.append(self.cur_run_len)
                    elif self.cur_run_kind == "pop":
                        self.pop_runs.append(self.cur_run_len)
                    self.cur_run_kind = action
                    self.cur_run_len = 1

        self.last_left_len = left_len
        self.loop_count = loop

        # Periodic sampling
        if loop % self.snapshot_every == 0 and loop > 0:
            sig = (head_dir, head_state, cell)
            pat = RIGHT_PATTERN.get(sig)
            N = count_right_pattern(right, pat) if pat else -1
            self.N_history.append((loop, sig, N))
            self.length_history.append((loop, left_len, right_len))
            # Only store a small handful of full configs
            if len(self.snapshots) < 50:
                self.snapshots.append((loop, raw_line.rstrip()))

        if loop % self.checkpoint_every == 0 and loop > 0:
            self.write_checkpoint(partial=True)

    def write_checkpoint(self, partial=False):
        # Close current run for checkpoint snapshot
        push_runs = list(self.push_runs)
        pop_runs = list(self.pop_runs)
        if self.cur_run_kind == "push":
            push_runs.append(self.cur_run_len)
        elif self.cur_run_kind == "pop":
            pop_runs.append(self.cur_run_len)

        head_top = dict(self.head_count.most_common(20))
        head_top_keyed = {f"{d}_{s}_{c}": v for (d, s, c), v in head_top.items()}

        out = {
            "loop_count": self.loop_count,
            "elapsed_s": time.time() - self.start_time,
            "partial": partial,
            "push_runs_count": len(push_runs),
            "pop_runs_count": len(pop_runs),
            "push_run_lens_last_30": push_runs[-30:],
            "pop_run_lens_last_30": pop_runs[-30:],
            "push_run_lens_stats": _stats(push_runs),
            "pop_run_lens_stats": _stats(pop_runs),
            "head_top": head_top_keyed,
            "head_unique_count": len(self.head_count),
            "N_history_recent": self.N_history[-20:],
            "length_history_recent": self.length_history[-10:],
            "snapshots_count": len(self.snapshots),
        }
        # Linear-fit on push runs (slope and intercept)
        if len(push_runs) >= 50:
            out["push_linear_fit"] = _linear_fit(push_runs)
        if len(pop_runs) >= 50:
            out["pop_linear_fit"] = _linear_fit(pop_runs)

        # Write full run sequences and snapshots to side files
        side_runs = self.out_path.with_suffix(".runs.json")
        side_snaps = self.out_path.with_suffix(".snapshots.json")
        with open(side_runs, "w") as f:
            json.dump({"push_runs": push_runs, "pop_runs": pop_runs}, f)
        with open(side_snaps, "w") as f:
            json.dump({"snapshots": self.snapshots,
                       "N_history": self.N_history,
                       "length_history": self.length_history,
                       "head_count": [(list(k), v) for k, v in self.head_count.most_common()]
                       }, f)

        with open(self.out_path, "w") as f:
            json.dump(out, f, indent=2, default=str)

        print(f"[checkpoint at loop {self.loop_count}, t={out['elapsed_s']:.1f}s] "
              f"push={len(push_runs)} pop={len(pop_runs)} "
              f"head_unique={len(self.head_count)}",
              flush=True)


def _stats(seq):
    if not seq:
        return None
    s = sorted(seq)
    n = len(s)
    return {
        "n": n, "min": s[0], "max": s[-1],
        "mean": sum(s) / n,
        "median": s[n // 2],
        "p90": s[int(n * 0.9)],
        "p99": s[int(n * 0.99)],
    }


def _linear_fit(seq):
    n = len(seq)
    xs = list(range(n))
    mx = sum(xs) / n
    my = sum(seq) / n
    num = sum((xs[i] - mx) * (seq[i] - my) for i in range(n))
    den = sum((xs[i] - mx) ** 2 for i in range(n))
    if den == 0:
        return None
    b = num / den
    a = my - b * mx
    ss_tot = sum((seq[i] - my) ** 2 for i in range(n))
    ss_res = sum((seq[i] - (a + b * xs[i])) ** 2 for i in range(n))
    r2 = 1 - ss_res / ss_tot if ss_tot else 0
    return {"intercept": a, "slope": b, "r2": r2, "n": n}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-loops", type=int, default=10_000_000)
    parser.add_argument("--block-size", type=int, default=2)
    parser.add_argument("--out", type=str, required=True,
                        help="Output JSON path (also writes .runs.json and .snapshots.json siblings)")
    parser.add_argument("--checkpoint-every", type=int, default=500_000)
    parser.add_argument("--snapshot-every", type=int, default=200_000)
    args = parser.parse_args()

    out_path = Path(args.out)
    if not out_path.is_absolute():
        out_path = OUT_DIR / out_path
    out_path.parent.mkdir(parents=True, exist_ok=True)

    cmd = [
        PY_BB, QS,
        "--recursive",
        "--verbose-simulator",
        "--print-loops", "1",
        "--max-loops", str(args.max_loops),
        "--block-size", str(args.block_size),
        TM_397,
    ]
    print(f"Launching: {' '.join(cmd)}", flush=True)
    print(f"Writing checkpoints to: {out_path}", flush=True)

    burn = Burn(out_path,
                checkpoint_every=args.checkpoint_every,
                snapshot_every=args.snapshot_every)

    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, bufsize=1,
    )

    try:
        for line in proc.stdout:
            m = INDEXED.match(line)
            if not m:
                continue
            loop = int(m.group(1))
            tokens = m.group(2).split()
            burn.feed(loop, tokens, line)
    except KeyboardInterrupt:
        print("KeyboardInterrupt - finalizing checkpoint", flush=True)
        proc.terminate()
    finally:
        proc.wait(timeout=10)
        burn.write_checkpoint(partial=False)
        print(f"DONE: {burn.loop_count} loops in "
              f"{time.time() - burn.start_time:.1f}s", flush=True)


if __name__ == "__main__":
    main()
