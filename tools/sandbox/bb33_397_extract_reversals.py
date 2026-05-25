#!/usr/bin/env python3
"""Extract full-config snapshots at every sweep-cycle reversal from a
cached Quick_Sim trace.

Streams the trace, tracks left-stack-length deltas, and dumps the
full token string at each push->pop transition (PEAK) and pop->push
transition (VALLEY). Discards intermediate configs.

Output: JSON with two lists (peaks, valleys), each entry being
{loop, config_tokens, head_dir, head_state, cell, left_len, right_len}.
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/tools/sandbox"))
sys.path.insert(0, str(SCRIPT_DIR))

INDEXED = re.compile(
    r"^\s*(\d+)\s+0+\^inf\s+(.+?)\s+0+\^inf\s+\((\d+),\s*(\d+)\)\s*$"
)
HEAD_LEFT = re.compile(r"^<([ABC])$")
HEAD_RIGHT = re.compile(r"^([ABC])>$")
CELL = re.compile(r"^\(([0-9]+)\)$")


def split_at_head(tokens):
    for i, t in enumerate(tokens):
        if HEAD_LEFT.match(t) and i+1 < len(tokens) and CELL.match(tokens[i+1]):
            return ("left", HEAD_LEFT.match(t).group(1),
                    CELL.match(tokens[i+1]).group(1), i, i+2)
        if HEAD_RIGHT.match(t) and i > 0 and CELL.match(tokens[i-1]):
            return ("right", HEAD_RIGHT.match(t).group(1),
                    CELL.match(tokens[i-1]).group(1), i-1, i+1)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trace",
                    default=str(Path(os.path.expanduser(
                        "~/src/collatz-cryptid/sim/complexity_397_b2_l200000.txt"))))
    ap.add_argument("--out",
                    default=str(Path(os.path.expanduser(
                        "~/src/collatz-cryptid/sim/397_reversals.json"))))
    ap.add_argument("--max-loops", type=int, default=None)
    args = ap.parse_args()

    last_left_len = None
    last_action = None  # "push" / "pop" / None (for same / replace)
    prev_config = None
    peaks = []
    valleys = []
    total = 0
    with open(args.trace) as f:
        for line in f:
            m = INDEXED.match(line)
            if not m:
                continue
            loop = int(m.group(1))
            if args.max_loops is not None and loop > args.max_loops:
                break
            tokens = m.group(2).split()
            info = split_at_head(tokens)
            if info is None:
                continue
            hdir, hs, cell, hi_start, hi_end = info
            left_len = hi_start
            right_len = len(tokens) - hi_end
            current = {
                "loop": loop,
                "tokens": tokens,
                "head_dir": hdir,
                "head_state": hs,
                "cell": cell,
                "left_len": left_len,
                "right_len": right_len,
            }
            if last_left_len is not None:
                dl = left_len - last_left_len
                if dl > 0:
                    action = "push"
                elif dl < 0:
                    action = "pop"
                else:
                    action = None  # same / replace
                if action is not None and last_action is not None and action != last_action:
                    # Reversal at the *previous* config (the last config of the prior run).
                    # If prior action was "push", then prev_config is the peak.
                    if last_action == "push":
                        peaks.append(prev_config)
                    else:
                        valleys.append(prev_config)
                if action is not None:
                    last_action = action
            last_left_len = left_len
            prev_config = current
            total += 1

    print(f"Parsed {total} configs")
    print(f"  peaks (push->pop): {len(peaks)}")
    print(f"  valleys (pop->push): {len(valleys)}")

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump({"peaks": peaks, "valleys": valleys}, f)
    print(f"Saved to {out_path}")


if __name__ == "__main__":
    main()
