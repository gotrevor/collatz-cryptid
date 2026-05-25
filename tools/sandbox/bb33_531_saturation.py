#!/usr/bin/env python3
"""Long-run saturation test for Holdout 531's right-side word set.

Hypothesis: 531's right-side word has bounded length (max 24 observed
at 200k loops). If the *reachable set* of right-side words is finite,
531 admits a counter-automaton model and non-halting is largely
decidable.

Method: stream Quick_Sim verbose-simulator output, parse each config,
extract the right-side block-label word (count-stripped), track the
running count of distinct words seen. Log periodically. If
distinct_count saturates (plateau in the curve), reachable set is
finite; if it grows linearly with step count, it's effectively
infinite.

Output: CSV at sim/531_saturation.csv with columns:
    step, total_configs, distinct_words, new_words_in_window,
    current_word_length, max_word_length_so_far
"""
import argparse
import os
import re
import subprocess
import sys
import time
from pathlib import Path

PY = os.path.expanduser("~/.venvs/bb/bin/python")
QS = os.path.expanduser("~/src/busy-beaver/Code/Quick_Sim.py")
SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))
TM_531 = "1RB2LA1LA_2LA0RA2RC_---0LC2RA"

CONFIG_LINE = re.compile(r"^0+\^inf\s+(.+?)\s+0+\^inf$")
BLOCK = re.compile(r"^([0-9]+)\^[\d_]+$")
CELL = re.compile(r"^\(([0-9]+)\)$")
HEAD_LEFT = re.compile(r"^<([ABC])$")
HEAD_RIGHT = re.compile(r"^([ABC])>$")


def split_at_head(tokens):
    for i, t in enumerate(tokens):
        if HEAD_LEFT.match(t):
            return tokens[:i], tokens[i:i + 2], tokens[i + 2:]
        if HEAD_RIGHT.match(t) and i > 0 and CELL.match(tokens[i - 1]):
            return tokens[:i - 1], tokens[i - 1:i + 1], tokens[i + 1:]
    return tokens, [], []


def right_word(config_str: str) -> str:
    """Return canonical right-side block-label word (comma-joined)."""
    tokens = config_str.split()
    _, _, right = split_at_head(tokens)
    out = []
    for t in right:
        m = BLOCK.match(t)
        if m:
            out.append(m.group(1))
            continue
        m = CELL.match(t)
        if m:
            out.append(m.group(1))
            continue
    return ",".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-loops", type=int, default=10_000_000)
    ap.add_argument("--log-every", type=int, default=100_000,
                    help="Report stats every N macro-steps")
    ap.add_argument("--out", default=str(SIM_DIR / "531_saturation.csv"))
    args = ap.parse_args()

    SIM_DIR.mkdir(exist_ok=True)
    out_path = Path(args.out)

    cmd = [
        PY, QS,
        "--recursive",
        "--verbose-simulator",
        "--print-loops", "1",
        "--max-loops", str(args.max_loops),
        "--block-size", "2",
        TM_531,
    ]
    print(f"Streaming: {' '.join(cmd[2:])}", flush=True)

    seen = set()
    step = 0
    new_since_last_log = 0
    max_word_length = 0
    current_word_length = 0

    t0 = time.time()
    with out_path.open("w") as fout:
        fout.write("step,total_configs,distinct_words,new_words_in_window,"
                   "current_word_length,max_word_length_so_far,elapsed_s\n")

        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            bufsize=1,
        )
        try:
            for line in proc.stdout:
                line = line.rstrip("\n")
                m = CONFIG_LINE.match(line)
                if not m:
                    continue
                word = right_word(m.group(1))
                step += 1
                wl = word.count(",") + 1 if word else 0
                current_word_length = wl
                if wl > max_word_length:
                    max_word_length = wl
                pre_size = len(seen)
                seen.add(word)
                if len(seen) > pre_size:
                    new_since_last_log += 1

                if step % args.log_every == 0:
                    elapsed = time.time() - t0
                    fout.write(f"{step},{step},{len(seen)},{new_since_last_log},"
                               f"{current_word_length},{max_word_length},"
                               f"{elapsed:.1f}\n")
                    fout.flush()
                    rate = step / elapsed if elapsed > 0 else 0
                    print(f"step={step:>10,}  distinct={len(seen):>9,}  "
                          f"new+{new_since_last_log:>7,}  "
                          f"wlen={current_word_length:>3}  "
                          f"max_wlen={max_word_length:>3}  "
                          f"elapsed={elapsed:>6.1f}s  "
                          f"rate={rate:>9,.0f}/s", flush=True)
                    new_since_last_log = 0
        finally:
            proc.terminate()
            proc.wait(timeout=5)

    elapsed = time.time() - t0
    print(f"\nDone. {step:,} configs, {len(seen):,} distinct words, {elapsed:.1f}s")
    print(f"CSV: {out_path}")


if __name__ == "__main__":
    main()
