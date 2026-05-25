#!/usr/bin/env python3
"""Count distinct shape signatures in a verbose-simulator Quick_Sim trace.

A "shape" is the sequence of block-types + head, with all counts stripped.
This is the test from 07-153-growth-and-structure.md applied to 397/531.

Bigfoot: ~few shapes, periodic.
153: 121+ shapes in 200 micro-steps (shape explosion).
"""
import re
import sys
import argparse
import subprocess
from collections import Counter
from pathlib import Path


CONFIG_LINE = re.compile(r"^00\^inf\s+(.+?)\s+0?0\^inf$")
BLOCK_N = re.compile(r"^([0-9]+)\^\d+$")
CELL = re.compile(r"^\([0-9]+\)$")
HEAD_LEFT = re.compile(r"^<([ABC])$")
HEAD_RIGHT = re.compile(r"^([ABC])>$")


def shape_of(middle: str):
    """Return a shape signature: tokens with counts stripped."""
    tokens = middle.split()
    out = []
    for t in tokens:
        m = BLOCK_N.match(t)
        if m:
            out.append(f"{m.group(1)}^")  # strip count
            continue
        if CELL.match(t):
            out.append(t)
            continue
        if HEAD_LEFT.match(t) or HEAD_RIGHT.match(t):
            out.append(t)
            continue
        out.append(t)
    return " ".join(out)


def extract_configs(trace_path):
    configs = []
    with open(trace_path) as f:
        for line in f:
            m = CONFIG_LINE.match(line.strip())
            if m:
                configs.append(m.group(1))
    return configs


def run_trace(tm, block_size, max_loops, out_path):
    py = Path.home() / ".venvs/bb/bin/python"
    qs = Path.home() / "src/busy-beaver/Code/Quick_Sim.py"
    args = [
        str(py), str(qs),
        "--recursive",
        "--verbose-simulator",
        "--print-loops", "1",
        "--max-loops", str(max_loops),
    ]
    if block_size:
        args += ["--block-size", str(block_size)]
    args.append(tm)
    print(f"  running {' '.join(args[2:])}", flush=True)
    r = subprocess.run(args, capture_output=True, text=True, timeout=180)
    out_path.write_text(r.stdout)
    return out_path


def analyze(tm, label, block_size, max_loops=500):
    sim_dir = Path.home() / "src/collatz-cryptid/sim"
    sim_dir.mkdir(exist_ok=True)
    trace_path = sim_dir / f"{label}_b{block_size or 'auto'}_trace.txt"
    run_trace(tm, block_size, max_loops, trace_path)
    configs = extract_configs(trace_path)
    shapes = [shape_of(c) for c in configs]
    counter = Counter(shapes)
    print(f"\n=== {label} (block_size={block_size}, max_loops={max_loops}) ===")
    print(f"  configs sampled: {len(configs)}")
    print(f"  distinct shapes: {len(counter)}")
    print(f"  shape ratio: {len(counter) / max(1, len(configs)):.2%}")
    # Top recurring shapes
    print(f"  top 5 shapes by count:")
    for shape, n in counter.most_common(5):
        print(f"    {n:4}× {shape}")
    return len(counter), len(configs)


HOLDOUTS = {
    "397": "1RB1LB2LC_1LA2RB1RB_---0LA2LA",
    "531": "1RB2LA1LA_2LA0RA2RC_---0LC2RA",
    "153": "1RB0LB0RC_2LC2LA1RA_1RA1LC---",
    "Bigfoot": "1RB2RA1LC_2LC1RB2RB_---2LA1LA",
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-loops", type=int, default=500)
    args = parser.parse_args()

    block_sizes = [None, 2, 3, 4]
    results = []
    for label, tm in HOLDOUTS.items():
        for bs in block_sizes:
            try:
                distinct, sampled = analyze(tm, label, bs, args.max_loops)
                results.append((label, bs, distinct, sampled))
            except Exception as e:
                print(f"  ERROR {label} b{bs}: {e}")

    print("\n=== COMPARISON TABLE ===")
    print(f"{'machine':<10} {'block':<6} {'distinct':<10} {'sampled':<10} {'ratio':<8}")
    for label, bs, d, s in results:
        ratio = d / max(1, s)
        print(f"{label:<10} {str(bs):<6} {d:<10} {s:<10} {ratio:.1%}")


if __name__ == "__main__":
    main()
