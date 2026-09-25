#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Exact finite-support simulator for BMO #9's published rewrite rules."""

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


def canonical(state: tuple[int, ...]) -> tuple[int, ...]:
    end = len(state)
    while end and state[end - 1] == 0:
        end -= 1
    return state[:end]


def step(state: tuple[int, ...]) -> tuple[int, ...] | None:
    """Return the next stream's finite support, or None on halt."""
    a, b, c = (state + (0, 0, 0))[:3]
    tail = state[3:]
    if a == 0:
        return canonical((3 + b + c,) + tail)
    if a == 1:
        if b == 0:
            return None
        return canonical((b - 1, 0, 1, c + 1) + tail)
    return canonical((a - 2, b + 1, c + 1) + tail)


def probe(steps: int) -> dict:
    state = ()
    head_one = Counter()
    exceptional = []
    for n in range(steps):
        if state and state[0] == 1:
            second = state[1] if len(state) > 1 else 0
            head_one[second % 3] += 1
            if second % 3 != 1 and len(exceptional) < 12:
                exceptional.append([n, list(state[:8])])
        state = step(state)
        if state is None:
            return {"steps": n + 1, "halted": True, "head_one_mod3": dict(head_one),
                    "exceptional": exceptional}
    return {"steps": steps, "halted": False, "head_one_mod3": dict(head_one),
            "exceptional": exceptional, "final_prefix": list(state[:8])}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p_step = sub.add_parser("step")
    p_step.add_argument("state", help="comma-separated finite support, e.g. 1,2,0")
    p_probe = sub.add_parser("probe")
    p_probe.add_argument("steps", type=int)
    sub.add_parser("test")
    args = parser.parse_args()
    if args.command == "test":
        raise SystemExit(subprocess.call([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
                                          str(Path(__file__).parents[2] / "tests" / "test_bmo9_probe.py")]))
    if args.command == "step":
        state = tuple(int(x) for x in args.state.split(",")) if args.state else ()
        if any(x < 0 for x in state):
            parser.error("state entries must be nonnegative")
        result = step(state)
        print(json.dumps(None if result is None else list(result)))
    else:
        if args.steps < 0:
            parser.error("steps must be nonnegative")
        print(json.dumps(probe(args.steps), sort_keys=True))


if __name__ == "__main__":
    main()
