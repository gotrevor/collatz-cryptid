#!/usr/bin/env python3
"""Parse Quick_Sim verbose trace of Holdout 153 and discover its macro-state graph.

Each trace line has the form:
    NNN  00^inf <blocks> <head> <blocks> 00^inf  (chain_steps, total_steps)

We parse into (step, left_blocks, head, right_blocks, total_steps),
then group by SHAPE (block types + head identifier, counts stripped),
and look at transitions between shapes.

Goal: see if a small finite set of shapes covers the trace, with consistent
counter arithmetic across transitions.
"""

import re
import sys
from collections import Counter, defaultdict

TRACE = "/Users/gotrevor/src/collatz-cryptid/sim/153_trace.txt"

# Match a row like:
#   123  00^inf 10^3 11^1 (11) B> 12^1 00^inf  (4, 100)
ROW = re.compile(
    r"^\s*(\d+)\s+00\^inf\s+(.+?)\s+00\^inf\s+\((\d+),\s*(\d+)\)\s*$"
)

# A "block" piece between the infinities is one of:
#   XY^n           e.g. 10^3
#   (XY)           e.g. (02) just a single cell, no head
#   <X (YZ)        e.g. <B (02) — left-facing head
#   (YZ) X>        e.g. (11) B> — right-facing head
#   X>             rarely on its own
#   <X             rarely on its own

BLOCK_N = re.compile(r"^([0-9])([0-9])\^(\d+)$")
CELL = re.compile(r"^\(([0-9])([0-9])\)$")
HEAD_LEFT = re.compile(r"^<([ABC])$")
HEAD_RIGHT = re.compile(r"^([ABC])>$")


def parse_middle(middle: str):
    """Parse the part between `00^inf ... 00^inf` into a list of tokens."""
    return middle.split()


def normalize(middle: str):
    """Return ((left_blocks, head, right_blocks), total_count_dict).

    left_blocks/right_blocks: list of (cell_type:str, count:int).
    head: tuple (direction, state, cell_under_head) where direction is
          'L' (facing left) or 'R' (facing right).
    """
    tokens = parse_middle(middle)
    # Find the head — a token sequence that contains '<X' or 'X>'.
    head = None
    head_idx = None
    head_consumed = 0  # how many tokens form the head: 1 (just <X or X>) or 2

    for i, tok in enumerate(tokens):
        if tok.startswith("<"):
            # <X (YZ) is the canonical left-facing head; cell is the next token
            m = HEAD_LEFT.match(tok)
            if m:
                state = m.group(1)
                # next token should be (YZ)
                if i + 1 < len(tokens) and CELL.match(tokens[i + 1]):
                    cell_m = CELL.match(tokens[i + 1])
                    cell = cell_m.group(1) + cell_m.group(2)
                    head = ("L", state, cell)
                    head_idx = i
                    head_consumed = 2
                    break
        elif tok.endswith(">"):
            m = HEAD_RIGHT.match(tok)
            if m:
                state = m.group(1)
                # previous token should be (YZ)
                if head_idx is None and i > 0 and CELL.match(tokens[i - 1]):
                    cell_m = CELL.match(tokens[i - 1])
                    cell = cell_m.group(1) + cell_m.group(2)
                    head = ("R", state, cell)
                    head_idx = i - 1
                    head_consumed = 2
                    break

    if head is None:
        return None  # couldn't parse

    left_tokens = tokens[:head_idx]
    right_tokens = tokens[head_idx + head_consumed:]

    def to_blocks(toks):
        blocks = []
        for t in toks:
            m = BLOCK_N.match(t)
            if m:
                cell = m.group(1) + m.group(2)
                n = int(m.group(3))
                blocks.append((cell, n))
            elif CELL.match(t):
                # bare (XY) without exponent — count 1
                cm = CELL.match(t)
                blocks.append((cm.group(1) + cm.group(2), 1))
            else:
                blocks.append((t, -1))  # unparsed token, flag it
        return blocks

    return (to_blocks(left_tokens), head, to_blocks(right_tokens))


def shape_signature(parsed):
    """Convert parsed config to a shape signature (counts replaced by '?').

    Form: 'cell1 cell2 ... | head | cellA cellB ...'
    """
    left, head, right = parsed
    left_sig = " ".join(c for c, _ in left)
    right_sig = " ".join(c for c, _ in right)
    head_sig = f"{head[0]}-{head[1]}@{head[2]}"
    return f"{left_sig} | {head_sig} | {right_sig}"


def main():
    rows = []
    with open(TRACE) as f:
        for line in f:
            m = ROW.match(line)
            if not m:
                continue
            step = int(m.group(1))
            middle = m.group(2)
            chain = int(m.group(3))
            total = int(m.group(4))
            parsed = normalize(middle)
            if parsed is None:
                continue
            rows.append((step, parsed, chain, total, middle))

    print(f"Parsed {len(rows)} rows from {TRACE}")
    print()

    # Frequency of shape signatures
    sig_count = Counter(shape_signature(p) for _, p, _, _, _ in rows)
    print(f"Distinct shape signatures: {len(sig_count)}")
    print()
    print("Top 25 by frequency:")
    for sig, n in sig_count.most_common(25):
        print(f"  {n:4d}  {sig}")
    print()

    # Transitions: (shape_i -> shape_{i+1})
    transitions = Counter()
    for i in range(len(rows) - 1):
        sig_a = shape_signature(rows[i][1])
        sig_b = shape_signature(rows[i + 1][1])
        transitions[(sig_a, sig_b)] += 1

    print(f"Distinct transitions: {len(transitions)}")
    print()
    print("Top 20 transitions by frequency:")
    for (a, b), n in transitions.most_common(20):
        print(f"  {n:4d}  {a}")
        print(f"        -> {b}")


if __name__ == "__main__":
    main()
