#!/usr/bin/env python3
"""Species taxonomy for Collatz orbits.

A 'species' at depth k is a residue class r mod 2^k (excluding the
degenerate residue 0). Two integers are conspecific at depth k if
their first k fast-Collatz parities agree.

Uses fast T:
    T(n) = (3n + 1) / 2   if n odd
    T(n) = n / 2          if n even

For each smallest positive representative r in {1, ..., 2^K_MAX - 1}:
  - parity_prefix(r): k-bit string (bit i = T^i(r) mod 2)
  - sigma(r):         first step i >= 1 with T^i(r) < r,
                      or -1 if no such i within K_MAX steps.

A species graduates at depth k if sigma(r) <= k.
The Collatz conjecture asserts every species eventually graduates.

Outputs:
  - data/graduation.json: graduation rate per depth
  - data/stubborn.csv:    residue classes with sigma > K_MAX
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

# See notes/02-species-taxonomy.md for the framework.


def enumerate_species(K_MAX: int) -> tuple[list[int], list[int]]:
    """Return (sigma, parity) lists indexed by r in [0, 2^K_MAX).

    sigma[r] = first step at which fast-T iterate drops strictly below r,
               or -1 if not within K_MAX steps. sigma[0] is unused.
    parity[r] = K_MAX-bit integer, bit i = (T^i(r)) mod 2.
    """
    N = 1 << K_MAX
    sigma = [-1] * N
    parity = [0] * N

    for r in range(1, N):
        n = r
        p = 0
        s = -1
        for i in range(K_MAX):
            bit = n & 1
            if bit:
                p |= (1 << i)
                n = (3 * n + 1) >> 1
            else:
                n >>= 1
            if s < 0 and n < r:
                s = i + 1
        sigma[r] = s
        parity[r] = p
    return sigma, parity


def graduation_curve(sigma: list[int], K_MAX: int) -> list[dict]:
    """Cumulative fraction of species mod 2^k that have graduated by depth k.

    Total species at depth k = 2^k - 1 (excluding residue 0).
    """
    curve = []
    for k in range(1, K_MAX + 1):
        total = (1 << k) - 1
        graduated = 0
        upper = 1 << k
        for r in range(1, upper):
            s = sigma[r]
            if 0 < s <= k:
                graduated += 1
        rate = graduated / total
        curve.append({
            "k": k,
            "species": total,
            "graduated": graduated,
            "ungraduated": total - graduated,
            "rate": rate,
        })
    return curve


def main(K_MAX: int) -> None:
    out_dir = Path(__file__).parent / "data"
    out_dir.mkdir(exist_ok=True)

    N = 1 << K_MAX
    print(f"Enumerating species up to depth {K_MAX}: "
          f"{N - 1:,} residue classes...")
    t0 = time.time()
    sigma, parity = enumerate_species(K_MAX)
    enum_time = time.time() - t0
    print(f"  enumeration: {enum_time:.1f}s")

    t0 = time.time()
    curve = graduation_curve(sigma, K_MAX)
    curve_time = time.time() - t0
    print(f"  graduation curve: {curve_time:.2f}s")

    print()
    print(f"{'k':>4} {'species':>12} {'graduated':>12} "
          f"{'ungraduated':>12} {'rate':>11} {'1 - rate':>12}")
    for row in curve:
        gap = 1.0 - row["rate"]
        print(f"{row['k']:>4} {row['species']:>12,} "
              f"{row['graduated']:>12,} {row['ungraduated']:>12,} "
              f"{row['rate']:>11.8f} {gap:>12.2e}")

    (out_dir / "graduation.json").write_text(json.dumps(curve, indent=2))

    stubborn = [r for r in range(1, N) if sigma[r] < 0]
    pct = 100 * len(stubborn) / (N - 1) if N > 1 else 0.0
    print()
    print(f"Stubborn species at depth {K_MAX}: "
          f"{len(stubborn):,} of {N - 1:,} ({pct:.4f}%)")

    if stubborn:
        print()
        print("Smallest 10 stubborn species (residue, parity prefix):")
        for r in stubborn[:10]:
            print(f"  r = {r:>10,}   parity = {parity[r]:0{K_MAX}b}")
        print()
        # popcount of parity prefix - how 1-heavy are these residues?
        ones_distribution = [bin(parity[r]).count("1") for r in stubborn]
        avg_ones = sum(ones_distribution) / len(ones_distribution)
        max_ones = max(ones_distribution)
        min_ones = min(ones_distribution)
        print(f"Parity-prefix popcount among stubborn species:")
        print(f"  min = {min_ones}, mean = {avg_ones:.2f}, "
              f"max = {max_ones} (out of {K_MAX} bits)")
        print(f"  expected popcount if uniform: {K_MAX / 2:.1f}")

    with open(out_dir / "stubborn.csv", "w") as f:
        f.write("r,parity_prefix_int,parity_prefix_bin,popcount\n")
        for r in stubborn:
            p = parity[r]
            f.write(f"{r},{p},{p:0{K_MAX}b},{bin(p).count('1')}\n")

    print()
    print(f"Wrote: {out_dir/'graduation.json'}")
    print(f"Wrote: {out_dir/'stubborn.csv'}")


if __name__ == "__main__":
    K_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    main(K_MAX)
