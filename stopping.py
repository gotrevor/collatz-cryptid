#!/usr/bin/env python3
"""Field guide computations for Collatz cryptids.

For each n in [1, N], record:
  - total stopping time tau(n): steps until orbit reaches 1
  - stopping time sigma(n):     steps until orbit first drops below n
  - peak value and peak/n ratio

Report running champions in each category and dump full champion list to JSON.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path


def trajectory_stats(start: int) -> tuple[int, int, int]:
    """Return (tau, peak, sigma) for the Collatz orbit starting at `start`.

    sigma is the first step at which the orbit drops strictly below `start`.
    For start == 1, both tau and sigma are 0 by convention.
    """
    n = start
    tau = 0
    peak = n
    sigma = 0
    sigma_found = start == 1
    while n != 1:
        if n & 1:
            n = 3 * n + 1
        else:
            n >>= 1
        tau += 1
        if n > peak:
            peak = n
        if not sigma_found and n < start:
            sigma = tau
            sigma_found = True
    return tau, peak, sigma


def main(N: int) -> None:
    out_dir = Path(__file__).parent / "data"
    out_dir.mkdir(exist_ok=True)

    tau_champions: list[tuple[int, int]] = []          # (n, tau)
    altitude_champions: list[tuple[int, int, float]] = []  # (n, peak, ratio)
    sigma_champions: list[tuple[int, int]] = []        # (n, sigma)

    best_tau = -1
    best_ratio = 0.0
    best_sigma = -1

    t0 = time.time()
    for n in range(1, N + 1):
        tau, peak, sigma = trajectory_stats(n)
        if tau > best_tau:
            best_tau = tau
            tau_champions.append((n, tau))
        ratio = peak / n
        if ratio > best_ratio:
            best_ratio = ratio
            altitude_champions.append((n, peak, ratio))
        if n > 1 and sigma > best_sigma:
            best_sigma = sigma
            sigma_champions.append((n, sigma))
    elapsed = time.time() - t0

    result = {
        "N": N,
        "elapsed_sec": round(elapsed, 2),
        "tau_champions": tau_champions,
        "altitude_champions": [
            {"n": n, "peak": peak, "ratio": ratio}
            for n, peak, ratio in altitude_champions
        ],
        "sigma_champions": sigma_champions,
    }
    (out_dir / "champions.json").write_text(json.dumps(result, indent=2))

    print(f"Scanned n in [1, {N:,}] in {elapsed:.1f}s")
    print()
    print("=== tau champions (longest total stopping time) ===")
    print(f"{'n':>12} {'tau':>8}")
    for n, tau in tau_champions[-15:]:
        print(f"{n:>12,} {tau:>8}")
    print()
    print("=== altitude champions (highest peak/n) ===")
    print(f"{'n':>12} {'peak':>18} {'ratio':>10}")
    for n, peak, ratio in altitude_champions[-15:]:
        print(f"{n:>12,} {peak:>18,} {ratio:>10.2f}")
    print()
    print("=== sigma champions (longest first-drop time) ===")
    print(f"{'n':>12} {'sigma':>8}")
    for n, sigma in sigma_champions[-15:]:
        print(f"{n:>12,} {sigma:>8}")
    print()
    print(f"Full champion lists written to {out_dir/'champions.json'}")


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    main(N)
