#!/usr/bin/env python3
"""Substitution-hunt on holdout 397's left-side macro word.

Hypothesis (from notes/12-holdouts-397-531-factor-complexity.md):
the left-side block-label word W[t] of holdout 397 evolves as a
substitution: there exists sigma: Sigma -> Sigma* such that
W[t+1] = sigma(W[t][0]) sigma(W[t][1]) ... sigma(W[t][n-1]).

We test:
  1. Length analysis: how does |W[t]| evolve? Substitutive sequences
     grow exponentially under iterated sigma; if growth is linear, the
     hypothesis is already strained.
  2. Uniform-length substitution (every symbol maps to a string of the
     same length k).
  3. Non-uniform substitution: solve a linear system for per-symbol
     image-lengths L(s), then extract sigma and verify on held-out
     pairs.
  4. k-step substitution (sub-sample every k-th macro-loop).
  5. Boundary-only growth: maybe the word grows by a fixed pattern at
     one end while the interior is stable / shifts.

Outputs: stdout report. Honest about negative results.
"""

import argparse
import os
import sys
from collections import Counter, defaultdict
from pathlib import Path

# Import parser from sibling script
SCRIPT_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/tools/sandbox"))
sys.path.insert(0, str(SCRIPT_DIR))
from bb33_complexity import parse_configs, token_to_symbol  # noqa: E402


SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))


def load_words(trace_path: Path, side: str = "left", limit: int = None):
    """Load all per-snapshot words from a Quick_Sim trace."""
    words = []
    for i, (left, head, right) in enumerate(parse_configs(trace_path)):
        chosen = left if side == "left" else right
        words.append(tuple(token_to_symbol(t) for t in chosen))
        if limit is not None and len(words) >= limit:
            break
    return words


def length_analysis(words):
    lens = [len(w) for w in words]
    print(f"  total snapshots: {len(words)}")
    print(f"  length: min={min(lens)} max={max(lens)} mean={sum(lens)/len(lens):.1f}")
    deltas = [lens[t+1] - lens[t] for t in range(len(lens) - 1)]
    dcount = Counter(deltas)
    print(f"  Delta(len) distribution (top 8 over {len(deltas)} steps):")
    for d, c in dcount.most_common(8):
        print(f"    Delta={d:+d}: {c} ({100*c/len(deltas):.1f}%)")
    return lens, deltas


def uniform_substitution_test(words, k_lengths=(1, 2, 3, 4, 5), pairs_to_check=2000):
    """For each candidate uniform length k, check whether |W[t+1]|
    = k * |W[t]| holds. If so, partition W[t+1] into blocks of length k
    aligned with positions of W[t], and verify every occurrence of the
    same symbol yields the same length-k image."""
    print("\n  -- Uniform-length substitution test --")
    for k in k_lengths:
        # Find pairs where |W[t+1]| == k * |W[t]| (and W[t] is non-empty)
        candidates = [(t, words[t], words[t+1])
                      for t in range(min(len(words) - 1, pairs_to_check))
                      if len(words[t]) > 0 and len(words[t+1]) == k * len(words[t])]
        if not candidates:
            print(f"    k={k}: no pairs satisfy |W'|=k|W|")
            continue
        # Try to fit sigma
        sigma = {}
        conflict = None
        for t, W, Wp in candidates:
            for i, s in enumerate(W):
                img = Wp[i*k:(i+1)*k]
                if s in sigma:
                    if sigma[s] != img:
                        conflict = (t, i, s, sigma[s], img)
                        break
                else:
                    sigma[s] = img
            if conflict:
                break
        if conflict is None:
            print(f"    k={k}: FIT on {len(candidates)} pairs!")
            for s, img in sorted(sigma.items()):
                print(f"      sigma({s}) = {''.join(img) if img else '(empty)'}")
        else:
            t, i, s, expected, got = conflict
            print(f"    k={k}: conflict at t={t}, pos={i}: "
                  f"sigma({s}) was {''.join(expected)!r}, "
                  f"got {''.join(got)!r}")


def variable_length_substitution_test(words, max_pairs=5000):
    """Try to solve for L(s) = |sigma(s)| via the linear system
    |W[t+1]| = sum over positions i of L(W[t][i])
            = sum over symbols s of count(s, W[t]) * L(s).

    Then verify sigma is self-consistent across pairs."""
    print("\n  -- Variable-length substitution test (k=1) --")
    alphabet = sorted(set(s for w in words for s in w))
    n_syms = len(alphabet)
    sym_to_idx = {s: i for i, s in enumerate(alphabet)}
    print(f"    alphabet ({n_syms}): {alphabet}")

    # Build linear system: rows = pairs, cols = symbols, RHS = |W'|.
    # For each pair (W, W'), if |W| > 0, we have one equation.
    rows = []
    rhs = []
    for t in range(min(len(words) - 1, max_pairs)):
        W = words[t]
        Wp = words[t+1]
        if len(W) == 0:
            continue
        row = [0] * n_syms
        for s in W:
            row[sym_to_idx[s]] += 1
        rows.append(row)
        rhs.append(len(Wp))

    if len(rows) < n_syms:
        print(f"    only {len(rows)} non-empty pairs, can't solve for {n_syms} unknowns")
        return None

    # Solve via least-squares (small system).
    try:
        import numpy as np
    except ImportError:
        print("    numpy not available, skipping")
        return None
    A = np.array(rows, dtype=float)
    b = np.array(rhs, dtype=float)
    L_real, residuals, rank, _ = np.linalg.lstsq(A, b, rcond=None)
    print(f"    least-squares solution rank={rank}:")
    for i, s in enumerate(alphabet):
        print(f"      L({s}) = {L_real[i]:.4f}")
    # Round to nearest int and check consistency
    L_int = [int(round(x)) for x in L_real]
    print(f"    rounded L: {dict(zip(alphabet, L_int))}")
    # Per-pair residual after rounding
    pred = A @ np.array(L_int, dtype=float)
    err = (pred - b)
    n_exact = int((err == 0).sum())
    print(f"    pairs where rounded L predicts |W'| exactly: "
          f"{n_exact}/{len(rows)} ({100*n_exact/len(rows):.1f}%)")
    if n_exact < len(rows):
        # Show some failures
        bad = np.where(err != 0)[0][:5]
        print(f"    first failures (idx, expected |W'|, predicted): ")
        for idx in bad:
            print(f"      pair t={idx}: expected={int(b[idx])} predicted={int(pred[idx])}  W={words[idx]}")

    if n_exact == len(rows):
        print("    Length-prediction is exact -> attempt sigma extraction...")
        # Use any one pair with all symbols present, or build sigma incrementally
        sigma = {}
        for t in range(min(len(words) - 1, max_pairs)):
            W = words[t]
            Wp = words[t+1]
            if not W:
                continue
            # Walk W, peel off L(s) characters from Wp for each W[i]
            pos = 0
            ok = True
            for i, s in enumerate(W):
                L = L_int[sym_to_idx[s]]
                img = Wp[pos:pos+L]
                if s in sigma and sigma[s] != img:
                    ok = False
                    break
                sigma[s] = img
                pos += L
            if not ok:
                print(f"    sigma conflict at t={t}, halting")
                return None
            if len(sigma) == n_syms:
                break
        print("    extracted sigma:")
        for s in alphabet:
            img = sigma.get(s, None)
            if img is None:
                print(f"      sigma({s}) = (never seen)")
            else:
                print(f"      sigma({s}) = {' '.join(img) if img else '(empty)'}")
        # Verify on the rest
        return verify_sigma(words, sigma, n_check=min(len(words) - 1, max_pairs))
    return None


def verify_sigma(words, sigma, n_check=5000):
    """Check sigma(W[t]) == W[t+1] across consecutive pairs."""
    print(f"\n    -- Verifying sigma across {n_check} pairs --")
    fails = 0
    first_fail = None
    for t in range(min(len(words) - 1, n_check)):
        W = words[t]
        Wp = words[t+1]
        pred = tuple(sym for s in W for sym in sigma.get(s, ()))
        if pred != Wp:
            fails += 1
            if first_fail is None:
                first_fail = t
    print(f"    fails: {fails}/{n_check}")
    if fails:
        t = first_fail
        W = words[t]
        Wp = words[t+1]
        pred = tuple(sym for s in W for sym in sigma.get(s, ()))
        print(f"    first failure at t={t}:")
        print(f"      W[t]      = {' '.join(W)}")
        print(f"      W[t+1]    = {' '.join(Wp)}")
        print(f"      sigma(W) = {' '.join(pred)}")
    return fails == 0


def k_step_test(words, k_values=(2, 3, 5, 10), max_pairs=2000):
    """Try substitution at cadence k: W[t+k] = sigma(W[t])."""
    print("\n  -- k-step substitution test --")
    for k in k_values:
        # Build sub-sampled sequence
        sub = words[::k]
        print(f"\n    k={k}: subsampled to {len(sub)} words")
        # Try uniform substitution on sub-sequence (length ratios)
        ratios = []
        for t in range(min(len(sub) - 1, max_pairs)):
            if len(sub[t]) > 0:
                ratios.append(len(sub[t+1]) / len(sub[t]))
        if ratios:
            ratios.sort()
            mid = ratios[len(ratios)//2]
            mn, mx = ratios[0], ratios[-1]
            print(f"      |W[t+k]|/|W[t]| range: [{mn:.3f}, {mx:.3f}], median {mid:.3f}")


def boundary_alignment_test(words, n_pairs=1000):
    """For each consecutive pair (W, W'), find longest prefix and
    longest suffix of W that appears as a prefix/suffix of W'. This
    tests boundary-growth: maybe one end is stable and the other end
    extends."""
    print("\n  -- Boundary-alignment test (stable-suffix / stable-prefix) --")
    prefix_match_lens = []
    suffix_match_lens = []
    for t in range(min(len(words) - 1, n_pairs)):
        W = words[t]
        Wp = words[t+1]
        if not W or not Wp:
            continue
        # Longest prefix of W matching prefix of W'
        p = 0
        while p < min(len(W), len(Wp)) and W[p] == Wp[p]:
            p += 1
        # Longest suffix of W matching suffix of W'
        s = 0
        while s < min(len(W), len(Wp)) and W[-1 - s] == Wp[-1 - s]:
            s += 1
        prefix_match_lens.append((p, len(W), len(Wp)))
        suffix_match_lens.append((s, len(W), len(Wp)))

    prefix_match_lens.sort(key=lambda x: x[0])
    suffix_match_lens.sort(key=lambda x: x[0])
    print(f"    median prefix-match: {prefix_match_lens[len(prefix_match_lens)//2][0]}")
    print(f"    median suffix-match: {suffix_match_lens[len(suffix_match_lens)//2][0]}")
    # How often is the *whole* prior word a prefix or suffix of the next?
    n = len(prefix_match_lens)
    whole_prefix = sum(1 for p, lw, lwp in prefix_match_lens if p == lw)
    whole_suffix = sum(1 for s, lw, lwp in suffix_match_lens if s == lw)
    print(f"    W[t] is prefix of W[t+1]: {whole_prefix}/{n} ({100*whole_prefix/n:.1f}%)")
    print(f"    W[t] is suffix of W[t+1]: {whole_suffix}/{n} ({100*whole_suffix/n:.1f}%)")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace",
                        default=str(SIM_DIR / "complexity_397_b2_l200000.txt"))
    parser.add_argument("--side", default="left")
    parser.add_argument("--limit", type=int, default=10000,
                        help="Max snapshots to load")
    args = parser.parse_args()

    trace_path = Path(args.trace)
    print(f"Loading trace: {trace_path}")
    words = load_words(trace_path, side=args.side, limit=args.limit)
    print(f"Loaded {len(words)} words from {trace_path.name}")

    print("\n== Length analysis ==")
    length_analysis(words)

    print("\n== Uniform-length substitution test ==")
    uniform_substitution_test(words)

    print("\n== Variable-length substitution test ==")
    variable_length_substitution_test(words)

    print("\n== k-step test ==")
    k_step_test(words)

    print("\n== Boundary-alignment test ==")
    boundary_alignment_test(words)


if __name__ == "__main__":
    main()
