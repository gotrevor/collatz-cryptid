#!/usr/bin/env python3
"""Extract and probe 397's sweep-run-length sequences.

We have ~624 push runs and ~624 pop runs from the 200k-loop trace.
Question: are these sequences computable by a small recurrence?
  - Case 1: eventually periodic / finite-state. -> 397 EASIER than Bigfoot.
  - Case 2: Bigfoot-shaped finite-parameter recurrence. -> SAME hardness.
  - Case 3: algorithmically random-looking. -> HARDER than Bigfoot.

Tests run:
  1. Print first N push/pop run lengths.
  2. Periodicity at small periods (1..50): look for a window where the
     sequence repeats every period.
  3. Autocorrelation at small lags.
  4. Cycle-net-drift sequence (push_run - pop_run): pattern?
  5. OEIS lookup of first 30 terms of each sequence (web search).
  6. Differences sequence d[k] = run[k+1] - run[k]: distribution + ACF.
  7. Cross-correlate the run-length sequence with cycle index (does
     run length grow linearly with cycle number?).
"""

import argparse
import json
import os
import sys
import urllib.parse
import urllib.request
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/tools/sandbox"))
sys.path.insert(0, str(SCRIPT_DIR))
from bb33_complexity import parse_configs, token_to_symbol  # noqa: E402
from bb33_397_stack_behavior import edit_diagnosis  # noqa: E402

SIM_DIR = Path(os.path.expanduser("~/src/collatz-cryptid/sim"))


def load_words(trace_path, side="left", limit=None):
    words = []
    for left, head, right in parse_configs(trace_path):
        chosen = left if side == "left" else right
        words.append(tuple(token_to_symbol(t) for t in chosen))
        if limit is not None and len(words) >= limit:
            break
    return words


def extract_runs(words):
    actions = []
    for t in range(len(words) - 1):
        kind, _, _ = edit_diagnosis(words[t], words[t+1])
        if kind in ("push", "pop"):
            actions.append(kind)
    runs = []
    if not actions:
        return runs
    cur, n = actions[0], 1
    for k in actions[1:]:
        if k == cur:
            n += 1
        else:
            runs.append((cur, n))
            cur, n = k, 1
    runs.append((cur, n))
    return runs


def check_eventual_period(seq, max_period=100, min_repeats=3):
    """Return smallest period p such that seq has a suffix of length
    >= min_repeats * p that repeats with period p. None if not found."""
    n = len(seq)
    for p in range(1, max_period + 1):
        # Find the longest suffix that is purely periodic at period p
        # i.e., seq[i] == seq[i + p] for all i in [start, n - p - 1].
        # Walk backward from the end to find where periodicity breaks.
        if n < min_repeats * p:
            continue
        i = n - p - 1
        while i >= 0 and seq[i] == seq[i + p]:
            i -= 1
        # Suffix [i+1, n) is periodic at period p; length = n - i - 1
        suffix_len = n - i - 1
        if suffix_len >= min_repeats * p:
            return p, suffix_len
    return None


def autocorr(seq, max_lag=50):
    """Naive autocorrelation: corr(seq[:n-k], seq[k:n])."""
    import math
    n = len(seq)
    mean = sum(seq) / n
    var = sum((x - mean) ** 2 for x in seq) / n
    if var == 0:
        return [(0, 1.0)]
    result = []
    for lag in range(0, max_lag + 1):
        if lag >= n:
            break
        s = 0.0
        for i in range(n - lag):
            s += (seq[i] - mean) * (seq[i + lag] - mean)
        s /= (n - lag) * var
        result.append((lag, s))
    return result


def linear_fit(seq):
    """Simple least-squares slope: run_len ~= a + b * cycle_index."""
    n = len(seq)
    if n < 2:
        return None
    xs = list(range(n))
    mx = sum(xs) / n
    my = sum(seq) / n
    num = sum((xs[i] - mx) * (seq[i] - my) for i in range(n))
    den = sum((xs[i] - mx) ** 2 for i in range(n))
    if den == 0:
        return None
    b = num / den
    a = my - b * mx
    # R^2
    ss_tot = sum((seq[i] - my) ** 2 for i in range(n))
    ss_res = sum((seq[i] - (a + b * xs[i])) ** 2 for i in range(n))
    r2 = 1 - ss_res / ss_tot if ss_tot else 0
    return a, b, r2


def oeis_lookup(seq, n_terms=20, max_attempts=4):
    """Query OEIS for the first n_terms of seq.

    OEIS search API: https://oeis.org/search?q=<comma-separated>&fmt=json
    We trim leading terms progressively if there's no hit.
    Returns list of (id, name) matches."""
    base = "https://oeis.org/search"
    for skip in range(max_attempts):
        terms = seq[skip:skip + n_terms]
        if len(terms) < n_terms:
            break
        q = ",".join(str(t) for t in terms)
        url = f"{base}?q={urllib.parse.quote(q)}&fmt=json"
        try:
            with urllib.request.urlopen(url, timeout=15) as r:
                data = json.loads(r.read().decode())
        except Exception as e:
            print(f"    OEIS lookup failed: {e}")
            return []
        if data.get("count", 0) > 0:
            results = data.get("results") or []
            hits = []
            for entry in results[:8]:
                hits.append((entry.get("number"), entry.get("name", "")[:90]))
            print(f"    OEIS (skip={skip}): {data.get('count')} hits")
            for nid, name in hits:
                print(f"      A{nid:06d}: {name}")
            return hits
        else:
            print(f"    OEIS (skip={skip}): 0 hits for {q[:80]}{'...' if len(q)>80 else ''}")
    return []


def analyze(name, seq):
    print(f"\n========================================")
    print(f"  Sequence: {name}  (length {len(seq)})")
    print(f"========================================")
    print(f"\n  First 30 terms:")
    print(f"    {seq[:30]}")
    print(f"\n  Statistics:")
    print(f"    min={min(seq)} max={max(seq)} mean={sum(seq)/len(seq):.2f}")
    print(f"    unique values: {len(set(seq))}")

    print(f"\n  Eventually-periodic test (period 1..100, min 3 repeats):")
    ep = check_eventual_period(seq, max_period=100, min_repeats=3)
    if ep:
        p, suffix_len = ep
        print(f"    period {p} confirmed over suffix of length {suffix_len}")
    else:
        print(f"    no period <= 100 found with >= 3 repeats")

    print(f"\n  Linear fit (run_len ~= a + b*cycle_index):")
    lf = linear_fit(seq)
    if lf:
        a, b, r2 = lf
        print(f"    a={a:.3f}  b={b:.4f}  R^2={r2:.4f}")
        if abs(b) > 0.01 and r2 > 0.05:
            print(f"    --> drift of {b:.3f} per cycle, fit explains "
                  f"{100*r2:.1f}% of variance")

    print(f"\n  Autocorrelation (lags 1..15):")
    ac = autocorr(seq, max_lag=15)
    for lag, c in ac:
        if lag == 0:
            continue
        bar = "*" * int(abs(c) * 40)
        sign = "+" if c >= 0 else "-"
        print(f"    lag {lag:3d}: {c:+.4f}  {sign}{bar}")

    print(f"\n  OEIS lookup (first 20 terms, with leading-skip tries):")
    oeis_lookup(seq, n_terms=20, max_attempts=4)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace",
                        default=str(SIM_DIR / "complexity_397_b2_l200000.txt"))
    parser.add_argument("--side", default="left")
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--no-oeis", action="store_true",
                        help="Skip OEIS lookups (offline run)")
    args = parser.parse_args()

    trace_path = Path(args.trace)
    print(f"Loading trace: {trace_path}")
    words = load_words(trace_path, side=args.side, limit=args.limit)
    print(f"Loaded {len(words)} words")

    runs = extract_runs(words)
    push_lens = [n for k, n in runs if k == "push"]
    pop_lens = [n for k, n in runs if k == "pop"]
    print(f"\nExtracted {len(push_lens)} push runs, {len(pop_lens)} pop runs")

    # Pairing: (push[i], pop[i]) - paired by sweep cycle
    pairs = []
    expect_push = runs[0][0] == "push"
    i = 0
    while i + 1 < len(runs):
        if runs[i][0] == "push" and runs[i+1][0] == "pop":
            pairs.append((runs[i][1], runs[i+1][1]))
            i += 2
        elif runs[i][0] == "pop" and runs[i+1][0] == "push":
            # cycle starts with pop -- pair as (push[i+1], pop[i])? skip
            i += 1
        else:
            i += 1
    print(f"Push/Pop pairs: {len(pairs)}")
    diff_seq = [p - q for p, q in pairs]

    if args.no_oeis:
        # Monkey-patch to skip
        global oeis_lookup
        def oeis_lookup(*a, **kw):  # noqa
            print("    [OEIS skipped]")
            return []

    analyze("push run lengths", push_lens)
    analyze("pop run lengths", pop_lens)
    analyze("(push - pop) per cycle", diff_seq)


if __name__ == "__main__":
    main()
