#!/usr/bin/env -S uv run python3
"""Bootstrap-novelty analysis for BB(3,3) sweep-PDA holdouts.

Reads one or more .reversals.json files (peaks + valleys with full
configs), decomposes each reversal config into (bootstrap, periodic body,
cap), and tracks the *cumulative novelty curve* of bootstrap words per
head signature.

The novelty curve answers the central case-split question for Fat Coyote
(397) and Wily Coyote (531):

  * Saturating → finite reachable bootstrap set → counter-automaton-style
    reduction is possible in Lean.
  * Linear growth → unbounded auxiliary state → strictly harder than
    Bigfoot, no finite parametric form.
  * Logarithmic-ish → ambiguous, want more data.

Outputs CSV for plotting, plus a summary report.

Usage:
    bb33_bootstrap_novelty.py --in sim/397_reversals.json
    bb33_bootstrap_novelty.py --in 397_reversals.json 397_burn_10M_v2.reversals.json \\
                              --summary-csv summary.csv --curves-csv curves.csv
    bb33_bootstrap_novelty.py --smoke-test   # runs on the cached 200k baseline
"""

import argparse
import csv
import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO = Path(os.path.expanduser("~/src/collatz-cryptid"))
DEFAULT_BASELINE = REPO / "sim" / "397_reversals.json"

BLOCK = re.compile(r"^([0-9]+)\^[\d_]+$")


def tok_sym(t):
    m = BLOCK.match(t)
    return m.group(1) if m else t


def find_longest_periodic_window(tokens, max_period=4):
    syms = [tok_sym(t) for t in tokens]
    n = len(syms)
    best = (None, None, 0, None)
    for p in range(1, max_period + 1):
        for start in range(max(0, n - p)):
            i = start
            while i + p < n and syms[i] == syms[i + p]:
                i += 1
            run_len = i - start + p
            if run_len > best[2]:
                pattern = tuple(syms[start:start + p])
                best = (p, start, run_len, pattern)
    return best


def decompose(side_tokens, side_name, max_period=4):
    """Decompose a side of the tape into (bootstrap, periodic body, cap).

    `side_name` is "left" or "right" — determines whether the bootstrap
    lives at the outer edge (left side = leftmost tokens) or at the
    inner edge nearest the head.
    """
    if len(side_tokens) < 4:
        return {"period": None, "pattern": None, "N": 0, "body_len": 0,
                "bootstrap": tuple(tok_sym(t) for t in side_tokens), "cap": ()}
    period, start, run_len, pattern = find_longest_periodic_window(side_tokens, max_period)
    if period is None or run_len < 2:
        return {"period": None, "pattern": None, "N": 0, "body_len": 0,
                "bootstrap": tuple(tok_sym(t) for t in side_tokens), "cap": ()}
    if side_name == "left":
        bootstrap = tuple(tok_sym(t) for t in side_tokens[:start])
        cap = tuple(tok_sym(t) for t in side_tokens[start + run_len:])
    else:
        cap = tuple(tok_sym(t) for t in side_tokens[:start])
        bootstrap = tuple(tok_sym(t) for t in side_tokens[start + run_len:])
    N = run_len // period
    return {"period": period, "pattern": pattern, "body_len": run_len, "N": N,
            "bootstrap": bootstrap, "cap": cap}


def split_left_right(tokens):
    """Return (left_tokens, right_tokens) by locating the head marker."""
    for i, t in enumerate(tokens):
        if t.startswith("<") and i + 1 < len(tokens):
            return tokens[:i], tokens[i + 2:]
        if t.endswith(">") and i > 0:
            return tokens[:i - 1], tokens[i + 1:]
    return None, None


def novelty_curve(snapshots):
    """Per head signature, compute the cumulative-distinct-bootstrap curve.

    Returns: {head_sig: [(snapshot_idx, distinct_left_count, distinct_right_count), ...]}
    """
    by_head = defaultdict(list)
    for s in snapshots:
        sig = (s["head_dir"], s["head_state"], s["cell"])
        left, right = split_left_right(s["tokens"])
        if left is None:
            continue
        L = decompose(left, "left")
        R = decompose(right, "right")
        by_head[sig].append((s["loop"], L["bootstrap"], R["bootstrap"]))

    curves = {}
    for sig, rows in by_head.items():
        seen_L = set()
        seen_R = set()
        curve = []
        for i, (loop, lboot, rboot) in enumerate(rows, start=1):
            seen_L.add(lboot)
            seen_R.add(rboot)
            curve.append((i, loop, len(seen_L), len(seen_R)))
        curves[sig] = curve
    return curves


def saturation_metrics(curve):
    """For a single head-signature novelty curve, compute summary stats.

    Returns dict with: n_snapshots, distinct_L_final, distinct_R_final,
    novel_L_first_decile, novel_L_last_decile, slope_L (linear fit on
    last half), saturation_ratio_L = last_decile_novelty / first_decile_novelty
    (1.0 = no saturation, 0.0 = full saturation).
    """
    n = len(curve)
    if n < 10:
        return None
    decile = max(1, n // 10)
    novel_L_first = curve[decile - 1][2] - 0
    novel_L_last = curve[-1][2] - curve[-decile - 1][2]
    novel_R_first = curve[decile - 1][3] - 0
    novel_R_last = curve[-1][3] - curve[-decile - 1][3]

    # Linear slope over the last half of the curve
    half = n // 2
    xs = list(range(half, n))
    ys_L = [curve[i][2] for i in xs]
    ys_R = [curve[i][3] for i in xs]
    slope_L = _slope(xs, ys_L)
    slope_R = _slope(xs, ys_R)

    return {
        "n_snapshots": n,
        "distinct_L_final": curve[-1][2],
        "distinct_R_final": curve[-1][3],
        "novel_L_first_decile": novel_L_first,
        "novel_L_last_decile": novel_L_last,
        "novel_R_first_decile": novel_R_first,
        "novel_R_last_decile": novel_R_last,
        "sat_ratio_L": novel_L_last / max(1, novel_L_first),
        "sat_ratio_R": novel_R_last / max(1, novel_R_first),
        "slope_L_last_half": slope_L,
        "slope_R_last_half": slope_R,
    }


def _slope(xs, ys):
    n = len(xs)
    if n < 2:
        return None
    mx = sum(xs) / n
    my = sum(ys) / n
    num = sum((xs[i] - mx) * (ys[i] - my) for i in range(n))
    den = sum((xs[i] - mx) ** 2 for i in range(n))
    return num / den if den else None


def analyze_file(path, label=None):
    """Load a .reversals.json and return {label: {peaks: curves, valleys: curves}}."""
    label = label or path.stem
    data = json.load(open(path))
    return {
        "label": label,
        "path": str(path),
        "peaks": novelty_curve(data["peaks"]),
        "valleys": novelty_curve(data["valleys"]),
        "n_peaks": len(data["peaks"]),
        "n_valleys": len(data["valleys"]),
    }


def write_summary_csv(analyses, path):
    """One row per (file, peak_or_valley, head_sig). Columns: saturation metrics."""
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "file", "kind", "head_dir", "head_state", "cell",
            "n_snapshots", "distinct_L_final", "distinct_R_final",
            "novel_L_first_decile", "novel_L_last_decile",
            "novel_R_first_decile", "novel_R_last_decile",
            "sat_ratio_L", "sat_ratio_R",
            "slope_L_last_half", "slope_R_last_half",
        ])
        for a in analyses:
            for kind in ("peaks", "valleys"):
                for sig, curve in sorted(a[kind].items()):
                    m = saturation_metrics(curve)
                    if m is None:
                        continue
                    w.writerow([
                        a["label"], kind, sig[0], sig[1], sig[2],
                        m["n_snapshots"],
                        m["distinct_L_final"], m["distinct_R_final"],
                        m["novel_L_first_decile"], m["novel_L_last_decile"],
                        m["novel_R_first_decile"], m["novel_R_last_decile"],
                        f"{m['sat_ratio_L']:.4f}", f"{m['sat_ratio_R']:.4f}",
                        f"{m['slope_L_last_half']:.6f}" if m['slope_L_last_half'] else "",
                        f"{m['slope_R_last_half']:.6f}" if m['slope_R_last_half'] else "",
                    ])


def write_curves_csv(analyses, path):
    """One row per (file, kind, head_sig, snapshot_idx). Full novelty curves."""
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["file", "kind", "head_dir", "head_state", "cell",
                    "snapshot_idx", "loop", "distinct_L", "distinct_R"])
        for a in analyses:
            for kind in ("peaks", "valleys"):
                for sig, curve in sorted(a[kind].items()):
                    for idx, loop, dL, dR in curve:
                        w.writerow([a["label"], kind, sig[0], sig[1], sig[2],
                                    idx, loop, dL, dR])


def _verdict(ratio):
    if ratio < 0.1:
        return "SATURATING"
    if ratio > 0.5:
        return "UNBOUNDED?"
    return "slowing"


def _slope_str(slope):
    if slope is None:
        return "—"
    return f"{slope:.4f}"


def print_report(analyses):
    for a in analyses:
        print(f"\n========== {a['label']}  ({a['n_peaks']} peaks, {a['n_valleys']} valleys) ==========")
        for kind in ("peaks", "valleys"):
            print(f"\n  --- {kind.upper()} ---")
            for sig, curve in sorted(a[kind].items()):
                m = saturation_metrics(curve)
                if m is None:
                    continue
                print(f"  <{sig[0]} {sig[1]}, cell={sig[2]}>  n={m['n_snapshots']}  "
                      f"distinct_L={m['distinct_L_final']} ({100*m['distinct_L_final']/m['n_snapshots']:.0f}% unique)  "
                      f"distinct_R={m['distinct_R_final']} ({100*m['distinct_R_final']/m['n_snapshots']:.0f}% unique)")
                ratio_L = m['sat_ratio_L']
                ratio_R = m['sat_ratio_R']
                print(f"    L: first +{m['novel_L_first_decile']:5d}  "
                      f"last +{m['novel_L_last_decile']:5d}  "
                      f"ratio={ratio_L:.2f}  slope={_slope_str(m['slope_L_last_half'])}  "
                      f"→ {_verdict(ratio_L)}")
                print(f"    R: first +{m['novel_R_first_decile']:5d}  "
                      f"last +{m['novel_R_last_decile']:5d}  "
                      f"ratio={ratio_R:.2f}  slope={_slope_str(m['slope_R_last_half'])}  "
                      f"→ {_verdict(ratio_R)}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inputs", nargs="+", default=None,
                    help="Path(s) to .reversals.json file(s)")
    ap.add_argument("--label", nargs="+", default=None,
                    help="Optional labels (one per --in file)")
    ap.add_argument("--summary-csv", default=None,
                    help="Per-(file, kind, head_sig) saturation metrics CSV")
    ap.add_argument("--curves-csv", default=None,
                    help="Full per-snapshot novelty curves CSV (for plotting)")
    ap.add_argument("--smoke-test", action="store_true",
                    help="Run on the 200k baseline (sim/397_reversals.json) and exit. "
                         "Confirms the pipeline is wired correctly.")
    args = ap.parse_args()

    if args.smoke_test:
        args.inputs = [str(DEFAULT_BASELINE)]
        args.label = ["baseline_200k"]

    if not args.inputs:
        ap.error("--in is required (or use --smoke-test)")

    if args.label and len(args.label) != len(args.inputs):
        ap.error(f"--label count ({len(args.label)}) must match --in count ({len(args.inputs)})")

    analyses = []
    for i, p in enumerate(args.inputs):
        label = args.label[i] if args.label else None
        analyses.append(analyze_file(Path(p), label=label))

    print_report(analyses)

    if args.summary_csv:
        write_summary_csv(analyses, args.summary_csv)
        print(f"\nSummary CSV: {args.summary_csv}")
    if args.curves_csv:
        write_curves_csv(analyses, args.curves_csv)
        print(f"Curves CSV: {args.curves_csv}")


if __name__ == "__main__":
    main()
