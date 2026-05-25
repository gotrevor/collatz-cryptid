#!/usr/bin/env python3
"""Generate a morning report from overnight BB6 batch run.

Reads ~/src/collatz-cryptid/sim/bb6_run/results.csv and writes
~/src/collatz-cryptid/notes/08-bb6-overnight-results.md
"""

import csv
import os
from collections import Counter, defaultdict
from pathlib import Path

RESULTS = Path(os.path.expanduser(
    "~/src/collatz-cryptid/sim/bb6_run/results.csv"))
OUT = Path(os.path.expanduser(
    "~/src/collatz-cryptid/notes/08-bb6-overnight-results.md"))


def to_bool(s: str) -> bool:
    return str(s).strip().lower() == "true"


def to_int(s: str, default: int = 0) -> int:
    try:
        return int(float(s))
    except (ValueError, TypeError):
        return default


def main() -> None:
    rows: list[dict] = []
    with RESULTS.open() as f:
        reader = csv.DictReader(f)
        for r in reader:
            rows.append(r)

    n = len(rows)
    if n == 0:
        OUT.write_text("# BB(6) Overnight Run\n\nNo results yet.\n")
        return

    # Classification breakdown
    by_class = Counter(r.get("classification", "") for r in rows)

    # Decider verdicts
    lr_decided = [r for r in rows if to_bool(r.get("lr_decided", ""))]
    qs_halted = [r for r in rows if to_bool(r.get("qs_halted", ""))]
    qs_proven_inf = [r for r in rows if to_bool(r.get("qs_proven_inf", ""))]
    cps_success = [r for r in rows if to_bool(r.get("cps_success", ""))]
    cps_inf_loop = [r for r in rows if to_bool(r.get("cps_inf_loop", ""))]

    # Timeouts
    lr_timeouts = sum(1 for r in rows if to_bool(r.get("lin_recur_timeout")))
    qs_timeouts = sum(1 for r in rows if to_bool(r.get("quick_sim_timeout")))
    cps_timeouts = sum(1 for r in rows if to_bool(r.get("cps_timeout")))

    # Quick_Sim rule discoveries (Collatz-rule heavyweights)
    rules_dist = Counter(to_int(r.get("qs_rules"), -1) for r in rows)
    high_rules = sorted(
        rows,
        key=lambda r: to_int(r.get("qs_rules"), -1),
        reverse=True,
    )[:25]

    # Largest Quick_Sim nonzeros (those simulating to a lot of tape)
    high_nonzeros = sorted(
        rows,
        key=lambda r: to_int(r.get("qs_nonzeros"), 0),
        reverse=True,
    )[:25]

    # Total decided (by any decider)
    decided_set = set()
    for r in rows:
        if to_bool(r.get("lr_decided")) or to_bool(r.get("qs_halted")) \
                or to_bool(r.get("qs_proven_inf")) \
                or to_bool(r.get("cps_success")):
            decided_set.add(r["tm"])

    # Average runtimes
    def avg(field: str) -> float:
        vals = []
        for r in rows:
            try:
                vals.append(float(r.get(field, 0)))
            except (ValueError, TypeError):
                pass
        return sum(vals) / len(vals) if vals else 0

    lr_avg = avg("lin_recur_elapsed")
    qs_avg = avg("quick_sim_elapsed")
    cps_avg = avg("cps_elapsed")

    # Build report
    md = []
    md.append("# BB(6) Overnight Run — Results 🌙\n")
    md.append(f"Processed **{n:,}** BB(6) holdout machines (Status=empty in "
              "the bbchallenge community spreadsheet snapshot).\n")
    md.append("## Deciders run\n")
    md.append("| Decider | Settings | Timeout | Avg elapsed |")
    md.append("|---|---|---|---|")
    md.append(f"| Lin_Recur_Detect | max-steps 1e6 | 30 s | {lr_avg:.2f} s |")
    md.append(f"| Quick_Sim | max-loops 10000, recursive | 60 s | {qs_avg:.2f} s |")
    md.append(f"| CPS | block 30, window 60, max-iters 5000 | 60 s | {cps_avg:.2f} s |")
    md.append("")

    md.append("## Headline\n")
    md.append(f"- **Newly decided by some decider**: {len(decided_set):,} / {n:,}")
    md.append(f"  - Lin_Recur translated-cycler: {len(lr_decided):,}")
    md.append(f"  - Quick_Sim reached halt:      {len(qs_halted):,}")
    md.append(f"  - Quick_Sim proven infinite:    {len(qs_proven_inf):,}")
    md.append(f"  - CPS closed:                   {len(cps_success):,}")
    md.append(f"- **Timeouts**: lr={lr_timeouts:,}  qs={qs_timeouts:,}  "
              f"cps={cps_timeouts:,}\n")

    md.append("## Classification breakdown\n")
    md.append("| Classification | Count |")
    md.append("|---|---:|")
    for c, k in by_class.most_common():
        md.append(f"| {c or '(blank)'} | {k:,} |")
    md.append("")

    md.append("## Quick_Sim Collatz-rule distribution\n")
    md.append("How many parametric rules Quick_Sim proved during the bounded "
              "10,000-loop run. More rules = richer accelerable structure.\n")
    md.append("| # rules | machines |")
    md.append("|---:|---:|")
    for k in sorted(rules_dist.keys()):
        if k < 0:
            continue
        md.append(f"| {k} | {rules_dist[k]:,} |")
    md.append("")

    md.append("## Top 25 machines by Quick_Sim Collatz-rule count\n")
    md.append("The candidates most worth a *real* look — machines whose "
              "accelerable structure is richest:\n")
    md.append("| Rules | Nonzeros | Classification | Machine |")
    md.append("|---:|---:|---|---|")
    for r in high_rules:
        k = to_int(r.get("qs_rules"), -1)
        nz = to_int(r.get("qs_nonzeros"), -1)
        cls = (r.get("classification") or "").strip()[:30]
        tm = r["tm"]
        md.append(f"| {k} | {nz} | {cls} | `{tm}` |")
    md.append("")

    md.append("## Top 25 machines by Quick_Sim tape nonzeros\n")
    md.append("Tape size after 10,000 prover loops — proxy for "
              "growth rate. Big = exponential-ish (Bigfoot family). "
              "Small = polynomial-or-slower (153-like family).\n")
    md.append("| Nonzeros | Rules | Classification | Machine |")
    md.append("|---:|---:|---|---|")
    for r in high_nonzeros[:25]:
        nz = to_int(r.get("qs_nonzeros"), -1)
        k = to_int(r.get("qs_rules"), -1)
        cls = (r.get("classification") or "").strip()[:30]
        tm = r["tm"]
        md.append(f"| {nz} | {k} | {cls} | `{tm}` |")
    md.append("")

    if qs_halted:
        md.append("## ⚠️ Quick_Sim reported HALT on supposedly undecided machines\n")
        md.append("This would be a real surprise. If any rows below are real "
                  "and not parser false-positives, the spreadsheet snapshot "
                  "needs updating — these are newly decided.\n")
        md.append("| Machine | Classification | qs_nonzeros |")
        md.append("|---|---|---:|")
        for r in qs_halted[:30]:
            md.append(f"| `{r['tm']}` | "
                      f"{(r.get('classification') or '').strip()} | "
                      f"{to_int(r.get('qs_nonzeros'), -1)} |")
        md.append("")

    if cps_success:
        md.append("## ⚠️ CPS closed on supposedly undecided machines\n")
        md.append("Each row here is a candidate new non-halting proof "
                  "(CPS infinite-loop detection).\n")
        md.append("| Machine | Classification | num_configs |")
        md.append("|---|---|---:|")
        for r in cps_success[:30]:
            md.append(f"| `{r['tm']}` | "
                      f"{(r.get('classification') or '').strip()} | "
                      f"{to_int(r.get('cps_num_configs'), -1)} |")
        md.append("")

    md.append("## Method\n")
    md.append("- Sources: BB(6) community spreadsheet "
              "(`1mMp8bAcTFT91j7azn72liX8NSTwc2E_ozKnOGTfRCfw`), pulled as CSV.")
    md.append("- Filtered to rows with empty `Status` column "
              "(truly undecided as of April 2026 snapshot).")
    md.append("- Tooling: `~/src/busy-beaver/Code/` (Shawn Ligocki's deciders), "
              "Python 3.14 in `~/.venvs/bb`.")
    md.append("- Driver: `~/personal/tools/sandbox/bb6_overnight.py`, "
              "8 parallel workers, results streamed to "
              "`~/src/collatz-cryptid/sim/bb6_run/results.csv`.")
    md.append("- Each machine gets ~150 s budget total across three deciders.")
    md.append("")
    md.append("## Caveat\n")
    md.append("Default decider settings + tight time budgets. These are the "
              "*holdouts* — machines that resisted strong community effort. "
              "Expecting our cursory pass to decide them would be naive. "
              "**Real value is the data shape**: which classes accelerate, "
              "which have rich rule structure, which are tape-quiet. That tells "
              "us where to direct a real follow-up.\n")

    OUT.write_text("\n".join(md))
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
