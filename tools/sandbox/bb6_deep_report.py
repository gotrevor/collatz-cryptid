#!/usr/bin/env python3
"""Generate a report from the deep BB6 batch run.

Reads ~/src/collatz-cryptid/sim/bb6_deep_run/results.csv and writes
~/src/collatz-cryptid/notes/09-bb6-deep-results.md.

Also computes delta vs. the shallow run (sim/bb6_run/results.csv).
"""

from __future__ import annotations

import csv
import os
from collections import Counter
from pathlib import Path

DEEP = Path(os.path.expanduser(
    "~/src/collatz-cryptid/sim/bb6_deep_run/results.csv"))
SHALLOW = Path(os.path.expanduser(
    "~/src/collatz-cryptid/sim/bb6_run/results.csv"))
OUT = Path(os.path.expanduser(
    "~/src/collatz-cryptid/notes/09-bb6-deep-results.md"))


def to_bool(s: str) -> bool:
    return str(s).strip().lower() == "true"


def to_int(s: str, default: int = 0) -> int:
    try:
        return int(float(s))
    except (ValueError, TypeError):
        return default


def avg(rows: list, field: str) -> float:
    vals = []
    for r in rows:
        try:
            vals.append(float(r.get(field, 0)))
        except (ValueError, TypeError):
            pass
    return sum(vals) / len(vals) if vals else 0


def load(path: Path) -> list[dict]:
    if not path.exists():
        return []
    with path.open() as f:
        return list(csv.DictReader(f))


def decided_by(r: dict) -> list[str]:
    """Return list of decider names that decided this machine."""
    hits = []
    if to_bool(r.get("qs_halted")):
        hits.append("quick_sim:halt")
    if to_bool(r.get("qs_proven_inf")):
        hits.append("quick_sim:proven_inf")
    for name in ["cps_small", "cps_large",
                 "ctl2_b2", "ctl2_b4", "ctl3_b2", "ctl3_b4"]:
        if to_bool(r.get(f"{name}_success")):
            hits.append(name)
    return hits


def main() -> None:
    rows = load(DEEP)
    shallow_rows = load(SHALLOW)
    n = len(rows)

    if n == 0:
        OUT.write_text("# BB(6) Deep Run\n\nNo results yet.\n")
        return

    # Decided breakdown
    decisions_by_decider: Counter[str] = Counter()
    decided_machines: dict[str, list[str]] = {}
    for r in rows:
        hits = decided_by(r)
        if hits:
            decided_machines[r["tm"]] = hits
            for h in hits:
                decisions_by_decider[h] += 1
    n_decided = len(decided_machines)

    # Classification of decided machines
    decided_by_class: Counter[str] = Counter()
    for r in rows:
        if r["tm"] in decided_machines:
            decided_by_class[r.get("classification", "")] += 1

    # Timeout stats
    timeouts = {}
    for name in ["quick_sim", "cps_small", "cps_large",
                 "ctl2_b2", "ctl2_b4", "ctl3_b2", "ctl3_b4"]:
        timeouts[name] = sum(1 for r in rows
                             if to_bool(r.get(f"{name}_timeout")))

    # Avg elapsed
    avg_elapsed = {}
    for name in ["quick_sim", "cps_small", "cps_large",
                 "ctl2_b2", "ctl2_b4", "ctl3_b2", "ctl3_b4"]:
        avg_elapsed[name] = avg(rows, f"{name}_elapsed")

    # Delta vs shallow
    shallow_decided_set: set[str] = set()
    for r in shallow_rows:
        if (to_bool(r.get("qs_halted")) or to_bool(r.get("qs_proven_inf")) or
                to_bool(r.get("lr_decided")) or to_bool(r.get("cps_success"))):
            shallow_decided_set.add(r["tm"])
    deep_decided_set = set(decided_machines.keys())
    newly_decided_in_deep = deep_decided_set - shallow_decided_set

    # Top by rule count (filtered to non-decided for follow-up signal)
    high_rules = sorted(
        rows,
        key=lambda r: to_int(r.get("qs_rules"), -1),
        reverse=True,
    )[:30]
    high_nonzeros = sorted(
        rows,
        key=lambda r: to_int(r.get("qs_nonzeros"), 0),
        reverse=True,
    )[:30]

    # Build report
    md: list[str] = []
    md.append("# BB(6) Deep Pass - Results 🌊\n")
    md.append(f"Processed **{n:,}** BB(6) holdouts. Second run with beefier "
              "decider settings to test the data-shape thesis from the "
              "shallow run.\n")

    md.append("## Decider lineup\n")
    md.append("| Decider | Settings | Timeout | Avg elapsed | Timed out |")
    md.append("|---|---|---|---|---|")
    md.append(f"| Quick_Sim | max-loops 50000, --recursive, "
              f"--exp-linear-rules | 120 s | "
              f"{avg_elapsed['quick_sim']:.2f} s | "
              f"{timeouts['quick_sim']} |")
    md.append(f"| CPS small | block 30, window 100, max-iters 20000, "
              f"max-configs 50000 | 90 s | "
              f"{avg_elapsed['cps_small']:.2f} s | "
              f"{timeouts['cps_small']} |")
    md.append(f"| CPS large | block 80, window 250, max-iters 10000, "
              f"max-configs 50000 | 120 s | "
              f"{avg_elapsed['cps_large']:.2f} s | "
              f"{timeouts['cps_large']} |")
    md.append(f"| CTL2 (b=2) | cutoff 10000, block 2, offset 0 | 20 s | "
              f"{avg_elapsed['ctl2_b2']:.2f} s | "
              f"{timeouts['ctl2_b2']} |")
    md.append(f"| CTL2 (b=4) | cutoff 5000, block 4, offset 0 | 20 s | "
              f"{avg_elapsed['ctl2_b4']:.2f} s | "
              f"{timeouts['ctl2_b4']} |")
    md.append(f"| CTL3 (b=2) | cutoff 10000, block 2, offset 0 | 20 s | "
              f"{avg_elapsed['ctl3_b2']:.2f} s | "
              f"{timeouts['ctl3_b2']} |")
    md.append(f"| CTL3 (b=4) | cutoff 5000, block 4, offset 0 | 20 s | "
              f"{avg_elapsed['ctl3_b4']:.2f} s | "
              f"{timeouts['ctl3_b4']} |")
    md.append("")

    md.append("## Headline\n")
    md.append(f"- **Total decided by deep pass**: {n_decided:,} / {n:,} "
              f"({n_decided/n*100:.2f}%)")
    md.append(f"- **Newly decided vs shallow run**: "
              f"{len(newly_decided_in_deep):,}")
    md.append("- **Decisions by decider:**")
    for name, c in decisions_by_decider.most_common():
        md.append(f"  - {name}: {c}")
    md.append("")

    if n_decided > 0:
        md.append("## Decided machines\n")
        md.append("| Machine | Classification | Decided by |")
        md.append("|---|---|---|")
        for tm in sorted(decided_machines.keys()):
            cls = next((r.get("classification", "") for r in rows
                        if r["tm"] == tm), "")
            md.append(f"| `{tm}` | {cls} | "
                      f"{', '.join(decided_machines[tm])} |")
        md.append("")

        md.append("## Decided machines by classification\n")
        md.append("| Classification | Decided | (of total in class) |")
        md.append("|---|---:|---:|")
        total_by_class = Counter(r.get("classification", "") for r in rows)
        for cls, cnt in decided_by_class.most_common():
            total = total_by_class.get(cls, 0)
            md.append(f"| {cls or '(blank)'} | {cnt} | {total} |")
        md.append("")

    md.append("## Top 30 by Quick_Sim Collatz-rule count\n")
    md.append("Most accelerable structure - candidates for hand analysis.\n")
    md.append("| Rules | Nonzeros | Decided? | Classification | Machine |")
    md.append("|---:|---:|:---:|---|---|")
    for r in high_rules:
        k = to_int(r.get("qs_rules"), -1)
        nz = to_int(r.get("qs_nonzeros"), -1)
        cls = (r.get("classification") or "").strip()[:30]
        tm = r["tm"]
        dec = "✅" if r["tm"] in decided_machines else ""
        md.append(f"| {k} | {nz} | {dec} | {cls} | `{tm}` |")
    md.append("")

    md.append("## Top 30 by tape nonzeros\n")
    md.append("| Nonzeros | Rules | Decided? | Classification | Machine |")
    md.append("|---:|---:|:---:|---|---|")
    for r in high_nonzeros:
        nz = to_int(r.get("qs_nonzeros"), -1)
        k = to_int(r.get("qs_rules"), -1)
        cls = (r.get("classification") or "").strip()[:30]
        tm = r["tm"]
        dec = "✅" if r["tm"] in decided_machines else ""
        md.append(f"| {nz} | {k} | {dec} | {cls} | `{tm}` |")
    md.append("")

    md.append("## Method\n")
    md.append("- Input: same 1085 undecided BB(6) machines as shallow run.")
    md.append("- Tooling: same (Shawn Ligocki's deciders, Python 3.14).")
    md.append("- Driver: `~/personal/tools/sandbox/bb6_deep.py`, "
              "12 workers, results in `~/src/collatz-cryptid/sim/"
              "bb6_deep_run/results.csv`.")
    md.append("- Lin_Recur dropped from the lineup - shallow run already "
              "ruled out cyclers, and bumping max-steps to 100M just "
              "burned the time budget without deciding anything.")
    md.append("- CPS expanded: small + large block variants with bigger "
              "config budgets. CTL2 / CTL3 added at two block sizes each.")
    md.append("")

    md.append("## Caveat\n")
    md.append("Default settings for each decider plus block/window sweeps "
              "in CPS and CTL. Anything we decide here is a candidate "
              "*new non-halting proof* worth verifying carefully before "
              "claiming. The bbchallenge community has run far more "
              "exhaustive parameter sweeps than this; if our pass finds a "
              "decision the community already explored, the signal is "
              "weak. If our pass finds something they haven't tried at "
              "these exact settings, the signal is stronger.\n")

    OUT.write_text("\n".join(md))
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
