#!/usr/bin/env python3
"""Smoke test the deep BB6 runner on 5 machines."""

import sys
sys.path.insert(0, "/Users/gotrevor/src/collatz-cryptid/tools/sandbox")
import bb6_deep as runner

machines = runner.load_undecided()
print(f"Total undecided: {len(machines):,}")

import time
t0 = time.time()
for m in machines[:5]:
    r = runner.process_machine(m)
    print()
    print(f"  TM: {r['tm']}")
    print(f"  class: {(r.get('classification') or '')[:60]}")
    for name in ["lin_recur", "quick_sim", "cps_small", "cps_large",
                 "ctl2", "ctl3"]:
        elapsed = r.get(f"{name}_elapsed", "?")
        timeout = r.get(f"{name}_timeout", False)
        decided = (r.get("lr_decided", False) if name == "lin_recur" else
                   r.get("qs_halted", False) or r.get("qs_proven_inf", False)
                   if name == "quick_sim" else
                   r.get(f"{name}_success", False))
        flag = ""
        if timeout: flag = "[TIMEOUT]"
        elif decided: flag = "🎯 DECIDED"
        print(f"    {name:12s} elapsed={elapsed}s {flag}")
print()
print(f"Total: {time.time()-t0:.1f}s for 5 machines")
