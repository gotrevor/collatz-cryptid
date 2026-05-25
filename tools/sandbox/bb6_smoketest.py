#!/usr/bin/env python3
"""Smoke test the BB6 overnight runner on 3 machines."""

import sys
sys.path.insert(0, "/Users/gotrevor/src/collatz-cryptid/tools/sandbox")
import bb6_overnight as runner

machines = runner.load_undecided()
print(f"Total undecided: {len(machines):,}")

# Test on first 3
import time
t0 = time.time()
for m in machines[:3]:
    r = runner.process_machine(m)
    print()
    print(f"  TM: {r['tm']}")
    print(f"  class: {r.get('classification', '')[:60]}")
    print(f"  lin_recur: elapsed={r.get('lin_recur_elapsed')}s "
          f"timeout={r.get('lin_recur_timeout')} "
          f"decided={r.get('lr_decided')}")
    print(f"  quick_sim: elapsed={r.get('quick_sim_elapsed')}s "
          f"timeout={r.get('quick_sim_timeout')} "
          f"halted={r.get('qs_halted')} "
          f"rules={r.get('qs_rules')} "
          f"nonzeros={r.get('qs_nonzeros')}")
    print(f"  cps: elapsed={r.get('cps_elapsed')}s "
          f"timeout={r.get('cps_timeout')} "
          f"success={r.get('cps_success')} "
          f"configs={r.get('cps_num_configs')}")
print()
print(f"Total: {time.time()-t0:.1f}s for 3 machines")
