# Print Quick_Sim chain-tape configs when the head is at a tape edge (one side is only 0^inf).
import sys, runpy
code, tm, loops, block = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
sys.path.insert(0, code)
sys.argv = ['Quick_Sim.py', '--manual', '-q', '-p', '-n', block, tm]
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    g = runpy.run_path(code + '/Quick_Sim.py', run_name='__main__')
sim = g['sim']
from Macro import Turing_Machine
n = 0
for i in range(loops):
    if sim.op_state != Turing_Machine.RUNNING: print('STOP', sim.op_state); break
    sim.step()
    L, R = sim.tape.tape
    if len(L) == 1 or len(R) == 1:
        print(i, sim.tape.print_with_state(sim.state)); n += 1
