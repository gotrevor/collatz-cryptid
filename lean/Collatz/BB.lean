import Mathlib.Tactic
import Mathlib.Logic.Function.Iterate

/-!
# A minimal 3-state, 3-symbol Turing machine framework

Each step does **read, write, move, transition** atomically — the
bbchallenge convention. We deliberately do NOT build on
`Mathlib.Computability.TuringMachine.TM0`, whose `Stmt` decomposes
`write` and `move` into separate steps. Building on TM0 would force
us to introduce intermediate states (`A` writing, `A` moving) for
every bbchallenge transition, doubling state counts and de-syncing
step counters from bbchallenge / Quick_Sim output. Convenience here
outweighs reuse.
-/

namespace BB

inductive Dir | L | R
deriving DecidableEq, Inhabited, Repr

inductive State | A | B | C
deriving DecidableEq, Inhabited, Repr

inductive Sym | s0 | s1 | s2
deriving DecidableEq, Inhabited, Repr

/-- One transition: write a symbol, move, and enter a new state. -/
structure Transition where
  state : State
  write : Sym
  dir : Dir
deriving DecidableEq, Inhabited, Repr

/-- A 3-state 3-symbol TM. `none` = halt at this `(state, symbol)` pair. -/
def Machine := State → Sym → Option Transition

/-- Doubly-infinite tape as a function `ℤ → Sym`. Almost-all-blank is a
property of *reachable* configurations from a blank start; we don't
enforce it on the type. -/
def Tape := ℤ → Sym

namespace Tape

def blank : Tape := fun _ => Sym.s0

def read (t : Tape) (i : ℤ) : Sym := t i

def write (t : Tape) (i : ℤ) (s : Sym) : Tape :=
  fun j => if j = i then s else t j

end Tape

/-- A configuration: state, tape, head position. -/
structure Cfg where
  state : State
  tape : Tape
  pos : ℤ

namespace Cfg

/-- Initial blank-tape configuration with head at position 0 and state `A`. -/
def blank : Cfg := ⟨State.A, Tape.blank, 0⟩

end Cfg

def shift (d : Dir) (i : ℤ) : ℤ :=
  match d with
  | Dir.L => i - 1
  | Dir.R => i + 1

/-- One TM step: read head symbol, look up transition, apply write + move
+ state change. `none` if the machine halts. -/
def step (M : Machine) (c : Cfg) : Option Cfg :=
  (M c.state (c.tape.read c.pos)).map fun t =>
    ⟨t.state, c.tape.write c.pos t.write, shift t.dir c.pos⟩

/-- `n` steps from `c`. `none` if the machine halts before reaching step `n`. -/
def stepN (M : Machine) : ℕ → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (stepN M n c).bind (step M)

/-- The machine never halts starting from configuration `c`. -/
def NeverHalts (M : Machine) (c : Cfg) : Prop :=
  ∀ n : ℕ, stepN M n c ≠ none

end BB
