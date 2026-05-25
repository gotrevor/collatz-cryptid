import Collatz.Bigfoot.Machine
import Collatz.Bigfoot.Dynamics
import Collatz.Bigfoot.Hypothesis

/-!
# The Bigfoot reduction interface

Factors the monolithic `sorry` formerly in `Hypothesis.lean` into:

1. **`Reduction`** - an interface bundling the ingredients of a Bigfoot
   reduction: an encoding `enc : Dyn → Cfg`, a step-count function
   `cost`, a `bootstrap` lemma (69 TM steps reach `enc init`), and a
   `sim` lemma (one Dyn step ↔ `cost d` TM steps).
2. **`Reduction.toNeverHalts`** - the *glue* theorem: given any
   `Reduction` and `Hypothesis`, the TM does not halt. **No `sorry`.**
3. **`bigfootReduction`** - a concrete `Reduction` value. 🚧 The remaining
   `sorry` is here, structurally identifying the four obligations
   (encoding, cost, bootstrap, sim). Each is independently dischargeable.
4. **`MachineNeverHalts`** - the original target theorem, now derived
   without `sorry` from `bigfootReduction.toNeverHalts`.

See `notes/11-bigfoot-reduction-anatomy.md` for what each remaining
piece requires.
-/

-- General BB helpers; live at the root `BB` namespace.
namespace BB

/-- Step composition: running `a + b` steps from `c` is the same as
running `b` more steps from the result of running `a` steps. -/
lemma stepN_add (M : Machine) (a b : ℕ) (c : Cfg) :
    stepN M (a + b) c = (stepN M a c).bind (stepN M b) := by
  induction b with
  | zero =>
    cases h : stepN M a c <;> simp [stepN]
  | succ b ih =>
    change stepN M (a + b + 1) c =
      (stepN M a c).bind (fun c' => stepN M (b + 1) c')
    have : stepN M (a + b + 1) c = (stepN M (a + b) c).bind (step M) := rfl
    rw [this, ih]
    cases h : stepN M a c with
    | none => rfl
    | some c' => rfl

/-- Halting is sticky: once halted, stays halted. -/
lemma stepN_none_mono (M : Machine) (c : Cfg) (n k : ℕ)
    (h : stepN M n c = none) : stepN M (n + k) c = none := by
  rw [stepN_add, h]; rfl

end BB

namespace Collatz.Bigfoot

/-- Bundled interface for "Bigfoot's `(a,b,c)` dynamics is the
parametric reduction of the Bigfoot TM." -/
structure Reduction where
  /-- Encoding of a `Dyn` state as a concrete TM configuration. -/
  enc : Dyn → BB.Cfg
  /-- TM micro-step count corresponding to one `Dyn.step` from state `d`. -/
  cost : Dyn → ℕ
  /-- Each Dyn step corresponds to at least one TM step. -/
  cost_pos : ∀ d, 0 < cost d
  /-- After 69 TM micro-steps from blank, the TM is at `enc init`. -/
  bootstrap : BB.stepN machine 69 BB.Cfg.blank = some (enc Dyn.init)
  /-- One `Dyn.step` is simulated by `cost d` TM micro-steps. -/
  sim : ∀ (d d' : Dyn), Dyn.step d = some d' →
        BB.stepN machine (cost d) (enc d) = some (enc d')

/-- The `Dyn` orbit value at step `n`, well-defined under `Hypothesis`. -/
noncomputable def Hypothesis.orbitVal (h : Hypothesis) (n : ℕ) : Dyn :=
  (Dyn.orbit n).get (Option.ne_none_iff_isSome.mp (h n))

lemma Hypothesis.orbit_eq_some (h : Hypothesis) (n : ℕ) :
    Dyn.orbit n = some (Hypothesis.orbitVal h n) := by
  unfold Hypothesis.orbitVal
  exact (Option.some_get _).symm

lemma Hypothesis.orbitVal_zero (h : Hypothesis) :
    Hypothesis.orbitVal h 0 = Dyn.init := by
  have h0 := Hypothesis.orbit_eq_some h 0
  have hinit : (Dyn.orbit 0 : Option Dyn) = some Dyn.init := rfl
  rw [hinit] at h0
  exact (Option.some.inj h0).symm

lemma Hypothesis.step_orbitVal (h : Hypothesis) (n : ℕ) :
    Dyn.step (Hypothesis.orbitVal h n) = some (Hypothesis.orbitVal h (n + 1)) := by
  have hn : Dyn.orbit n = some (Hypothesis.orbitVal h n) :=
    Hypothesis.orbit_eq_some h n
  have hn1 : Dyn.orbit (n + 1) = some (Hypothesis.orbitVal h (n + 1)) :=
    Hypothesis.orbit_eq_some h (n + 1)
  have hbind : Dyn.orbit (n + 1) = (Dyn.orbit n).bind Dyn.step := rfl
  rw [hbind, hn] at hn1
  exact hn1

namespace Reduction

/-- Cumulative TM-step count after `j` Dyn-steps. Starts at 69
(bootstrap) and each Dyn step adds `cost (orbitVal j)`. -/
noncomputable def cumulative (R : Reduction) (h : Hypothesis) : ℕ → ℕ
  | 0 => 69
  | n + 1 => cumulative R h n + R.cost (Hypothesis.orbitVal h n)

/-- After `cumulative R h j` TM steps from blank, the TM is at
`enc (orbitVal h j)`. -/
lemma reaches_orbit (R : Reduction) (h : Hypothesis) (j : ℕ) :
    BB.stepN machine (cumulative R h j) BB.Cfg.blank =
      some (R.enc (Hypothesis.orbitVal h j)) := by
  induction j with
  | zero =>
    change BB.stepN machine 69 BB.Cfg.blank =
      some (R.enc (Hypothesis.orbitVal h 0))
    rw [Hypothesis.orbitVal_zero]
    exact R.bootstrap
  | succ j ih =>
    change BB.stepN machine
      (cumulative R h j + R.cost (Hypothesis.orbitVal h j)) BB.Cfg.blank =
        some (R.enc (Hypothesis.orbitVal h (j + 1)))
    rw [BB.stepN_add, ih]
    change BB.stepN machine (R.cost (Hypothesis.orbitVal h j))
        (R.enc (Hypothesis.orbitVal h j)) =
      some (R.enc (Hypothesis.orbitVal h (j + 1)))
    exact R.sim _ _ (Hypothesis.step_orbitVal h j)

/-- The cumulative cost dominates the index: `n ≤ cumulative R h n`. -/
lemma cumulative_ge (R : Reduction) (h : Hypothesis) (n : ℕ) :
    n ≤ cumulative R h n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    change k + 1 ≤ cumulative R h k + R.cost (Hypothesis.orbitVal h k)
    have := R.cost_pos (Hypothesis.orbitVal h k)
    omega

/-- **The glue theorem.** Given a Bigfoot `Reduction` and the dynamics
`Hypothesis`, the Bigfoot TM does not halt on blank tape.

The proof: for any candidate halt step `n`, the cumulative cost
`cumulative R h n ≥ n` reaches a TM-step count at which `reaches_orbit`
shows the configuration is `some (enc _)`. Halt-stickiness rules out
the TM having halted by step `n` either. -/
theorem toNeverHalts (R : Reduction) (h : Hypothesis) :
    BB.NeverHalts machine BB.Cfg.blank := by
  intro n hcontra
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (cumulative_ge R h n)
  have hnone : BB.stepN machine (cumulative R h n) BB.Cfg.blank = none := by
    rw [hk]
    exact BB.stepN_none_mono machine BB.Cfg.blank n k hcontra
  rw [reaches_orbit R h n] at hnone
  exact Option.some_ne_none _ hnone

end Reduction

/-- 🚧 **Phase D obligation**: exhibit a concrete Bigfoot reduction.

This is a `sorry` on a structured object: discharging it means producing
four pieces - `enc`, `cost`, `cost_pos`, `bootstrap`, `sim` - each a
labelled, type-checked mathematical object. Cf. the *monolithic* `sorry`
in the old `MachineNeverHalts`, which gave a future reader no entry
point. -/
noncomputable def bigfootReduction : Reduction := sorry

/-- **The Bigfoot non-halting theorem** (target of Phase D).

Now derived from the glue with no `sorry` of its own - the sole
remaining obligation is to discharge `bigfootReduction`. -/
theorem MachineNeverHalts (h : Hypothesis) :
    BB.NeverHalts machine BB.Cfg.blank :=
  bigfootReduction.toNeverHalts h

end Collatz.Bigfoot
