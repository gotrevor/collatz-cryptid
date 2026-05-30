import Collatz.BB
import Collatz.BB.SideTape

/-!
# Relational step + non-halt framework

The existing `BB.lean` has `step : Machine → Cfg → Option Cfg` (functional).
That's perfect for executing the machine but awkward for proofs about the
*existence* of trajectories. This file adds the relational view used by
`busycoq`:

* `c -[M]-> c'` : one step
* `c -[M]->* c'` : zero-or-more steps (refl-trans closure)
* `c -[M]->+ c'` : one-or-more steps

Plus the headline framework lemma `progress_nonhalt_simple`: given an
indexed family `C : ι → Cfg2` such that every `C i` makes nontrivial
progress to some `C i'`, the machine doesn't halt starting from any
`C i₀`.

We work on the `Cfg2` (side-stream) model because that's what the
BB33_494 proof uses. The iso to `BB.Cfg` is in `Iso.lean`.
-/

namespace BB

/-- A single relational step on the side-stream model. -/
def Step2 (M : Machine) (c c' : Cfg2) : Prop := step2 M c = some c'

/-- Notation matching `busycoq`'s `c -[M]-> c'`. -/
notation:40 c " -[" M "]-> " c' => Step2 M c c'

/-- Reflexive-transitive closure: zero or more steps. -/
inductive Multistep (M : Machine) : Cfg2 → Cfg2 → Prop where
  | refl (c : Cfg2) : Multistep M c c
  | step {c c' c'' : Cfg2} : Step2 M c c' → Multistep M c' c'' → Multistep M c c''

notation:40 c " -[" M "]->* " c' => Multistep M c c'

/-- Transitive (non-reflexive) closure: one or more steps. -/
def MultistepPlus (M : Machine) (c c'' : Cfg2) : Prop :=
  ∃ c', Step2 M c c' ∧ Multistep M c' c''

notation:40 c " -[" M "]->+ " c' => MultistepPlus M c c'

namespace Multistep

variable {M : Machine}

theorem trans {c c' c'' : Cfg2}
    (h₁ : c -[M]->* c') (h₂ : c' -[M]->* c'') : c -[M]->* c'' := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem of_step {c c' : Cfg2} (h : c -[M]-> c') : c -[M]->* c' :=
  .step h (.refl c')

theorem of_plus {c c' : Cfg2} (h : c -[M]->+ c') : c -[M]->* c' := by
  obtain ⟨cm, hs, hr⟩ := h
  exact .step hs hr

end Multistep

namespace MultistepPlus

variable {M : Machine}

theorem of_step {c c' : Cfg2} (h : c -[M]-> c') : c -[M]->+ c' :=
  ⟨c', h, .refl c'⟩

theorem trans_left {c c' c'' : Cfg2}
    (h₁ : c -[M]-> c') (h₂ : c' -[M]->* c'') : c -[M]->+ c'' :=
  ⟨c', h₁, h₂⟩

theorem trans {c c' c'' : Cfg2}
    (h₁ : c -[M]->+ c') (h₂ : c' -[M]->+ c'') : c -[M]->+ c'' := by
  obtain ⟨cm, hs, hr⟩ := h₁
  exact ⟨cm, hs, hr.trans (Multistep.of_plus h₂)⟩

theorem trans_right {c c' c'' : Cfg2}
    (h₁ : c -[M]->* c') (h₂ : c' -[M]->+ c'') : c -[M]->+ c'' := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact ⟨_, hs, Multistep.of_plus (ih h₂)⟩

/-- Append a `Multistep` suffix to a `MultistepPlus`. -/
theorem append {c c' c'' : Cfg2}
    (h₁ : c -[M]->+ c') (h₂ : c' -[M]->* c'') : c -[M]->+ c'' := by
  obtain ⟨cm, hs, hr⟩ := h₁
  exact ⟨cm, hs, hr.trans h₂⟩

end MultistepPlus

/-! ## Halting and non-halting -/

/-- A configuration is halted if the machine has no transition from it. -/
def halted (M : Machine) (c : Cfg2) : Prop := M c.state c.headSym = none

/-- The machine halts starting from `c₀` if some reachable configuration is
halted. Mirrors `busycoq`'s `halts tm c0 := ∃ c, c0 -[tm]->* c ∧ halted tm c`. -/
def halts (M : Machine) (c₀ : Cfg2) : Prop :=
  ∃ c, (c₀ -[M]->* c) ∧ halted M c

/-! ## The framework lemma

If every state in an indexed family makes positive progress to another
state in the same family, the machine cannot halt from any starting
state in the family. This is the only theorem you really need to wield
to close a BB(3,3) holdout via the longitudinal-analysis pattern.
-/

/-- A halted configuration takes no step. -/
theorem halted_no_step {M : Machine} {c c' : Cfg2}
    (hh : halted M c) (hs : c -[M]-> c') : False := by
  unfold Step2 step2 at hs
  rw [halted] at hh
  rw [hh] at hs
  simp at hs

/-- Reaching the halt branch via `→*` requires at least one step from a
non-halted configuration. -/
theorem multistep_halted {M : Machine} {c c' : Cfg2}
    (hh : halted M c) (hm : c -[M]->* c') : c = c' := by
  cases hm with
  | refl => rfl
  | step hs _ => exact absurd hs (fun h => halted_no_step hh h)

/-! ### stepN ↔ Multistep bridge

To prove `progress_nonhalt_simple` we need to do strong induction on the
step count, which requires going through `stepN2` (the deterministic
n-step function). -/

/-- `Multistep` decomposes into some finite number of steps via `stepN2`. -/
theorem multistep_to_stepN {M : Machine} {c c' : Cfg2}
    (h : c -[M]->* c') : ∃ n, stepN2 M n c = some c' := by
  induction h with
  | refl c => exact ⟨0, rfl⟩
  | step hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [stepN2_succ, hs]; exact hn

/-- `MultistepPlus` corresponds to some `n ≥ 1` step count. -/
theorem multistepPlus_to_stepN {M : Machine} {c c' : Cfg2}
    (h : c -[M]->+ c') : ∃ n, 1 ≤ n ∧ stepN2 M n c = some c' := by
  obtain ⟨cm, hs, hr⟩ := h
  obtain ⟨n, hn⟩ := multistep_to_stepN hr
  refine ⟨n + 1, Nat.one_le_iff_ne_zero.mpr (by omega), ?_⟩
  rw [stepN2_succ, hs]; exact hn

/-- `stepN2` over addition: `n + m` steps from `c` = `m` steps from
`(n steps from c)`. -/
theorem stepN2_add (M : Machine) (n m : ℕ) (c : Cfg2) :
    stepN2 M (n + m) c = (stepN2 M n c).bind (stepN2 M m) := by
  induction n generalizing c with
  | zero => simp [stepN2]
  | succ n ih =>
      rw [show n + 1 + m = (n + m) + 1 from by ring]
      rw [stepN2_succ, stepN2_succ]
      cases hs : step2 M c with
      | none => simp
      | some c' => simp [ih c']

/-- A halted configuration can't take one more step. -/
theorem step2_of_halted {M : Machine} {c : Cfg2} (hh : halted M c) :
    step2 M c = none := by
  unfold step2; rw [halted] at hh; rw [hh]; rfl

/-- If `stepN2` reaches a halted config in `n` steps, any further step is `none`. -/
theorem stepN_halt_none {M : Machine} {c c_h : Cfg2} (n k : ℕ)
    (hn : stepN2 M n c = some c_h) (hh : halted M c_h) (hk : 1 ≤ k) :
    stepN2 M (n + k) c = none := by
  rw [stepN2_add, hn]
  simp only [Option.bind_some]
  rcases k with _ | k
  · omega
  · rw [stepN2_succ, step2_of_halted hh]; rfl

/-- `stepN2 ... = some c'` gives a Multistep witness. -/
theorem stepN_to_multistep {M : Machine} :
    ∀ {n} {c c' : Cfg2}, stepN2 M n c = some c' → c -[M]->* c' := by
  intro n
  induction n with
  | zero =>
      intro c c' h
      rw [stepN2] at h
      cases h
      exact Multistep.refl _
  | succ n ih =>
      intro c c' h
      rw [stepN2_succ] at h
      cases hs : step2 M c with
      | none => rw [hs] at h; simp at h
      | some cm =>
          rw [hs] at h
          simp only [Option.bind_some] at h
          exact .step hs (ih h)

/-- Prefix invariance of non-halting. If `c0` reaches `c` and `c` doesn't
halt, then `c0` doesn't halt either. Mirrors busycoq's `multistep_nonhalt`. -/
theorem multistep_nonhalt {M : Machine} {c0 c : Cfg2}
    (hms : c0 -[M]->* c) (hnh : ¬ halts M c) : ¬ halts M c0 := by
  intro ⟨c_h, hms', hh⟩
  obtain ⟨n0, hn0⟩ := multistep_to_stepN hms
  obtain ⟨nH, hnH⟩ := multistep_to_stepN hms'
  apply hnh
  by_cases hle : n0 ≤ nH
  · -- c0 → c in n0; c0 → c_h in nH ≥ n0. So c → c_h in (nH - n0) steps.
    refine ⟨c_h, ?_, hh⟩
    have hsum : n0 + (nH - n0) = nH := by omega
    have hbind : stepN2 M nH c0 =
        (stepN2 M n0 c0).bind (stepN2 M (nH - n0)) := by
      conv_lhs => rw [← hsum]; rw [stepN2_add]
    rw [hbind, hn0] at hnH
    simp only [Option.bind_some] at hnH
    exact stepN_to_multistep hnH
  · -- nH < n0 contradicts c_h halted (would force stepN2 n0 c0 = none).
    push_neg at hle
    exfalso
    have hnone : stepN2 M (nH + (n0 - nH)) c0 = none :=
      stepN_halt_none nH (n0 - nH) hnH hh (by omega)
    have heq : nH + (n0 - nH) = n0 := by omega
    rw [heq] at hnone
    rw [hn0] at hnone
    exact absurd hnone (by simp)

/-- **The headline framework lemma.** If every member of an indexed family
`C : ι → Cfg2` makes positive progress within the family, the machine
doesn't halt starting from any member.

Mirrors `busycoq/verify/TM.v`'s `progress_nonhalt_simple`. Proven by
strong induction on the halt-distance: if there were `n` steps to a
halted config, the family's positive chain step would push us past `n`
to a non-halted config, contradicting the halt. -/
theorem progress_nonhalt_simple {M : Machine} {ι : Type*}
    (C : ι → Cfg2) (i₀ : ι)
    (step_in_fam : ∀ i, ∃ i', C i -[M]->+ C i') :
    ¬ halts M (C i₀) := by
  -- Strengthen: for all i, for all n and c, stepN2 M n (C i) = some c → ¬ halted c.
  suffices h : ∀ n, ∀ i, ∀ c, stepN2 M n (C i) = some c → ¬ halted M c by
    intro ⟨c, hms, hh⟩
    obtain ⟨n, hn⟩ := multistep_to_stepN hms
    exact h n i₀ c hn hh
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro i c hn hh
      -- Get the family chain step
      obtain ⟨i', hpos⟩ := step_in_fam i
      obtain ⟨m, hm1, hm⟩ := multistepPlus_to_stepN hpos
      by_cases hnm : m ≤ n
      · -- m ≤ n: split n = m + (n - m), then IH at n - m < n.
        have hsum : m + (n - m) = n := by omega
        have hsplit : stepN2 M n (C i) =
            (stepN2 M m (C i)).bind (stepN2 M (n - m)) := by
          conv_lhs => rw [← hsum]
          rw [stepN2_add]
        rw [hsplit, hm] at hn
        simp only [Option.bind_some] at hn
        exact ih (n - m) (by omega) i' c hn hh
      · -- m > n: stepN n hits halt; stepN m should be none, contradicting hm.
        push_neg at hnm
        have hnone : stepN2 M (n + (m - n)) (C i) = none :=
          stepN_halt_none n (m - n) hn hh (by omega)
        have hmeq : n + (m - n) = m := by omega
        rw [hmeq] at hnone
        rw [hnone] at hm
        exact absurd hm (by simp)

end BB
