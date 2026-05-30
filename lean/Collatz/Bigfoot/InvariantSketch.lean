import Collatz.Bigfoot.Dynamics
import Collatz.Bigfoot.Hypothesis
import Mathlib.Tactic

/-!
# Bigfoot Hypothesis — Invariant Sketch

This file decomposes the proof of `Bigfoot.Hypothesis` into a sequence of
intermediate claims. As of writing, **the central invariant remains a `sorry`**.
The file's value is in *factoring* the proof obligation cleanly:

1. **`step_ne_none_of_a_ge_one`** — direct: `Dyn.step` only returns `none`
   when `a = 0 ∧ b % 6 = 2`. Provable.

2. **`r2_streak_bound`** — structural: in the orbit, you never get three
   consecutive `b ≡ 2 (mod 6)` events. After two r=2 steps, `c = 2`, and
   the next `b mod 6 ∈ {1, 3, 5}`. Provable by case analysis on `b/6 mod 3`.

3. **`InvariantA`** — the main invariant: `a ≥ 1` whenever `b ≡ 2 (mod 6)`
   on the orbit. **Open** — this is the genuinely hard piece.

4. **`hypothesis_of_invariantA`** — `InvariantA` + step semantics implies
   `Hypothesis`. Provable.

5. **`Hypothesis`** itself follows. Closed except for `InvariantA`.

The 1B-cycle empirical evidence (via the (k, a, b, pat) pure-rule iterator,
notes/17) and the 1M-step direct trajectory check both show `a ≥ 3` at every
r=2 event — a *strictly stronger* statement than `InvariantA`. We state and
attempt only the weaker `a ≥ 1` here, which is precisely what excludes halt.
-/

namespace Collatz.Bigfoot

open Dyn

/-- Computational lemma: `Dyn.step d = none ↔ d.a = 0 ∧ d.b % 6 = 2`. -/
lemma step_eq_none_iff (d : Dyn) :
    Dyn.step d = none ↔ d.a = 0 ∧ d.b % 6 = 2 := by
  unfold Dyn.step
  constructor
  · intro h
    -- Case analysis on b % 6
    have hmod : d.b % 6 < 6 := Nat.mod_lt _ (by decide)
    -- The only branch that returns `none` is r=2 with a=0
    by_cases h0 : d.b % 6 = 0
    · simp [h0] at h
    by_cases h1 : d.b % 6 = 1
    · simp [h0, h1] at h
    by_cases h2 : d.b % 6 = 2
    · simp [h0, h1, h2] at h
      exact ⟨h, h2⟩
    by_cases h3 : d.b % 6 = 3
    · simp [h0, h1, h2, h3] at h
    by_cases h4 : d.b % 6 = 4
    · simp [h0, h1, h2, h3, h4] at h
    -- Then b % 6 = 5
    have h5 : d.b % 6 = 5 := by omega
    simp [h0, h1, h2, h3, h4, h5] at h
  · rintro ⟨ha, hb⟩
    simp [hb, ha]

/-- The orbit reaches `none` only if some earlier state was in the halt
configuration `(a = 0, b % 6 = 2)`. -/
lemma orbit_none_implies_halt_state (n : ℕ) (h : Dyn.orbit n = none) :
    ∃ k < n, ∃ d, Dyn.orbit k = some d ∧ d.a = 0 ∧ d.b % 6 = 2 := by
  induction n with
  | zero => simp [Dyn.orbit] at h
  | succ n ih =>
    -- orbit (n+1) = (orbit n).bind step
    have heq : Dyn.orbit (n + 1) = (Dyn.orbit n).bind Dyn.step := rfl
    rw [heq] at h
    cases hO : Dyn.orbit n with
    | none =>
      -- orbit n = none, so the previous failure happened earlier
      obtain ⟨k, hk, d, hk_orbit, hk_a, hk_b⟩ := ih hO
      exact ⟨k, Nat.lt_succ_of_lt hk, d, hk_orbit, hk_a, hk_b⟩
    | some d =>
      rw [hO] at h
      simp [Option.bind] at h
      -- Dyn.step d = none, so d itself is the halt state
      have := (step_eq_none_iff d).mp h
      exact ⟨n, Nat.lt_succ_self n, d, hO, this.1, this.2⟩

/-- **The main invariant** (statement only): along the orbit, every state with
`b % 6 = 2` has `a ≥ 1`. Equivalently, the halt branch `(a = 0, b % 6 = 2)`
is never reached. -/
def InvariantA : Prop :=
  ∀ n d, Dyn.orbit n = some d → d.b % 6 = 2 → d.a ≥ 1

/-- **The headline theorem**: `InvariantA → Hypothesis`. The reduction is
direct — every halt state has `a = 0`, contradicting the invariant. -/
theorem hypothesis_of_invariantA (hI : InvariantA) : Hypothesis := by
  intro n hne
  -- Suppose orbit n = none. Find the halt state.
  obtain ⟨k, _, d, hk, ha, hb⟩ := orbit_none_implies_halt_state n hne
  -- The invariant says d.a ≥ 1, but d.a = 0.
  have := hI k d hk hb
  omega

/-! ## Streak bound (provable, structural)

After every `r=2` step, the rule sets `c = 2`. If the *next* step is also
`r=2`, then at that next step `c = 2` (the input c, set by the previous
r=2). Then the step after that computes
`new b = 8k + c + 3 = 8k + 5`, so `new b % 6 = (2k + 5) % 6 ∈ {1, 3, 5}` —
never 2. So three consecutive `r=2` steps are impossible. -/

/-- After an `r=2` step, the new state has `c = 2`. -/
lemma c_eq_two_after_r2 (d d' : Dyn) (hr : d.b % 6 = 2) (ha : d.a ≠ 0)
    (hstep : Dyn.step d = some d') : d'.c = 2 := by
  unfold Dyn.step at hstep
  have hne : ¬ d.b % 6 = 0 := by omega
  have hne1 : ¬ d.b % 6 = 1 := by omega
  simp [hne, hne1, hr, ha] at hstep
  rw [← hstep]

/-- After two consecutive `r=2` steps, the next step's `b % 6 ∈ {1, 3, 5}`,
hence is *not* `r=2`. -/
theorem no_three_consecutive_r2
    (d1 d2 d3 : Dyn)
    (hr1 : d1.b % 6 = 2) (ha1 : d1.a ≠ 0)
    (h12 : Dyn.step d1 = some d2)
    (hr2 : d2.b % 6 = 2) (ha2 : d2.a ≠ 0)
    (h23 : Dyn.step d2 = some d3) :
    d3.b % 6 ≠ 2 := by
  -- After d1→d2 (an r=2 step), d2.c = 2.
  have hc2 : d2.c = 2 := c_eq_two_after_r2 d1 d2 hr1 ha1 h12
  -- Apply step to d2 with d2.b % 6 = 2 and d2.c = 2.
  unfold Dyn.step at h23
  have hne0 : ¬ d2.b % 6 = 0 := by omega
  have hne1 : ¬ d2.b % 6 = 1 := by omega
  simp [hne0, hne1, hr2, ha2] at h23
  -- h23 says d3 = ⟨d2.a - 1, 8 * (d2.b / 6) + d2.c + 3, 2⟩
  rw [← h23]
  -- d3.b = 8 * (d2.b / 6) + d2.c + 3 = 8 * (d2.b / 6) + 5  (since d2.c = 2)
  show ¬ (8 * (d2.b / 6) + d2.c + 3) % 6 = 2
  rw [hc2]
  -- Now: (8k + 5) % 6 = (2k + 5) % 6, where 2k+5 is odd ⇒ never 2.
  -- 2k+5 mod 6 ∈ {1, 3, 5} for k mod 3 ∈ {1, 2, 0} respectively.
  intro habs
  -- 8k + 5 ≡ 2 mod 6 ⇒ 8k ≡ -3 ≡ 3 mod 6 ⇒ 2k ≡ 3 mod 6.
  -- But 2k is even and 3 is odd. Contradiction.
  omega

/-! ## What's left

To close `Hypothesis` we need to prove `InvariantA`. Empirically:
- 1M-step direct orbit (Shawn's `Dyn` rule) shows `a ≥ 3` at every r=2 event.
- 1B-cycle pure-rule iterator (notes/17) in our (k, a, b) coordinates shows
  no halt-precursor state.
- Streak analysis (notes/17 §"why a=0 looks unreachable"): r=2 streaks are
  bounded by 2 in length, and the orbital structure suggests `a` accumulates
  at rate ~1/6 per step.

A rigorous proof likely needs an auxiliary invariant relating `a` to the
"deficit" `M_2(n) - M_{1,4}(n)` of r=2 events over compensating r∈{1,4}
events. We have not yet identified a closed-form invariant that captures
this. Candidates we've considered (`a ≥ 2`, `a + f(c) ≥ const`, etc.) all
fail at edge cases.

This is the open mathematical content. -/

/-- The genuine sorry. **This is the open question** — closing it would close
BB(3,3)'s Bigfoot cryptid. -/
theorem invariantA_sorry : InvariantA := by
  sorry

/-- The Bigfoot non-halt theorem, modulo `invariantA_sorry`. -/
theorem Hypothesis_proved : Hypothesis :=
  hypothesis_of_invariantA invariantA_sorry

end Collatz.Bigfoot
