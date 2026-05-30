import Mathlib.Tactic

/-!
# Bigfoot's v6 (k, a, b) recurrence

A closed-form 9-rule recurrence on `(k, a, b, pat)` derived from Bigfoot's TM
via stepwise simulator decompilation (`bigfoot_v1..v6.py`), matching the
canonical TM at 1B+ super-cycles empirically. The end-of-super-cycle tape has
the shape `(1 2)^k 1^a 2^b TAIL` with `TAIL = 1 2` (P1) or `TAIL = ε` (P2,
head inside the `2^b` block).

This file encodes the rule in Lean and proves a structural invariant that
excludes the halting precursor `(pat = P1, a = 0)` — the only state from
which `step` returns `none`.

See `notes/17-bigfoot-v5-recurrence.md` and `HANDOFF.md` for full background.
Source: `tools/sandbox/bigfoot_v6_pure_rule.py`.
-/

namespace Collatz.Bigfoot.V6

/-- End-of-super-cycle tape shape. -/
inductive Pat where
  | P1
  | P2
deriving DecidableEq, Repr

/-- The (k, a, b, pat) state at a super-cycle boundary. -/
structure State where
  k : ℕ
  a : ℕ
  b : ℕ
  pat : Pat
deriving DecidableEq, Repr

open Pat

/-- One step of the v6 rule. Returns `none` exactly when
`(pat = P1, a = 0)` — the would-be halt precursor, which empirically (1B
cycles) is never produced by any rule.

Rules (from `bigfoot_v6_pure_rule.step`):
```
P2(k, a, b)  ->  P1(k, a-4, b+4)                            [P2→P1]

P1, a even:
    a >= 4:   S       P1(k,   a-3,  b+5)
    a == 2:   W       P1(k,   b+4,  0)
    a == 0:   none    (halt precursor)

P1, a odd:
    a >= 11:  B       P1(k,   a-9,  b+11)
    a == 9:   B-coll  P1(k-1, 1,    b+12)
    a == 7:   Q-W     P1(k+1, b+7,  0)
    a == 5:   Q-same  P2(k,   b+7,  2)
    a == 3:   D-W     P1(k-1, b+7,  0)
    a == 1:   Q-kpp   P2(k+1, b,    3)
```
-/
def step (s : State) : Option State :=
  match s.pat with
  | P2 => some ⟨s.k, s.a - 4, s.b + 4, P1⟩
  | P1 =>
    if s.a % 2 = 0 then
      if 4 ≤ s.a then some ⟨s.k, s.a - 3, s.b + 5, P1⟩
      else if s.a = 2 then some ⟨s.k, s.b + 4, 0, P1⟩
      else none
    else
      if 11 ≤ s.a then some ⟨s.k, s.a - 9, s.b + 11, P1⟩
      else if s.a = 9 then some ⟨s.k - 1, 1, s.b + 12, P1⟩
      else if s.a = 7 then some ⟨s.k + 1, s.b + 7, 0, P1⟩
      else if s.a = 5 then some ⟨s.k, s.b + 7, 2, P2⟩
      else if s.a = 3 then some ⟨s.k - 1, s.b + 7, 0, P1⟩
      else some ⟨s.k + 1, s.b, 3, P2⟩

/-- The starting state, matching `bigfoot_v6_pure_rule.INITIAL`. Reached
empirically at cycle 5 of v5's parser; equivalently, by 5 cycles of the
literal TM past the bootstrap. -/
def initial : State := ⟨2, 1, 5, P1⟩

/-- The forward orbit of the v6 rule. -/
def orbit : ℕ → Option State
  | 0     => some initial
  | n + 1 => (orbit n).bind step

/-! ### Orbit sanity checks

The first few super-cycles. Cross-check against `bigfoot_v6_pure_rule.run`:
- 1: Q-kpp on a=1 → P2(3, 5, 3)
- 2: P2→P1     → P1(3, 1, 7)
- 3: Q-kpp     → P2(4, 7, 3)
- 4: P2→P1     → P1(4, 3, 7)
- 5: D-W (a=3) → P1(3, 14, 0)
-/

example : orbit 0 = some ⟨2, 1, 5, P1⟩ := rfl
example : orbit 1 = some ⟨3, 5, 3, P2⟩ := by decide
example : orbit 2 = some ⟨3, 1, 7, P1⟩ := by decide
example : orbit 3 = some ⟨4, 7, 3, P2⟩ := by decide
example : orbit 4 = some ⟨4, 3, 7, P1⟩ := by decide
example : orbit 5 = some ⟨3, 14, 0, P1⟩ := by decide

/-! ## Structural invariant

The invariant has FOUR (a, b, pat) clauses; it deliberately does NOT mention
`k`. The rules `B-coll` and `D-W` decrement `k`, and one might expect that
preservation forces `k ≥ 1` as an input precondition. It doesn't: every
preservation obligation about `(a, b, pat)` goes through without using the
input `k`. The "k_pos" concern is purely about whether the rule continues to
*correspond to the TM* once `k` would underflow — a separate concern from
"the rule never halts". This file proves the latter, cleanly.
-/

/-- Structural invariant on `(a, b, pat)` carried along the orbit. -/
structure Inv (s : State) : Prop where
  /-- P1 states never reach `a = 0` (the only halt precursor). -/
  p1_a_pos  : s.pat = P1 → 1 ≤ s.a
  /-- In P1 with `a = 1`, the b-counter is at least 5. Needed so that the
  next step (Q-kpp) lands in P2 with `a_p2 = b ≥ 5`. -/
  p1_a1_b5  : s.pat = P1 → s.a = 1 → 5 ≤ s.b
  /-- P2 states have `a ≥ 5`. Needed so that the next step (P2→P1) keeps
  `a ≥ 1`. -/
  p2_a_5    : s.pat = P2 → 5 ≤ s.a
  /-- In P2 with `a = 5`, the b-counter equals 3. Needed so that the next
  step (P2→P1) lands with `a = 1, b = 7 ≥ 5`. -/
  p2_a5_b3  : s.pat = P2 → s.a = 5 → s.b = 3

/-! ## Per-rule unfolding lemmas

Each lemma fixes the rule's preconditions on `s` and reads off `step s`. This
keeps the case-by-case proof of `step_preserves_Inv` tidy. (Not `private` so
that the strengthened-invariant work in `V6KPos.lean` can reuse them.) -/

lemma step_P2 {s : State} (h : s.pat = P2) :
    step s = some ⟨s.k, s.a - 4, s.b + 4, P1⟩ := by
  unfold step; rw [h]

lemma step_S {s : State} (hp : s.pat = P1) (he : s.a % 2 = 0)
    (hg : 4 ≤ s.a) :
    step s = some ⟨s.k, s.a - 3, s.b + 5, P1⟩ := by
  unfold step; rw [hp]; simp [he, hg]

lemma step_W {s : State} (hp : s.pat = P1) (ha : s.a = 2) :
    step s = some ⟨s.k, s.b + 4, 0, P1⟩ := by
  unfold step; rw [hp]; simp [ha]

lemma step_halt {s : State} (hp : s.pat = P1) (ha : s.a = 0) :
    step s = none := by
  unfold step; rw [hp]; simp [ha]

lemma step_B {s : State} (hp : s.pat = P1) (ho : s.a % 2 = 1)
    (hg : 11 ≤ s.a) :
    step s = some ⟨s.k, s.a - 9, s.b + 11, P1⟩ := by
  have he : ¬ s.a % 2 = 0 := by omega
  unfold step; rw [hp]; simp [he, hg]

lemma step_Bcoll {s : State} (hp : s.pat = P1) (ha : s.a = 9) :
    step s = some ⟨s.k - 1, 1, s.b + 12, P1⟩ := by
  unfold step; rw [hp]; simp [ha]

lemma step_QW {s : State} (hp : s.pat = P1) (ha : s.a = 7) :
    step s = some ⟨s.k + 1, s.b + 7, 0, P1⟩ := by
  unfold step; rw [hp]; simp [ha]

lemma step_Qsame {s : State} (hp : s.pat = P1) (ha : s.a = 5) :
    step s = some ⟨s.k, s.b + 7, 2, P2⟩ := by
  unfold step; rw [hp]; simp [ha]

lemma step_DW {s : State} (hp : s.pat = P1) (ha : s.a = 3) :
    step s = some ⟨s.k - 1, s.b + 7, 0, P1⟩ := by
  unfold step; rw [hp]; simp [ha]

lemma step_Qkpp {s : State} (hp : s.pat = P1) (ha : s.a = 1) :
    step s = some ⟨s.k + 1, s.b, 3, P2⟩ := by
  unfold step; rw [hp]; simp [ha]

/-! ## Invariant holds at initial state -/

/-- `Inv` holds at the starting state. -/
theorem Inv_initial : Inv initial := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> first | decide | (rename_i h; cases h)

/-! ## Step semantics from `Inv`

Two small consequences of `Inv` that we need below: `step` always returns
`some` (the orbit doesn't halt locally), and the output state is determined
by the firing rule. -/

/-- If `Inv s` holds, then `step s` is not the halt branch. The four invariant
clauses combine to rule out `(pat = P1, a = 0)`. -/
theorem step_ne_none_of_Inv {s : State} (hI : Inv s) : step s ≠ none := by
  cases hpat : s.pat with
  | P2 => rw [step_P2 hpat]; simp
  | P1 =>
    by_cases hae : s.a % 2 = 0
    · by_cases hg4 : 4 ≤ s.a
      · rw [step_S hpat hae hg4]; simp
      · by_cases ha2 : s.a = 2
        · rw [step_W hpat ha2]; simp
        · -- a even, < 4, ≠ 2 → a = 0; Inv says a ≥ 1, contradiction
          have ha0 : s.a = 0 := by omega
          have hpos := hI.p1_a_pos hpat
          omega
    · have ho : s.a % 2 = 1 := by omega
      by_cases hg11 : 11 ≤ s.a
      · rw [step_B hpat ho hg11]; simp
      · by_cases ha9 : s.a = 9
        · rw [step_Bcoll hpat ha9]; simp
        · by_cases ha7 : s.a = 7
          · rw [step_QW hpat ha7]; simp
          · by_cases ha5 : s.a = 5
            · rw [step_Qsame hpat ha5]; simp
            · by_cases ha3 : s.a = 3
              · rw [step_DW hpat ha3]; simp
              · have ha1 : s.a = 1 := by omega
                rw [step_Qkpp hpat ha1]; simp

/-! ## Invariant is preserved by `step`

Case-split on `s.pat`, then on the value of `s.a`. Each branch uses the
matching per-rule unfolding lemma. The four invariant clauses close by
`omega` (plus a single appeal to one prior clause of `Inv s` for the cases
that need an inductive hypothesis). -/

/-- `step` preserves `Inv`. -/
theorem step_preserves_Inv {s s' : State} (hI : Inv s)
    (hstep : step s = some s') : Inv s' := by
  cases hpat : s.pat with
  | P2 =>
    rw [step_P2 hpat] at hstep
    have hs := Option.some.inj hstep
    subst hs
    have h5 : 5 ≤ s.a := hI.p2_a_5 hpat
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _; change 1 ≤ s.a - 4; omega
    · intro _ h1
      change s.a - 4 = 1 at h1
      have h5eq : s.a = 5 := by omega
      have hb3 := hI.p2_a5_b3 hpat h5eq
      change 5 ≤ s.b + 4; omega
    · intro h; cases h
    · intro h _; cases h
  | P1 =>
    by_cases hae : s.a % 2 = 0
    · by_cases hg4 : 4 ≤ s.a
      · rw [step_S hpat hae hg4] at hstep
        have hs := Option.some.inj hstep; subst hs
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro _; change 1 ≤ s.a - 3; omega
        · intro _ _; change 5 ≤ s.b + 5; omega
        · intro h; cases h
        · intro h _; cases h
      · by_cases ha2 : s.a = 2
        · rw [step_W hpat ha2] at hstep
          have hs := Option.some.inj hstep; subst hs
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro _; change 1 ≤ s.b + 4; omega
          · intro _ h1
            change s.b + 4 = 1 at h1
            exfalso; omega
          · intro h; cases h
          · intro h _; cases h
        · have ha0 : s.a = 0 := by omega
          rw [step_halt hpat ha0] at hstep
          cases hstep
    · have ho : s.a % 2 = 1 := by omega
      by_cases hg11 : 11 ≤ s.a
      · rw [step_B hpat ho hg11] at hstep
        have hs := Option.some.inj hstep; subst hs
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro _; change 1 ≤ s.a - 9; omega
        · intro _ h1
          change s.a - 9 = 1 at h1
          -- s.a - 9 = 1 → s.a = 10, but s.a is odd ≥ 11
          exfalso; omega
        · intro h; cases h
        · intro h _; cases h
      · by_cases ha9 : s.a = 9
        · rw [step_Bcoll hpat ha9] at hstep
          have hs := Option.some.inj hstep; subst hs
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro _; change 1 ≤ 1; omega
          · intro _ _; change 5 ≤ s.b + 12; omega
          · intro h; cases h
          · intro h _; cases h
        · by_cases ha7 : s.a = 7
          · rw [step_QW hpat ha7] at hstep
            have hs := Option.some.inj hstep; subst hs
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro _; change 1 ≤ s.b + 7; omega
            · intro _ h1
              change s.b + 7 = 1 at h1
              exfalso; omega
            · intro h; cases h
            · intro h _; cases h
          · by_cases ha5 : s.a = 5
            · rw [step_Qsame hpat ha5] at hstep
              have hs := Option.some.inj hstep; subst hs
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro h; cases h
              · intro h _; cases h
              · intro _; change 5 ≤ s.b + 7; omega
              · intro _ h
                change s.b + 7 = 5 at h
                exfalso; omega
            · by_cases ha3 : s.a = 3
              · rw [step_DW hpat ha3] at hstep
                have hs := Option.some.inj hstep; subst hs
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro _; change 1 ≤ s.b + 7; omega
                · intro _ h1
                  change s.b + 7 = 1 at h1
                  exfalso; omega
                · intro h; cases h
                · intro h _; cases h
              · have ha1 : s.a = 1 := by omega
                rw [step_Qkpp hpat ha1] at hstep
                have hs := Option.some.inj hstep; subst hs
                have hb5 := hI.p1_a1_b5 hpat ha1
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro h; cases h
                · intro h _; cases h
                · intro _; exact hb5
                · intro _ _; rfl

/-! ## Closure: orbit-wide invariant and no-halt -/

/-- `Inv` holds on every reachable state. -/
theorem orbit_Inv : ∀ n s, orbit n = some s → Inv s := by
  intro n
  induction n with
  | zero =>
    intro s h
    have : s = initial := (Option.some.inj h).symm
    subst this
    exact Inv_initial
  | succ n ih =>
    intro s h
    rw [show orbit (n + 1) = (orbit n).bind step from rfl] at h
    cases hO : orbit n with
    | none =>
      rw [hO] at h
      cases h
    | some t =>
      rw [hO] at h
      -- `(some t).bind step` is definitionally `step t`
      change step t = some s at h
      exact step_preserves_Inv (ih t hO) h

/-- **Headline theorem**: the v6 rule's orbit never halts. -/
theorem no_halt : ∀ n, orbit n ≠ none := by
  intro n
  induction n with
  | zero =>
    intro hne
    rw [show orbit 0 = some initial from rfl] at hne
    cases hne
  | succ n ih =>
    intro hne
    rw [show orbit (n + 1) = (orbit n).bind step from rfl] at hne
    cases hO : orbit n with
    | none => exact ih hO
    | some t =>
      rw [hO] at hne
      change step t = none at hne
      have hI : Inv t := orbit_Inv n t hO
      exact step_ne_none_of_Inv hI hne

end Collatz.Bigfoot.V6
