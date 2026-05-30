import Collatz.Bigfoot.V6Rule

/-!
# Bigfoot's V6 rule: strengthened invariant `InvB` and the open `k_pos` goal

`V6Rule.lean`'s `Inv` (four clauses on `(a, b, pat)`) was enough to prove
`no_halt`. It is NOT enough to prove `k_pos : 1 ≤ s.k`, which the rules
`B-coll` (`a = 9`) and `D-W` (`a = 3`) threaten by decrementing `s.k`.

We strengthen the invariant by adding five structural bounds on the `b`
counter (`InvB`). With these in hand, every clause-by-rule preservation
obligation for `k_pos` closes EXCEPT for two:

* `B-coll` preservation needs `2 ≤ s.k` at `(pat = P1, a = 9)`.
* `D-W`    preservation needs `2 ≤ s.k` at `(pat = P1, a = 3)`.

`k_pos_orbit_of` formalises this reduction: assuming those two cascade
obligations hold along the orbit, `k_pos` follows. The top-level
`k_pos_orbit` instantiates the reduction with two precisely-stated
`sorry`s, factoring the open math content of Bigfoot (the `(3,3)`-state
busy beaver holdout) sharply.

See `notes/18-v6-k-pos-attempt.md` for the by-hand cascade analysis and
why the two remaining obligations are mathematically equivalent to Shawn
Ligocki's `InvariantA` in `(a, b, c)` coordinates (via the bijection
`φ(a_s, b_s, c_s) = (a_s, 2·b_s − 1, 2·c_s + 1, P1)`).
-/

namespace Collatz.Bigfoot.V6

open Pat

/-! ## Strengthened invariant `InvB`

Nine clauses on `(a, b, pat)`. Four match `Inv`. Five are new structural
`b`-bounds. `k` is NOT mentioned: every new clause closes sorry-free under
preservation. The k-bound `k_pos` is handled separately via
`k_pos_orbit_of` below.
-/

/-- Strengthened structural invariant on `(a, b, pat)`. -/
structure InvB (s : State) : Prop where
  /-- (Inv) P1 states never reach `a = 0`. -/
  p1_a_pos      : s.pat = P1 → 1 ≤ s.a
  /-- (Inv) In P1 with `a = 1`, b ≥ 5. -/
  p1_a1_b5      : s.pat = P1 → s.a = 1 → 5 ≤ s.b
  /-- (Inv) In P2, a ≥ 5. -/
  p2_a_5        : s.pat = P2 → 5 ≤ s.a
  /-- (Inv) In P2 with `a = 5`, b = 3. -/
  p2_a5_b3      : s.pat = P2 → s.a = 5 → s.b = 3
  /-- (new) In P2, b ≥ 2. Both Q-same (→ b = 2) and Q-kpp (→ b = 3) output b ≥ 2. -/
  p2_b_ge_2     : s.pat = P2 → 2 ≤ s.b
  /-- (new) In P2, b ≤ 3. -/
  p2_b_le_3     : s.pat = P2 → s.b ≤ 3
  /-- (new) In P2 with `b = 2`, a ≥ 7. Q-same is the only source of `b = 2`;
  its output `a = b_in + 7 ≥ 7`. -/
  p2_b2_a_ge_7  : s.pat = P2 → s.b = 2 → 7 ≤ s.a
  /-- (new) In P1 with `a = 3`, b ≥ 7. Strengthened from `≥ 5` using
  parity (b odd) plus `p1_a6_b_ge_6` (rules out the S source from
  `(P1, 6, 0)`). Eliminates the smallest "dangerous mod 12 = 5" D-W
  input case `(P1, 3, 5)`. -/
  p1_a3_b_ge_7  : s.pat = P1 → s.a = 3 → 7 ≤ s.b
  /-- (new) In P1 with `a = 2`, b ≥ 7. Rules out W firing on small `b`. -/
  p1_a2_b_ge_7  : s.pat = P1 → s.a = 2 → 7 ≤ s.b
  /-- (new) Parity: `a + b` is always even. Each rule's `Δ(a + b)` is in
  `{0, 2, 4}`, so parity is structurally preserved. Initial state has
  `a + b = 1 + 5 = 6`. Verified empirically over 100M V6 cycles with
  zero violations. Consequences: at `(P1, 3)` and `(P1, 9)`, b is
  ALWAYS odd; at `(P1, 6)`, b is always even; at `(P2, 7)` and
  `(P2, 5)`, b is always odd, which rules out the `b = 2` Q-same branch
  there. -/
  parity_ab     : (s.a + s.b) % 2 = 0
  /-- (new) In P1 with `a = 6`, b ≥ 6. Provable from parity (b even at
  (P1, 6)) plus the existing source analysis: B-source gives b ≥ 12,
  W-source gives b ≥ 11, P2→P1 source gives b = 6 (the tight case,
  with b_p2 = 2 from parity + p2_b_le_3). S source vacuous (would
  need (P1, 9, b-5) but a=9 is odd, S needs even input). Used as a
  premise for `p1_a3_b_ge_7`. -/
  p1_a6_b_ge_6  : s.pat = P1 → s.a = 6 → 6 ≤ s.b

/-- Forget the strengthening: every `InvB` is an `Inv`. -/
theorem InvB.toInv {s : State} (h : InvB s) : Inv s :=
  ⟨h.p1_a_pos, h.p1_a1_b5, h.p2_a_5, h.p2_a5_b3⟩

/-! ## `InvB` holds at the initial state -/

/-- `InvB` holds at the starting state `⟨2, 1, 5, P1⟩`. -/
theorem InvB_initial : InvB initial := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; decide        -- p1_a_pos
  · intro _ _; decide      -- p1_a1_b5
  · intro h; cases h       -- p2_a_5
  · intro h _; cases h     -- p2_a5_b3
  · intro h; cases h       -- p2_b_ge_2
  · intro h; cases h       -- p2_b_le_3
  · intro h _; cases h     -- p2_b2_a_ge_7
  · intro _ h; exact absurd h (by decide)   -- p1_a3_b_ge_7: 1 = 3 is False
  · intro _ h; exact absurd h (by decide)   -- p1_a2_b_ge_7: 1 = 2 is False
  · decide                 -- parity_ab: (1 + 5) % 2 = 0
  · intro _ h; exact absurd h (by decide)   -- p1_a6_b_ge_6: 1 = 6 is False

/-! ## `step` preserves `InvB` (modulo the two cascade gaps)

The proof mirrors `step_preserves_Inv` from `V6Rule.lean`: case-split on
`s.pat`, then on `s.a`. Each branch invokes the matching unfolding lemma
and discharges all 10 clauses. The two `sorry`s sit at the `B-coll` and
`D-W` cases, on the `k_pos` clause only.
-/

/-- `step` preserves `InvB`. Sorry-free: all nine clauses close at every
rule via case analysis on `s.pat` and `s.a`. -/
theorem step_preserves_InvB {s s' : State} (hI : InvB s)
    (hstep : step s = some s') : InvB s' := by
  have hpar := hI.parity_ab
  cases hpat : s.pat with
  | P2 =>
    rw [step_P2 hpat] at hstep
    have hs := Option.some.inj hstep
    subst hs
    have ha5  := hI.p2_a_5 hpat
    have hbge := hI.p2_b_ge_2 hpat
    have hble := hI.p2_b_le_3 hpat
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- p1_a_pos
    · intro _; change 1 ≤ s.a - 4; omega
    -- p1_a1_b5: a-4 = 1 → a=5 → b=3 → b+4 = 7 ≥ 5
    · intro _ h1
      change s.a - 4 = 1 at h1
      have h5eq : s.a = 5 := by omega
      have hb3 := hI.p2_a5_b3 hpat h5eq
      change 5 ≤ s.b + 4; omega
    -- p2_a_5 (output is P1, vacuous)
    · intro h; cases h
    -- p2_a5_b3
    · intro h _; cases h
    -- p2_b_ge_2
    · intro h; cases h
    -- p2_b_le_3
    · intro h; cases h
    -- p2_b2_a_ge_7
    · intro h _; cases h
    -- p1_a3_b_ge_7: a-4 = 3 → a_p2 = 7. Need s.b ≥ 3 to get b+4 ≥ 7.
    -- With parity (s.a + s.b even, s.a = 7 → s.b odd) and p2_b_ge_2/le_3
    -- (s.b ∈ {2, 3}), omega forces s.b = 3.
    · intro _ h3
      change s.a - 4 = 3 at h3
      change 7 ≤ s.b + 4; omega
    -- p1_a2_b_ge_7: a-4 = 2 → a = 6; only Q-kpp can give a=6 in P2, so b = 3
    · intro _ h2
      change s.a - 4 = 2 at h2
      have ha6 : s.a = 6 := by omega
      -- rule out b = 2 via p2_b2_a_ge_7
      have hb_ne_2 : s.b ≠ 2 := by
        intro heq
        have := hI.p2_b2_a_ge_7 hpat heq
        omega
      -- b ∈ {2, 3}, b ≠ 2, so b = 3
      have hb3 : s.b = 3 := by omega
      change 7 ≤ s.b + 4; omega
    -- parity_ab: (s.a - 4) + (s.b + 4) ≡ s.a + s.b (mod 2)
    · change (s.a - 4 + (s.b + 4)) % 2 = 0; omega
    -- p1_a6_b_ge_6: a-4 = 6 → a_p2 = 10. With parity and p2_b_ge_2/le_3,
    -- s.b ∈ {2}. Output b = 6.
    · intro _ h6
      change s.a - 4 = 6 at h6
      change 6 ≤ s.b + 4; omega
  | P1 =>
    by_cases hae : s.a % 2 = 0
    · by_cases hg4 : 4 ≤ s.a
      ----- S: (k, a-3, b+5, P1)
      · rw [step_S hpat hae hg4] at hstep
        have hs := Option.some.inj hstep; subst hs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _; change 1 ≤ s.a - 3; omega
        · intro _ _; change 5 ≤ s.b + 5; omega
        · intro h; cases h
        · intro h _; cases h
        · intro h; cases h
        · intro h; cases h
        · intro h _; cases h
        -- p1_a3_b_ge_7: a-3 = 3 → input a = 6 → use p1_a6_b_ge_6 → output b ≥ 11
        · intro _ h3
          change s.a - 3 = 3 at h3
          have ha6 : s.a = 6 := by omega
          have hb6 := hI.p1_a6_b_ge_6 hpat ha6
          change 7 ≤ s.b + 5; omega
        -- p1_a2_b_ge_7: a-3 = 2 → a = 5 (odd, but s.a is even) → vacuous
        · intro _ h2
          change s.a - 3 = 2 at h2
          have ha5 : s.a = 5 := by omega
          exfalso; omega
        -- parity_ab: (a-3) + (b+5) = a + b + 2
        · change (s.a - 3 + (s.b + 5)) % 2 = 0; omega
        -- p1_a6_b_ge_6: a-3 = 6 → input a = 9 (odd, but S needs even) → vacuous
        · intro _ h6
          change s.a - 3 = 6 at h6
          have ha9 : s.a = 9 := by omega
          exfalso; omega
      · by_cases ha2 : s.a = 2
        ----- W: (k, b+4, 0, P1) at a=2
        · rw [step_W hpat ha2] at hstep
          have hs := Option.some.inj hstep; subst hs
          have hb7 := hI.p1_a2_b_ge_7 hpat ha2
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro _; change 1 ≤ s.b + 4; omega
          · intro _ h1; change s.b + 4 = 1 at h1; exfalso; omega
          · intro h; cases h
          · intro h _; cases h
          · intro h; cases h
          · intro h; cases h
          · intro h _; cases h
          -- p1_a3_b_ge_7: b+4 = 3 → b = -1 impossible
          · intro _ h3; change s.b + 4 = 3 at h3; exfalso; omega
          -- p1_a2_b_ge_7: b+4 = 2 → impossible
          · intro _ h2; change s.b + 4 = 2 at h2; exfalso; omega
          -- parity_ab: (b+4) + 0 even, using input parity (s.a=2 + s.b) even → s.b even
          · change (s.b + 4 + 0) % 2 = 0; omega
          -- p1_a6_b_ge_6: b+4 = 6 → b = 2. But p1_a2_b_ge_7 gives b ≥ 7. Contradiction.
          · intro _ h6; change s.b + 4 = 6 at h6; exfalso; omega
        ----- halt branch: a = 0, contradicts p1_a_pos
        · have ha0 : s.a = 0 := by omega
          rw [step_halt hpat ha0] at hstep
          cases hstep
    · have ho : s.a % 2 = 1 := by omega
      by_cases hg11 : 11 ≤ s.a
      ----- B: (k, a-9, b+11, P1)
      · rw [step_B hpat ho hg11] at hstep
        have hs := Option.some.inj hstep; subst hs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _; change 1 ≤ s.a - 9; omega
        -- p1_a1_b5: a-9 = 1 → a = 10 (even), but s.a is odd
        · intro _ h1
          change s.a - 9 = 1 at h1
          exfalso; omega
        · intro h; cases h
        · intro h _; cases h
        · intro h; cases h
        · intro h; cases h
        · intro h _; cases h
        -- p1_a3_b_ge_7: a-9 = 3 → a = 12 (even), s.a odd → vacuous
        · intro _ h3
          change s.a - 9 = 3 at h3
          exfalso; omega
        -- p1_a2_b_ge_7: a-9 = 2 → a = 11. Output b = b + 11 ≥ 11 ≥ 7
        · intro _ _; change 7 ≤ s.b + 11; omega
        -- parity_ab: (a-9) + (b+11) = a + b + 2
        · change (s.a - 9 + (s.b + 11)) % 2 = 0; omega
        -- p1_a6_b_ge_6: a-9 = 6 → a = 15 (odd ✓). Output b = b+11 ≥ 11 ≥ 6.
        · intro _ _; change 6 ≤ s.b + 11; omega
      · by_cases ha9 : s.a = 9
        ----- B-coll: (k-1, 1, b+12, P1)
        · rw [step_Bcoll hpat ha9] at hstep
          have hs := Option.some.inj hstep; subst hs
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro _; change 1 ≤ 1; omega
          · intro _ _; change 5 ≤ s.b + 12; omega
          · intro h; cases h
          · intro h _; cases h
          · intro h; cases h
          · intro h; cases h
          · intro h _; cases h
          -- p1_a3_b_ge_7: output a = 1 ≠ 3, vacuous
          · intro _ h3
            change (1 : ℕ) = 3 at h3
            exact absurd h3 (by decide)
          -- p1_a2_b_ge_7: output a = 1 ≠ 2, vacuous
          · intro _ h2
            change (1 : ℕ) = 2 at h2
            exact absurd h2 (by decide)
          -- parity_ab: 1 + (b+12) = b+13; input (9+b) even → b odd → b+13 even
          · change (1 + (s.b + 12)) % 2 = 0; omega
          -- p1_a6_b_ge_6: output a = 1 ≠ 6, vacuous
          · intro _ h6
            change (1 : ℕ) = 6 at h6
            exact absurd h6 (by decide)
        · by_cases ha7 : s.a = 7
          ----- Q-W: (k+1, b+7, 0, P1)
          · rw [step_QW hpat ha7] at hstep
            have hs := Option.some.inj hstep; subst hs
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro _; change 1 ≤ s.b + 7; omega
            · intro _ h1; change s.b + 7 = 1 at h1; exfalso; omega
            · intro h; cases h
            · intro h _; cases h
            · intro h; cases h
            · intro h; cases h
            · intro h _; cases h
            -- p1_a3_b_ge_7: b+7 = 3 → b = -4 impossible
            · intro _ h3; change s.b + 7 = 3 at h3; exfalso; omega
            -- p1_a2_b_ge_7: b+7 = 2 impossible
            · intro _ h2; change s.b + 7 = 2 at h2; exfalso; omega
            -- parity_ab: (b+7) + 0; input (7+b) even → b odd → b+7 even
            · change (s.b + 7 + 0) % 2 = 0; omega
            -- p1_a6_b_ge_6: b+7 = 6 → b = -1 impossible
            · intro _ h6; change s.b + 7 = 6 at h6; exfalso; omega
          · by_cases ha5 : s.a = 5
            ----- Q-same: (k, b+7, 2, P2)
            · rw [step_Qsame hpat ha5] at hstep
              have hs := Option.some.inj hstep; subst hs
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro h; cases h
              · intro h _; cases h
              · intro _; change 5 ≤ s.b + 7; omega
              · intro _ h; change s.b + 7 = 5 at h; exfalso; omega
              · intro _; change (2 : ℕ) ≤ 2; omega
              · intro _; change (2 : ℕ) ≤ 3; omega
              · intro _ _; change 7 ≤ s.b + 7; omega
              · intro h _; cases h
              · intro h _; cases h
              · change (s.b + 7 + 2) % 2 = 0; omega
              -- p1_a6_b_ge_6: output pat = P2, vacuous
              · intro h _; cases h
            · by_cases ha3 : s.a = 3
              ----- D-W: (k-1, b+7, 0, P1)
              · rw [step_DW hpat ha3] at hstep
                have hs := Option.some.inj hstep; subst hs
                have hb7 := hI.p1_a3_b_ge_7 hpat ha3
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro _; change 1 ≤ s.b + 7; omega
                · intro _ h1; change s.b + 7 = 1 at h1; exfalso; omega
                · intro h; cases h
                · intro h _; cases h
                · intro h; cases h
                · intro h; cases h
                · intro h _; cases h
                -- p1_a3_b_ge_7: b+7 = 3 → b = -4 impossible
                · intro _ h3; change s.b + 7 = 3 at h3; exfalso; omega
                -- p1_a2_b_ge_7: b+7 = 2 impossible
                · intro _ h2; change s.b + 7 = 2 at h2; exfalso; omega
                -- parity_ab: (b+7) + 0; input (3+b) even → b odd → b+7 even
                · change (s.b + 7 + 0) % 2 = 0; omega
                -- p1_a6_b_ge_6: b+7 = 6 → b = -1 impossible
                · intro _ h6; change s.b + 7 = 6 at h6; exfalso; omega
              ----- Q-kpp: (k+1, b, 3, P2)
              · have ha1 : s.a = 1 := by omega
                rw [step_Qkpp hpat ha1] at hstep
                have hs := Option.some.inj hstep; subst hs
                have hb5 := hI.p1_a1_b5 hpat ha1
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro h; cases h
                · intro h _; cases h
                · intro _; exact hb5
                · intro _ _; rfl
                · intro _; change (2 : ℕ) ≤ 3; omega
                · intro _; change (3 : ℕ) ≤ 3; omega
                · intro _ h
                  change (3 : ℕ) = 2 at h
                  exact absurd h (by decide)
                · intro h _; cases h
                · intro h _; cases h
                · change (s.b + 3) % 2 = 0; omega
                -- p1_a6_b_ge_6: output pat = P2, vacuous
                · intro h _; cases h

/-! ## Orbit-wide `InvB`

Modulo the two `sorry`s in `step_preserves_InvB`, every reachable state
satisfies `InvB`. -/

/-- `InvB` holds at every reachable state (conditional on the two
`sorry`s in `step_preserves_InvB`). -/
theorem orbit_InvB : ∀ n s, orbit n = some s → InvB s := by
  intro n
  induction n with
  | zero =>
    intro s h
    have : s = initial := (Option.some.inj h).symm
    subst this
    exact InvB_initial
  | succ n ih =>
    intro s h
    rw [show orbit (n + 1) = (orbit n).bind step from rfl] at h
    cases hO : orbit n with
    | none => rw [hO] at h; cases h
    | some t =>
      rw [hO] at h
      change step t = some s at h
      exact step_preserves_InvB (ih t hO) h

/-! ## Factoring `k_pos_orbit` cleanly

`k_pos_orbit_of` reduces `1 ≤ s.k` along the orbit to two precise
obligations: `k ≥ 2` at every reachable `(P1, a = 9)` and `(P1, a = 3)`.
This factoring is sorry-free; the cascade obligations themselves are the
genuinely open content (Bigfoot's `(3,3)` BB holdout, equivalent to
Ligocki's `InvariantA` in `(a, b, c)` coords).
-/

/-- The two cascade obligations needed for `k_pos`. -/
abbrev KPosCascade : Prop :=
  (∀ n s, orbit n = some s → s.pat = P1 → s.a = 9 → 2 ≤ s.k) ∧
  (∀ n s, orbit n = some s → s.pat = P1 → s.a = 3 → 2 ≤ s.k)

/-- `k_pos` along the orbit follows from the two cascade obligations.

This is a sorry-free reduction: assuming `k ≥ 2` at every reachable
`(P1, a = 9)` (B-coll input) and `(P1, a = 3)` (D-W input), we get
`k ≥ 1` at every reachable state. The two cascade obligations together
are Bigfoot's `InvariantA` in V6 coordinates. -/
theorem k_pos_orbit_of (cascade : KPosCascade) :
    ∀ n s, orbit n = some s → 1 ≤ s.k := by
  obtain ⟨h9, h3⟩ := cascade
  intro n
  induction n with
  | zero =>
    intro s hs
    have : s = initial := (Option.some.inj hs).symm
    subst this
    decide
  | succ n ih =>
    intro s hs
    rw [show orbit (n + 1) = (orbit n).bind step from rfl] at hs
    cases hO : orbit n with
    | none => rw [hO] at hs; cases hs
    | some t =>
      rw [hO] at hs
      change step t = some s at hs
      have hkp_t : 1 ≤ t.k := ih t hO
      -- Case-split on which rule fired from t to s.
      cases hpat : t.pat with
      | P2 =>
        rw [step_P2 hpat] at hs
        have hs' := Option.some.inj hs
        subst hs'
        change 1 ≤ t.k
        exact hkp_t
      | P1 =>
        by_cases hae : t.a % 2 = 0
        · by_cases hg4 : 4 ≤ t.a
          -- S
          · rw [step_S hpat hae hg4] at hs
            have hs' := Option.some.inj hs; subst hs'
            change 1 ≤ t.k; exact hkp_t
          · by_cases ha2 : t.a = 2
            -- W
            · rw [step_W hpat ha2] at hs
              have hs' := Option.some.inj hs; subst hs'
              change 1 ≤ t.k; exact hkp_t
            -- halt branch unreachable from `Inv t`; but we don't have `Inv t`
            -- here. Argue via `step_halt` returning `none`.
            · have ha0 : t.a = 0 := by omega
              rw [step_halt hpat ha0] at hs
              cases hs
        · have ho : t.a % 2 = 1 := by omega
          by_cases hg11 : 11 ≤ t.a
          -- B
          · rw [step_B hpat ho hg11] at hs
            have hs' := Option.some.inj hs; subst hs'
            change 1 ≤ t.k; exact hkp_t
          · by_cases ha9 : t.a = 9
            -- B-coll: needs t.k ≥ 2 via h9
            · rw [step_Bcoll hpat ha9] at hs
              have hs' := Option.some.inj hs; subst hs'
              have htk2 := h9 n t hO hpat ha9
              change 1 ≤ t.k - 1; omega
            · by_cases ha7 : t.a = 7
              -- Q-W
              · rw [step_QW hpat ha7] at hs
                have hs' := Option.some.inj hs; subst hs'
                change 1 ≤ t.k + 1; omega
              · by_cases ha5 : t.a = 5
                -- Q-same
                · rw [step_Qsame hpat ha5] at hs
                  have hs' := Option.some.inj hs; subst hs'
                  change 1 ≤ t.k; exact hkp_t
                · by_cases ha3 : t.a = 3
                  -- D-W: needs t.k ≥ 2 via h3
                  · rw [step_DW hpat ha3] at hs
                    have hs' := Option.some.inj hs; subst hs'
                    have htk2 := h3 n t hO hpat ha3
                    change 1 ≤ t.k - 1; omega
                  -- Q-kpp
                  · have ha1 : t.a = 1 := by omega
                    rw [step_Qkpp hpat ha1] at hs
                    have hs' := Option.some.inj hs; subst hs'
                    change 1 ≤ t.k + 1; omega

/-! ## `k_pos_orbit`: the open theorem

We state the headline `k_pos_orbit` as the application of the (sorry-free)
reduction to two precisely-stated `sorry`s. Each `sorry` is one of the
cascade obligations from `notes/18-v6-k-pos-attempt.md`. Together they
are equivalent to Shawn Ligocki's `InvariantA` and the `(3,3)`-BB holdout
remaining open.
-/

/-- **Open cascade obligation #1**: at every reachable `(P1, a = 9)` state
(the B-coll firing point), `k ≥ 2`. Equivalent through the bijection
`φ : Shawn → V6` to the part of Ligocki's `InvariantA` that prevents
`a_s` from reaching the halting band at a B-coll-aligned super-cycle.
Empirically verified to 1B V6 cycles (`bigfoot_v6_pure_rule.py`,
`k ∈ [2, 14]`). -/
theorem k_at_9_ge_2_orbit :
    ∀ n s, orbit n = some s → s.pat = P1 → s.a = 9 → 2 ≤ s.k := by
  sorry

/-- **Open cascade obligation #2**: at every reachable `(P1, a = 3)` state
(the D-W firing point), `k ≥ 2`. The structurally harder of the two
gaps: D-W's k-decrement is not immediately recovered (unlike B-coll's
which pairs with Q-kpp). See `notes/18-v6-k-pos-attempt.md` for the
D-W input-`b` sparseness analysis. -/
theorem k_at_3_ge_2_orbit :
    ∀ n s, orbit n = some s → s.pat = P1 → s.a = 3 → 2 ≤ s.k := by
  sorry

/-! ## Structural fact: no two consecutive decrement firings

`B-coll` (at `(P1, a = 9)`) and `D-W` (at `(P1, a = 3)`) are the only
two rules that decrement `k`. Empirically (100M cycles) the maximum
number of consecutive decrement firings is 2 — and even stronger, no
two are *immediately* consecutive.

This is a finite, mechanically-verifiable fact (no cascade): given
`InvB`, the immediate successor of any decrement-firing state is never
itself decrement-firing. The proof case-splits on `B-coll` vs `D-W`:

* After `B-coll`, the next state has `a = 1` (the `Q-kpp` firing point),
  which is *not* in `{3, 9}`. Doesn't need `InvB`.
* After `D-W`, the next state has `a = b_in + 7`. Under `InvB`,
  `p1_a3_b_ge_7` gives `b_in ≥ 7`, so `a_out ≥ 14`. Not in `{3, 9}`.

This rules out `D D` patterns in the firing sequence, leaving only the
`D ... D` patterns separated by `≥ 1` non-decrement rule. The empirical
"max 2 consecutive decrements" observation is the next strengthening:
no `D ... D ... D` separated only by non-increment intervening rules.
That requires the `b mod 12` → terminus structure documented in
`BIGFOOT-HANDOFF.md` §8, and is left open.
-/

/-- A state is decrement-firing iff its `step` decrements `k`: namely,
the `B-coll` firing point `(P1, a = 9)` and the `D-W` firing point
`(P1, a = 3)`. -/
def IsDecrementFiring (s : State) : Prop :=
  s.pat = P1 ∧ (s.a = 9 ∨ s.a = 3)

/-- **No two immediately consecutive decrement firings.** Under `InvB`,
if `s` is decrement-firing and `step s = some s'`, then `s'` is not
decrement-firing. -/
theorem no_consecutive_decrements {s s' : State} (hI : InvB s)
    (hdec : IsDecrementFiring s) (hstep : V6.step s = some s') :
    ¬ IsDecrementFiring s' := by
  obtain ⟨hpat, hor⟩ := hdec
  rcases hor with ha9 | ha3
  · -- B-coll: step s = some ⟨k-1, 1, b+12, P1⟩. Successor has a = 1.
    have hs' : s' = ⟨s.k - 1, 1, s.b + 12, P1⟩ := by
      have hbc := step_Bcoll hpat ha9
      rw [hbc] at hstep
      exact (Option.some.inj hstep).symm
    rintro ⟨_, h⟩
    rw [hs'] at h
    rcases h with h | h <;> simp at h
  · -- D-W: step s = some ⟨k-1, b+7, 0, P1⟩. Under InvB, b ≥ 7 so a_out ≥ 14.
    have hb7 : 7 ≤ s.b := hI.p1_a3_b_ge_7 hpat ha3
    have hs' : s' = ⟨s.k - 1, s.b + 7, 0, P1⟩ := by
      have hdw := step_DW hpat ha3
      rw [hdw] at hstep
      exact (Option.some.inj hstep).symm
    rintro ⟨_, h⟩
    rw [hs'] at h
    rcases h with h | h
    · -- s.b + 7 = 9 means s.b = 2, contradicting b ≥ 7.
      simp only at h; omega
    · -- s.b + 7 = 3 is impossible in ℕ.
      simp only at h
      omega

/-- **Orbit-wide corollary.** No two orbit-consecutive positions both
fire decrement rules. Combines `no_consecutive_decrements` with
`orbit_InvB`. -/
theorem no_consecutive_decrements_orbit (n : ℕ) (s s' : State)
    (hn : orbit n = some s) (hsucc : orbit (n + 1) = some s')
    (hdec : IsDecrementFiring s) :
    ¬ IsDecrementFiring s' := by
  -- orbit (n+1) = (orbit n).bind step = step s.
  have h_succ : orbit (n + 1) = (orbit n).bind step := rfl
  rw [hn] at h_succ
  simp only [Option.bind_some] at h_succ
  rw [hsucc] at h_succ
  exact no_consecutive_decrements (orbit_InvB n s hn) hdec h_succ.symm

/-- **Open**: V6's k-counter never drops below 1 along the orbit.

This is the `(k, a, b)`-coordinate form of Bigfoot's `InvariantA`. The
`(3,3)`-state busy beaver holdout #1 (Bigfoot) is closed precisely when
this theorem is proved (modulo the V6 ↔ TM correspondence, also pending).

The proof here factors the obligation cleanly via `k_pos_orbit_of`:
given the two `(P1, a ∈ {3, 9}) → k ≥ 2` cascade conditions, `k_pos` at
every orbit step follows mechanically. The `sorry`s for the cascade
conditions are the genuinely open math content. -/
theorem k_pos_orbit : ∀ n s, orbit n = some s → 1 ≤ s.k :=
  k_pos_orbit_of ⟨k_at_9_ge_2_orbit, k_at_3_ge_2_orbit⟩

end Collatz.Bigfoot.V6
