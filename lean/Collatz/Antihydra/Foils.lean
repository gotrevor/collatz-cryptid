/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Rounding-choice foils for Antihydra

Antihydra (BB(6) cryptid `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) is the orbit of `8` under
`H x = x + ⌊x/2⌋ = ⌊3x/2⌋` with a counter that gains `2` on even values and loses `1` on odd
values; it halts when an odd value is met with counter `0` (sligocki's rules
`A(2a,b) → A(3a,b+2)`, `A(2a+1,b+1) → A(3a+1,b)`, `A(2a+1,0) → halt`, start `A(8,0)`; the same
convention as `Antihydra.AntihydraHalts` in mfornet/antihydra-autoresearch, see
`halts_floor_iff` below).

**The foil family.**  Keep the even branch `x ↦ 3x/2` exact, and at each odd `x` allow either
rounding `⌊3x/2⌋` or `⌈3x/2⌉` (defect `≤ 1`).  A choice function `τ : ℕ → Bool` (`true` =
ceiling) gives one member.  `F_L` (`member L σ`) asks the choice to be constant on blocks of `L`
consecutive odd values: odd `x = 2j+1` lies in block `j / L = x / (2L)`.  Antihydra is the
all-floor member of every `F_L`.

**Results.**
* `exists_halting_member`: for every `L ≥ 1`, some member of `F_L` halts from `(8,0)`.  More:
  `halting_dense`: every member of `F_L` agrees, on any prescribed finite set of blocks, with a
  halting member; so halting members accumulate at Antihydra.
* `exists_eventually_odd_member`: the same members have an odd tail: from some step on every
  value is odd, so the even count `E_k` is bounded (`evenCount_bounded`) and odd runs are
  unbounded.  Any argument whose inputs are shared by all of `F_L` therefore proves neither
  non-halting, nor `E_k → ∞`, nor an odd-run cap.
* `even_run_dvd` (rounding-blind, holds for every member): an even run of length `e` from `x`
  forces `2^e ∣ x`.  This is the only run cap the family cannot see past.
* `nonhalting_member_of_survives`: if a member survives until its orbit first reaches height
  `2LK`, it agrees below block `K` with a member that never halts (choose the even image at each
  odd value from then on).  `exists_nonhalting_member_one` is the unconditional case `L = 1`.
* `rounding_blind_cannot_decide`: no property shared by all members agreeing with Antihydra
  below block `K` implies non-halting.
* **The ceiling** (`evenCount_ceiling_lower`, `evenCount_ceiling_sharp`): over the members
  agreeing with Antihydra below block `K`, the best lower bound on the even count `E_k` is
  exactly Antihydra's own even count up to `horizon L K`, the first odd value of height
  `≥ 2LK`.  A rounding-blind argument proves nothing about `E_k` past a finite computation.
  On the odd side the blind facts are lower bounds (`odd_infinitely_often`, `even_run_dvd`),
  which point towards halting, not away from it.
* `halts_floor_iff`: the all-floor member halts iff mfornet's `AntihydraHalts`.
-/

namespace Collatz.Antihydra.Foils

/-! ## The family -/

/-- One step of the rounding-choice dynamics on states `(x, c)` (value, counter).  At odd `x`,
`τ x = true` picks `⌈3x/2⌉ = (3x+1)/2` and `false` picks `⌊3x/2⌋`; at even `x` both give
`3x/2`.  The counter gains `2` on an even value and loses `1` (truncated) on an odd one. -/
def step (τ : ℕ → Bool) (s : ℕ × ℕ) : ℕ × ℕ :=
  ((3 * s.1 + if τ s.1 then 1 else 0) / 2, if s.1 % 2 = 0 then s.2 + 2 else s.2 - 1)

/-- The orbit of `s` under the member with choice function `τ`. -/
def orbit (τ : ℕ → Bool) (s : ℕ × ℕ) (n : ℕ) : ℕ × ℕ := (step τ)^[n] s

/-- The machine halts at step `n`: an odd value is met with counter `0`.  Before the first such
step the truncated subtraction in `step` never truncates. -/
def HaltsAt (τ : ℕ → Bool) (s : ℕ × ℕ) (n : ℕ) : Prop :=
  (orbit τ s n).1 % 2 = 1 ∧ (orbit τ s n).2 = 0

/-- The member with choice `τ` halts from `s`. -/
def Halts (τ : ℕ → Bool) (s : ℕ × ℕ) : Prop := ∃ n, HaltsAt τ s n

/-- Block index of a value: odd `x = 2j+1` lies in block `j / L = x / (2L)`. -/
def blk (L x : ℕ) : ℕ := x / (2 * L)

/-- The member of `F_L` with block choices `σ : ℕ → Bool` (`true` = ceiling). -/
def member (L : ℕ) (σ : ℕ → Bool) : ℕ → Bool := fun x => σ (blk L x)

/-- Antihydra's choice: always the floor. -/
def floorChoice : ℕ → Bool := fun _ => false

theorem member_floor (L : ℕ) : member L (fun _ => false) = floorChoice := rfl

/-- Number of even values among the first `k` states. -/
def evenCount (τ : ℕ → Bool) (s : ℕ × ℕ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun m => (orbit τ s m).1 % 2 = 0).card

/-! ## Basic step facts -/

@[simp] theorem orbit_zero (τ : ℕ → Bool) (s : ℕ × ℕ) : orbit τ s 0 = s := rfl

theorem orbit_succ (τ : ℕ → Bool) (s : ℕ × ℕ) (n : ℕ) :
    orbit τ s (n + 1) = step τ (orbit τ s n) :=
  Function.iterate_succ_apply' _ _ _

theorem orbit_succ' (τ : ℕ → Bool) (s : ℕ × ℕ) (n : ℕ) :
    orbit τ s (n + 1) = orbit τ (step τ s) n :=
  Function.iterate_succ_apply _ _ _

theorem orbit_add (τ : ℕ → Bool) (s : ℕ × ℕ) (m n : ℕ) :
    orbit τ s (m + n) = orbit τ (orbit τ s m) n := by
  simp only [orbit, add_comm m n, Function.iterate_add_apply]

theorem step_fst_ge (τ : ℕ → Bool) (s : ℕ × ℕ) : s.1 + s.1 / 2 ≤ (step τ s).1 := by
  unfold step; split <;> omega

theorem step_fst_even (τ : ℕ → Bool) (s : ℕ × ℕ) (h : s.1 % 2 = 0) :
    (step τ s).1 = 3 * s.1 / 2 := by
  unfold step; split <;> omega

theorem step_snd_even (τ : ℕ → Bool) (s : ℕ × ℕ) (h : s.1 % 2 = 0) :
    (step τ s).2 = s.2 + 2 := by
  simp [step, h]

theorem step_snd_odd (τ : ℕ → Bool) (s : ℕ × ℕ) (h : s.1 % 2 = 1) :
    (step τ s).2 = s.2 - 1 := by
  simp [step, h]

theorem step_congr {τ₁ τ₂ : ℕ → Bool} {s : ℕ × ℕ} (h : τ₁ s.1 = τ₂ s.1) :
    step τ₁ s = step τ₂ s := by
  simp [step, h]

theorem step_congr_even {τ₁ τ₂ : ℕ → Bool} {s : ℕ × ℕ} (h : s.1 % 2 = 0) :
    step τ₁ s = step τ₂ s :=
  Prod.ext (by rw [step_fst_even _ _ h, step_fst_even _ _ h]) (by simp [step, h])

/-- Two members whose choices agree at the odd values among the first `n` states of the first
one's orbit have the same orbit up to step `n`. -/
theorem orbit_congr_prefix {τ₁ τ₂ : ℕ → Bool} {s : ℕ × ℕ} {n : ℕ}
    (h : ∀ m < n, (orbit τ₁ s m).1 % 2 = 1 → τ₁ (orbit τ₁ s m).1 = τ₂ (orbit τ₁ s m).1) :
    ∀ m ≤ n, orbit τ₁ s m = orbit τ₂ s m := by
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [orbit_succ, orbit_succ, ← ih (by omega)]
    rcases Nat.mod_two_eq_zero_or_one (orbit τ₁ s m).1 with he | ho
    · exact step_congr_even he
    · exact step_congr (h m (by omega) ho)

theorem orbit_congr {τ₁ τ₂ : ℕ → Bool} {s : ℕ × ℕ}
    (h : ∀ m, τ₁ (orbit τ₁ s m).1 = τ₂ (orbit τ₁ s m).1) (n : ℕ) :
    orbit τ₁ s n = orbit τ₂ s n :=
  orbit_congr_prefix (n := n) (fun m _ _ => h m) n le_rfl

/-- Values never decrease. -/
theorem orbit_fst_mono (τ : ℕ → Bool) (s : ℕ × ℕ) {m n : ℕ} (h : m ≤ n) :
    (orbit τ s m).1 ≤ (orbit τ s n).1 := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · have := step_fst_ge τ (orbit τ s n)
      rw [orbit_succ]; have := ih (by omega); omega
    · rw [show m = n + 1 by omega]

/-- From a value `≥ 2` the orbit climbs by at least one per step. -/
theorem orbit_fst_ge_add (τ : ℕ → Bool) (s : ℕ × ℕ) (hs : 2 ≤ s.1) (n : ℕ) :
    s.1 + n ≤ (orbit τ s n).1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := step_fst_ge τ (orbit τ s n)
    rw [orbit_succ]; omega

/-! ## Rounding-blind facts: the exact even branch -/

/-- From value `2^a * y`, the next `a` steps are even and land on `3^a * y`, whatever the
choices. -/
theorem orbit_two_pow (τ : ℕ → Bool) (a : ℕ) :
    ∀ y c, (orbit τ (2 ^ a * y, c) a).1 = 3 ^ a * y := by
  induction a with
  | zero => intro y c; simp
  | succ a ih =>
    intro y c
    rw [orbit_succ']
    have h1 : (step τ (2 ^ (a + 1) * y, c)).1 = 2 ^ a * (3 * y) := by
      rw [step_fst_even _ _
        (Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) y))]
      simp only [pow_succ]
      rw [show 3 * (2 ^ a * 2 * y) = 2 * (2 ^ a * (3 * y)) by ring]
      omega
    have : step τ (2 ^ (a + 1) * y, c) = (2 ^ a * (3 * y), (step τ (2 ^ (a + 1) * y, c)).2) :=
      Prod.ext h1 rfl
    rw [this, ih]; ring

/-- Every orbit from a positive value reaches an odd value. -/
theorem exists_odd (τ : ℕ → Bool) (s : ℕ × ℕ) (hs : 0 < s.1) :
    ∃ j, (orbit τ s j).1 % 2 = 1 := by
  obtain ⟨a, y, hy, hxy⟩ := Nat.exists_eq_two_pow_mul_odd (n := s.1) (by omega)
  refine ⟨a, ?_⟩
  have : s = (2 ^ a * y, s.2) := Prod.ext hxy rfl
  rw [this, orbit_two_pow]
  exact Nat.odd_iff.mp ((Odd.pow (by decide : Odd 3)).mul hy)

/-- **Even-run cap (rounding-blind).**  If the `e` values from step `n` on are all even, then
`2^e` divides the value at step `n`.  Uses only the exact even branch, so it holds for every
member. -/
theorem even_run_dvd (τ : ℕ → Bool) (e : ℕ) :
    ∀ s : ℕ × ℕ, (∀ i < e, (orbit τ s i).1 % 2 = 0) → 2 ^ e ∣ s.1 := by
  induction e with
  | zero => intro s _; simp
  | succ e ih =>
    intro s h
    have h0 : s.1 % 2 = 0 := h 0 (by omega)
    have h1 : 2 ^ e ∣ (step τ s).1 :=
      ih (step τ s) fun i hi => by rw [← orbit_succ']; exact h (i + 1) (by omega)
    rw [step_fst_even _ _ h0] at h1
    obtain ⟨y, hy⟩ := Nat.dvd_of_mod_eq_zero h0
    rw [hy, show 3 * (2 * y) / 2 = 3 * y by omega] at h1
    have : 2 ^ e ∣ y :=
      (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left _ (by decide)) h1)
    rw [hy, pow_succ, mul_comm (2 ^ e)]
    exact Nat.mul_dvd_mul_left 2 this

/-- Rounding-blind: every member meets odd values infinitely often (`O_k → ∞`). -/
theorem odd_infinitely_often (τ : ℕ → Bool) (s : ℕ × ℕ) (hs : 2 ≤ s.1) (N : ℕ) :
    ∃ n, N ≤ n ∧ (orbit τ s n).1 % 2 = 1 := by
  obtain ⟨j, hj⟩ := exists_odd τ (orbit τ s N) (by have := orbit_fst_ge_add τ s hs N; omega)
  exact ⟨N + j, by omega, by rw [orbit_add]; exact hj⟩

/-! ## Blocks -/

theorem blk_lt_iff {L K x : ℕ} (hL : 0 < L) : blk L x < K ↔ x < 2 * L * K := by
  unfold blk
  rw [Nat.div_lt_iff_lt_mul (by omega), mul_comm K]

theorem blk_lt_blk {L x y : ℕ} (hL : 0 < L) (h : x + 2 * L ≤ y) : blk L x < blk L y := by
  unfold blk
  have h2 : 0 < 2 * L := by omega
  have : (x + 2 * L) / (2 * L) = x / (2 * L) + 1 := Nat.add_div_right x h2
  have := Nat.div_le_div_right (c := 2 * L) h
  omega

/-- **Realization.**  Above height `2LK` (with `K ≥ 2`) the orbit visits each block at most
once, so any value-wise choice `τ` that is block-wise below `2LK` is, along its own orbit, the
choice of a genuine member of `F_L` that agrees with `σ₀` on the blocks `< K`. -/
theorem realize {L K : ℕ} (hL : 1 ≤ L) (hK : 2 ≤ K) (σ₀ τ : ℕ → Bool)
    (hτ : ∀ x < 2 * L * K, τ x = σ₀ (blk L x)) (s : ℕ × ℕ) :
    ∃ σ : ℕ → Bool, (∀ b < K, σ b = σ₀ b) ∧ ∀ n, orbit (member L σ) s n = orbit τ s n := by
  classical
  set x : ℕ → ℕ := fun n => (orbit τ s n).1 with hx
  let σ : ℕ → Bool := fun b =>
    if b < K then σ₀ b else if h : ∃ n, blk L (x n) = b then τ (x (Nat.find h)) else false
  refine ⟨σ, fun b hb => by simp [σ, hb], ?_⟩
  have key : ∀ n, τ (x n) = member L σ (x n) := by
    intro n
    show τ (x n) = σ (blk L (x n))
    by_cases hlt : x n < 2 * L * K
    · have hb : blk L (x n) < K := (blk_lt_iff (by omega)).mpr hlt
      simp only [σ, hb, if_true, hτ _ hlt]
    · have hb : ¬ blk L (x n) < K := fun h => hlt ((blk_lt_iff (by omega)).mp h)
      have h : ∃ m, blk L (x m) = blk L (x n) := ⟨n, rfl⟩
      simp only [σ, hb, if_false, dif_pos h]
      have hspec : blk L (x (Nat.find h)) = blk L (x n) := Nat.find_spec h
      have hle : Nat.find h ≤ n := Nat.find_min' h rfl
      rcases Nat.lt_or_ge (Nat.find h) n with hlt' | hge
      · exfalso
        set m := Nat.find h
        have hm : 2 * L * K ≤ x m := by
          by_contra hc
          exact hb (hspec ▸ (blk_lt_iff (by omega)).mpr (by omega))
        have h4 : 4 * L ≤ 2 * L * K := by nlinarith
        have hstep : x m + x m / 2 ≤ x (m + 1) := by
          simp only [hx, orbit_succ]; exact step_fst_ge _ _
        have hmono : x (m + 1) ≤ x n := orbit_fst_mono τ s (by omega)
        have := blk_lt_blk (L := L) (x := x m) (y := x n) (by omega) (by omega)
        omega
      · rw [show Nat.find h = n by omega]
  intro n
  exact (orbit_congr (τ₁ := τ) (τ₂ := member L σ) (fun m => key m) n).symm

/-! ## Odd tails and halting members -/

/-- Choose the odd image: at odd `x ≡ 1 (mod 4)` the floor `(3x-1)/2` is odd, at `x ≡ 3` the
ceiling `(3x+1)/2` is. -/
theorem step_odd_image (τ : ℕ → Bool) (s : ℕ × ℕ) (h : s.1 % 2 = 1)
    (hτ : τ s.1 = decide (s.1 % 4 = 3)) : (step τ s).1 % 2 = 1 := by
  unfold step; rw [hτ]
  by_cases h3 : s.1 % 4 = 3 <;> simp [h3] <;> omega

/-- Choose the even image: at odd `x ≡ 1 (mod 4)` the ceiling is even, at `x ≡ 3` the floor. -/
theorem step_even_image (τ : ℕ → Bool) (s : ℕ × ℕ) (h : s.1 % 2 = 1)
    (hτ : τ s.1 = decide (s.1 % 4 = 1)) : (step τ s).1 % 2 = 0 := by
  unfold step; rw [hτ]
  by_cases h3 : s.1 % 4 = 1 <;> simp [h3] <;> omega

/-- **Odd tail.**  For every `L ≥ 1`, every member `σ₀` of `F_L`, every `K` and every start of
height `≥ 2`, some member agreeing with `σ₀` on the blocks `< K` has, from some step `n₁` on,
only odd values, its counter falling by one per step. -/
theorem exists_eventually_odd_member {L : ℕ} (hL : 1 ≤ L) (σ₀ : ℕ → Bool) (K : ℕ)
    (s : ℕ × ℕ) (hs : 2 ≤ s.1) :
    ∃ σ : ℕ → Bool, (∀ b < K, σ b = σ₀ b) ∧ ∃ n₁, ∀ i,
      (orbit (member L σ) s (n₁ + i)).1 % 2 = 1 ∧
      (orbit (member L σ) s (n₁ + i)).2 = (orbit (member L σ) s n₁).2 - i := by
  classical
  set K' := max K 2
  set M := 2 * L * K'
  let τ : ℕ → Bool := fun x => if x < M then σ₀ (blk L x) else decide (x % 4 = 3)
  obtain ⟨σ, hσ, horb⟩ := realize (K := K') hL (le_max_right _ _) σ₀ τ
    (fun x hx => by simp [τ, M, hx]) s
  refine ⟨fun b => σ b, fun b hb => hσ b (lt_of_lt_of_le hb (le_max_left _ _)), ?_⟩
  simp only [horb]
  -- reach height `M`, then an odd value
  have hM : M ≤ (orbit τ s M).1 := (Nat.le_add_left M s.1).trans (orbit_fst_ge_add τ s hs M)
  obtain ⟨j, hj⟩ := exists_odd τ (orbit τ s M) (by have := orbit_fst_ge_add τ s hs M; omega)
  refine ⟨M + j, ?_⟩
  have hM' : M ≤ (orbit τ s (M + j)).1 := le_trans hM (orbit_fst_mono τ s (by omega))
  have hodd : (orbit τ s (M + j)).1 % 2 = 1 := by rw [orbit_add]; exact hj
  intro i
  induction i with
  | zero => exact ⟨hodd, by simp⟩
  | succ i ih =>
    have hge : M ≤ (orbit τ s (M + j + i)).1 := le_trans hM' (orbit_fst_mono τ s (by omega))
    have hn : ¬ (orbit τ s (M + j + i)).1 < M := by omega
    rw [← add_assoc, orbit_succ]
    refine ⟨step_odd_image τ _ ih.1 (by simp only [τ]; rw [if_neg hn]), ?_⟩
    rw [step_snd_odd _ _ ih.1, ih.2]; omega

/-- **Halting members are dense** in `F_L` (product topology on block choices): every member
agrees, on any finite set of blocks `< K`, with a member that halts from `s`. -/
theorem halting_dense {L : ℕ} (hL : 1 ≤ L) (σ₀ : ℕ → Bool) (K : ℕ) (s : ℕ × ℕ)
    (hs : 2 ≤ s.1) : ∃ σ : ℕ → Bool, (∀ b < K, σ b = σ₀ b) ∧ Halts (member L σ) s := by
  obtain ⟨σ, hσ, n₁, h⟩ := exists_eventually_odd_member hL σ₀ K s hs
  refine ⟨σ, hσ, n₁ + (orbit (member L σ) s n₁).2, ?_⟩
  have := h (orbit (member L σ) s n₁).2
  exact ⟨this.1, by rw [this.2]; simp⟩

/-- **T2, target 2.**  For every `L ≥ 1`, some member of `F_L` halts from Antihydra's start
`(8, 0)`; it may be taken to agree with Antihydra on any prescribed finite set of blocks. -/
theorem exists_halting_member {L : ℕ} (hL : 1 ≤ L) (K : ℕ) :
    ∃ σ : ℕ → Bool, (∀ b < K, σ b = false) ∧ Halts (member L σ) (8, 0) :=
  halting_dense hL (fun _ => false) K (8, 0) (by norm_num)

/-- The odd-tail members have bounded even count: `E_k` does not tend to infinity. -/
theorem evenCount_le_of_odd_tail (τ : ℕ → Bool) (s : ℕ × ℕ) (n₁ : ℕ)
    (h : ∀ i, (orbit τ s (n₁ + i)).1 % 2 = 1) (k : ℕ) : evenCount τ s k ≤ n₁ := by
  unfold evenCount
  calc _ ≤ (Finset.range n₁).card := by
        apply Finset.card_le_card
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
        by_contra hc
        have := h (m - n₁)
        rw [show n₁ + (m - n₁) = m by omega] at this
        omega
    _ = n₁ := Finset.card_range _

/-- For every `L ≥ 1` and `K`, some member agreeing with Antihydra below block `K` has bounded
even count along its (unhalted, truncated-counter) orbit from `(8, 0)`.  So `E_k / log k → ∞`
(mfornet ES3, for Antihydra itself) is not a property of the family: its proof must use the
exact floor law. -/
theorem evenCount_bounded {L : ℕ} (hL : 1 ≤ L) (K : ℕ) :
    ∃ σ : ℕ → Bool, (∀ b < K, σ b = false) ∧
      ∃ B, ∀ k, evenCount (member L σ) (8, 0) k ≤ B := by
  obtain ⟨σ, hσ, n₁, h⟩ := exists_eventually_odd_member hL (fun _ => false) K (8, 0)
    (by norm_num)
  exact ⟨σ, hσ, n₁, evenCount_le_of_odd_tail _ _ n₁ (fun i => (h i).1)⟩

/-! ## Non-halting members -/

/-- No halt at this state: an odd value carries a positive counter. -/
def Alive (p : ℕ × ℕ) : Prop := p.1 % 2 = 1 → 1 ≤ p.2

/-- Taking the even image at an odd value keeps the machine alive at the next step, whatever
the counter. -/
theorem alive_step_even_image (τ : ℕ → Bool) (p : ℕ × ℕ)
    (hτ : τ p.1 = decide (p.1 % 4 = 1)) : Alive (step τ p) := by
  intro hodd
  rcases Nat.mod_two_eq_zero_or_one p.1 with h | h
  · rw [step_snd_even _ _ h]; omega
  · have := step_even_image τ p h hτ; omega

/-- **Conditional non-halting member.**  If the member `σ₀` of `F_L` survives up to and
including the first step at which its orbit from `s` reaches height `2LK` (`K ≥ 2`), then
some member agreeing with `σ₀` below block `K` never halts from `s`: from that height on, take
the even image at each odd value. -/
theorem nonhalting_member_of_survives {L K : ℕ} (hL : 1 ≤ L) (hK : 2 ≤ K) (σ₀ : ℕ → Bool)
    (s : ℕ × ℕ)
    (hsurv : ∀ n, (∀ m < n, (orbit (member L σ₀) s m).1 < 2 * L * K) →
      Alive (orbit (member L σ₀) s n)) :
    ∃ σ : ℕ → Bool, (∀ b < K, σ b = σ₀ b) ∧ ¬ Halts (member L σ) s := by
  classical
  set M := 2 * L * K
  let τ : ℕ → Bool := fun x => if x < M then σ₀ (blk L x) else decide (x % 4 = 1)
  obtain ⟨σ, hσ, horb⟩ := realize hL hK σ₀ τ (fun x hx => by simp [τ, M, hx]) s
  refine ⟨σ, hσ, ?_⟩
  -- prefix agreement with `σ₀` while below height `M`
  have hpre : ∀ n, (∀ m < n, (orbit τ s m).1 < M) →
      ∀ m ≤ n, orbit τ s m = orbit (member L σ₀) s m := fun n hn =>
    orbit_congr_prefix fun m hm _ => by simp [τ, member, hn m hm]
  have halive : ∀ n, Alive (orbit τ s n) := by
    intro n
    induction n with
    | zero => exact hsurv 0 (by simp)
    | succ n _ =>
      by_cases hlow : ∀ m < n + 1, (orbit τ s m).1 < M
      · rw [hpre (n + 1) hlow (n + 1) le_rfl]
        refine hsurv (n + 1) fun m hm => ?_
        rw [← hpre (n + 1) hlow m hm.le]; exact hlow m hm
      · simp only [not_forall, not_lt] at hlow
        obtain ⟨m, hm, hmM⟩ := hlow
        have hn : ¬ (orbit τ s n).1 < M := by
          have := orbit_fst_mono τ s (show m ≤ n by omega); omega
        rw [orbit_succ]
        exact alive_step_even_image τ _ (by simp only [τ]; rw [if_neg hn])
  rintro ⟨n, hodd, hzero⟩
  rw [horb] at hodd hzero
  have := halive n hodd; omega

/-- **Unconditional non-halting member for `L = 1`** from Antihydra's start `(8, 0)`. -/
theorem exists_nonhalting_member_one :
    ∃ σ : ℕ → Bool, ¬ Halts (member 1 σ) (8, 0) := by
  obtain ⟨σ, -, h⟩ := nonhalting_member_of_survives (L := 1) (K := 2) le_rfl le_rfl
    (fun _ => false) (8, 0) (fun n hn => by
      cases n with
      | zero => intro h; simp at h
      | succ n => exact absurd (hn 0 (by omega)) (by simp))
  exact ⟨σ, h⟩

/-- Both behaviours in one family: `F_1` contains a member that halts from `(8, 0)` and a
member that never does. -/
theorem F_one_both :
    (∃ σ : ℕ → Bool, Halts (member 1 σ) (8, 0)) ∧
      ∃ σ : ℕ → Bool, ¬ Halts (member 1 σ) (8, 0) :=
  ⟨(exists_halting_member le_rfl 0).imp fun _ h => h.2, exists_nonhalting_member_one⟩

/-! ## The ceiling of rounding-blind arguments -/

/-- **Gate.**  No property of orbits that holds for every member of `F_L` agreeing with Antihydra
on the blocks `< K` can imply non-halting from `(8, 0)`. -/
theorem rounding_blind_cannot_decide {L : ℕ} (hL : 1 ≤ L) (K : ℕ)
    (P : (ℕ → ℕ × ℕ) → Prop)
    (hP : ∀ σ : ℕ → Bool, (∀ b < K, σ b = false) → P (orbit (member L σ) (8, 0)))
    (hdec : ∀ τ : ℕ → Bool, P (orbit τ (8, 0)) → ¬ Halts τ (8, 0)) : False := by
  obtain ⟨σ, hσ, hh⟩ := exists_halting_member hL K
  exact hdec _ (hP σ hσ) hh

/-- Every orbit from height `≥ 2` reaches an odd value of height `≥ M`. -/
theorem exists_odd_above (τ : ℕ → Bool) (s : ℕ × ℕ) (hs : 2 ≤ s.1) (M : ℕ) :
    ∃ n, M ≤ (orbit τ s n).1 ∧ (orbit τ s n).1 % 2 = 1 := by
  have hM : M ≤ (orbit τ s M).1 := (Nat.le_add_left M s.1).trans (orbit_fst_ge_add τ s hs M)
  obtain ⟨j, hj⟩ := exists_odd τ (orbit τ s M) (by have := orbit_fst_ge_add τ s hs M; omega)
  exact ⟨M + j, le_trans hM (orbit_fst_mono τ s (by omega)), by rw [orbit_add]; exact hj⟩

theorem evenCount_mono (τ : ℕ → Bool) (s : ℕ × ℕ) {j k : ℕ} (h : j ≤ k) :
    evenCount τ s j ≤ evenCount τ s k := by
  unfold evenCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

theorem evenCount_congr {τ₁ τ₂ : ℕ → Bool} {s : ℕ × ℕ} {k : ℕ}
    (h : ∀ m < k, orbit τ₁ s m = orbit τ₂ s m) : evenCount τ₁ s k = evenCount τ₂ s k := by
  unfold evenCount
  congr 1
  exact Finset.filter_congr fun m hm => by rw [h m (Finset.mem_range.mp hm)]

/-- Members agreeing with Antihydra below block `K` (`K ≥ 2`) share its orbit up to and
including the first odd value of height `≥ 2LK`. -/
theorem orbit_eq_floor_upto {L K : ℕ} (hL : 1 ≤ L) (σ : ℕ → Bool)
    (hσ : ∀ b < K, σ b = false) (n : ℕ)
    (hn : ∀ m < n, (orbit floorChoice (8, 0) m).1 % 2 = 1 →
      (orbit floorChoice (8, 0) m).1 < 2 * L * K) :
    ∀ m ≤ n, orbit floorChoice (8, 0) m = orbit (member L σ) (8, 0) m := by
  refine orbit_congr_prefix fun m hm ho => ?_
  simp [floorChoice, member, hσ _ ((blk_lt_iff (by omega)).mpr (hn m hm ho))]

/-- The **horizon** of `F_L` at block `K`: the first step at which Antihydra's orbit meets an
odd value of height `≥ 2LK`.  Up to it, every member agreeing with Antihydra below block `K`
follows Antihydra exactly. -/
noncomputable def horizon (L K : ℕ) : ℕ :=
  Nat.find (exists_odd_above floorChoice (8, 0) (by norm_num) (2 * L * K))

theorem horizon_spec (L K : ℕ) :
    2 * L * K ≤ (orbit floorChoice (8, 0) (horizon L K)).1 ∧
      (orbit floorChoice (8, 0) (horizon L K)).1 % 2 = 1 :=
  Nat.find_spec (exists_odd_above floorChoice (8, 0) (by norm_num) (2 * L * K))

theorem lt_of_lt_horizon {L K m : ℕ} (hm : m < horizon L K)
    (ho : (orbit floorChoice (8, 0) m).1 % 2 = 1) :
    (orbit floorChoice (8, 0) m).1 < 2 * L * K := by
  by_contra h
  exact Nat.find_min (exists_odd_above floorChoice (8, 0) (by norm_num) (2 * L * K)) hm
    ⟨by omega, ho⟩

theorem evenCount_eq_min_of_odd_tail (τ : ℕ → Bool) (s : ℕ × ℕ) (n : ℕ)
    (h : ∀ m, n ≤ m → (orbit τ s m).1 % 2 = 1) (k : ℕ) :
    evenCount τ s k = evenCount τ s (min k n) := by
  unfold evenCount
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, he⟩
    refine ⟨lt_min hk (by by_contra hc; have := h m (by omega); omega), he⟩
  · rintro ⟨hk, he⟩; exact ⟨lt_of_lt_of_le hk (min_le_left _ _), he⟩

/-- **The ceiling of rounding-blind arguments, lower half.**  Every member of `F_L` agreeing
with Antihydra below block `K` has at least as many even values in its first `k` steps as
Antihydra has before `min k (horizon L K)`. -/
theorem evenCount_ceiling_lower {L K : ℕ} (hL : 1 ≤ L) (σ : ℕ → Bool)
    (hσ : ∀ b < K, σ b = false) (k : ℕ) :
    evenCount floorChoice (8, 0) (min k (horizon L K)) ≤ evenCount (member L σ) (8, 0) k := by
  have hpre := orbit_eq_floor_upto hL σ hσ (horizon L K) fun m hm ho => lt_of_lt_horizon hm ho
  rw [evenCount_congr (τ₂ := member L σ) fun m hm => hpre m (by omega)]
  exact evenCount_mono _ _ (min_le_left _ _)

/-- **The ceiling of rounding-blind arguments, sharpness.**  For `L ≥ 1`, `K ≥ 2`, some member
agreeing with Antihydra below block `K` attains the lower half for every `k`: its even count
freezes at the horizon.  So the best lower bound on `E_k` that a property of all such members
can give is Antihydra's own even count up to the horizon, a finite computation. -/
theorem evenCount_ceiling_sharp {L K : ℕ} (hL : 1 ≤ L) (hK : 2 ≤ K) :
    ∃ σ : ℕ → Bool, (∀ b < K, σ b = false) ∧ ∀ k,
      evenCount (member L σ) (8, 0) k = evenCount floorChoice (8, 0) (min k (horizon L K)) := by
  classical
  set M := 2 * L * K
  set n₁ := horizon L K
  let τ : ℕ → Bool := fun x => if x < M then false else decide (x % 4 = 3)
  obtain ⟨σ, hσ, horb⟩ := realize hL hK (fun _ => false) τ (fun x hx => by simp [τ, M, hx]) (8, 0)
  refine ⟨σ, hσ, fun k => ?_⟩
  have hpre : ∀ m ≤ n₁, orbit floorChoice (8, 0) m = orbit τ (8, 0) m :=
    orbit_congr_prefix fun m hm ho => by
      have h : (orbit floorChoice (8, 0) m).1 < M := lt_of_lt_horizon hm ho
      simp only [τ, floorChoice]; rw [if_pos h]
  have hspec := horizon_spec L K
  rw [hpre n₁ le_rfl] at hspec
  have htail : ∀ i, M ≤ (orbit τ (8, 0) (n₁ + i)).1 ∧ (orbit τ (8, 0) (n₁ + i)).1 % 2 = 1 := by
    intro i
    induction i with
    | zero => exact hspec
    | succ i ih =>
      have hn : ¬ (orbit τ (8, 0) (n₁ + i)).1 < M := by omega
      rw [← add_assoc, orbit_succ]
      exact ⟨le_trans ih.1 (by have := step_fst_ge τ (orbit τ (8, 0) (n₁ + i)); omega),
        step_odd_image τ _ ih.2 (by simp only [τ]; rw [if_neg hn])⟩
  have hodd : ∀ m, n₁ ≤ m → (orbit τ (8, 0) m).1 % 2 = 1 := fun m hm => by
    have := (htail (m - n₁)).2; rwa [show n₁ + (m - n₁) = m by omega] at this
  have heq : ∀ n, orbit (member L σ) (8, 0) n = orbit τ (8, 0) n := horb
  rw [evenCount_congr (τ₂ := τ) fun m _ => heq m, evenCount_eq_min_of_odd_tail τ _ n₁ hodd,
    evenCount_congr (τ₂ := floorChoice) fun m hm => (hpre m (by omega)).symm]

/-! ## Faithfulness: the all-floor member is Antihydra -/

/-- Antihydra's map `n ↦ n + ⌊n/2⌋`, as in mfornet/antihydra-autoresearch `lean/Antihydra.lean`. -/
def H (n : ℕ) : ℕ := n + n / 2

/-- Antihydra's orbit `8, 12, 18, 27, 40, …`. -/
def a : ℕ → ℕ
  | 0 => 8
  | k + 1 => H (a k)

/-- Odd terms among `a 0, …, a (k-1)`. -/
def O : ℕ → ℕ
  | 0 => 0
  | k + 1 => O k + if a k % 2 = 1 then 1 else 0

/-- Even terms among `a 0, …, a (k-1)`. -/
def E : ℕ → ℕ
  | 0 => 0
  | k + 1 => E k + if a k % 2 = 1 then 0 else 1

/-- **The Antihydra problem** (mfornet's `AntihydraHalts`; formal-conjectures BMO problem 2):
some prefix has more than twice as many odd as even terms.  Conjectured false. -/
def AntihydraHalts : Prop := ∃ k, (O k : ℤ) > 2 * (E k : ℤ)

theorem orbit_floor_fst (n : ℕ) : (orbit floorChoice (8, 0) n).1 = a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orbit_succ, a, ← ih]
    simp only [step, floorChoice, H, Bool.false_eq_true, if_false]
    omega

theorem orbit_floor_snd (n : ℕ) (h : ∀ m < n, ¬ HaltsAt floorChoice (8, 0) m) :
    ((orbit floorChoice (8, 0) n).2 : ℤ) = 2 * (E n : ℤ) - (O n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih := ih fun m hm => h m (by omega)
    have hn := h n (by omega)
    simp only [HaltsAt, orbit_floor_fst] at hn
    rw [orbit_succ, E, O]
    rcases Nat.mod_two_eq_zero_or_one (a n) with he | ho
    · rw [step_snd_even _ _ (by rw [orbit_floor_fst]; exact he)]
      simp only [he]; push_cast; simp; linarith
    · rw [step_snd_odd _ _ (by rw [orbit_floor_fst]; exact ho)]
      have hc : (orbit floorChoice (8, 0) n).2 ≠ 0 := fun hc => hn ⟨ho, hc⟩
      simp only [ho]
      rw [Nat.cast_sub (by omega)]; push_cast; simp; linarith

/-- Trace check against mfornet's table: `a 3 = 27`, `a 14 = 2296`, `E 14 = 8`, `O 14 = 6`. -/
theorem trace_check : a 3 = 27 ∧ a 14 = 2296 ∧ E 14 = 8 ∧ O 14 = 6 := by decide

/-- **Faithfulness anchor.**  The all-floor member halts from `(8, 0)` iff Antihydra halts. -/
theorem halts_floor_iff : Halts floorChoice (8, 0) ↔ AntihydraHalts := by
  classical
  constructor
  · intro h
    let n := Nat.find h
    have hn : HaltsAt floorChoice (8, 0) n := Nat.find_spec h
    have hb := orbit_floor_snd n fun m hm => Nat.find_min h hm
    have ho : a n % 2 = 1 := by rw [← orbit_floor_fst]; exact hn.1
    refine ⟨n + 1, ?_⟩
    rw [hn.2] at hb
    push_cast at hb
    simp only [O, E, ho]; push_cast; simp; linarith
  · rintro ⟨k, hk⟩
    by_contra hnh
    have := orbit_floor_snd k fun m _ hm => hnh ⟨m, hm⟩
    have : (0 : ℤ) ≤ (orbit floorChoice (8, 0) k).2 := by positivity
    linarith

end Collatz.Antihydra.Foils
