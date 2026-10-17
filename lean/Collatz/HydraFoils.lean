/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic
import Collatz.Census
import Collatz.Antihydra.Foils

/-!
# Rounding-choice foils for the whole Hydra schema

int-y1's `Hydra` schema (`Collatz.Bigfoot.Hydra`): `x ↦ p⌊x/q⌋ + g[x mod q]`, walk
`y ↦ y + w[x mod q]`, cryptid = "`y ≥ 0` forever".  T2 (`Collatz.Antihydra.Foils`) showed for
Antihydra that halting members of the rounding-choice family accumulate at the cryptid.  This
file lifts that gate to the schema.

**The family.**  A defect-`d` member adds a choice `τ x : Fin (d+1)` to the image:
`x ↦ p⌊x/q⌋ + g[x mod q] + τ x`, with the walk unchanged (`Sys.step`).  The original map is the
all-zero member (`Sys.step_zero`, `Sys.hydra_iff`).  The block subfamily `F_{L,d}` asks `τ` to be
constant on blocks of `qL` consecutive integers (`member q L σ`, block `x / (qL)`), as in T2.

**Results.**
* `Sys.halting_dense_of_drain`: the general gate.  A *drain certificate* (a trap predicate, a
  potential `Φ ≥ 0`, a multiplier `m`, and an entry predicate satisfied along the starting member's
  orbit) makes halting members dense in `F_{L,d}`: every member agrees, on all blocks `< K`, with a
  halting member.  Uses only expansion (`q < p`) and the certificate.
* `Sys.halting_dense_of_window`: the cyclic window condition (every `d+1` consecutive residues mod
  `q` meet a residue with `w < 0`) is a certificate, for every `p > q ≥ 1`.
* `Sys.window_two`: for `q = 2`, `d = 1`, any residue with `w < 0` gives the window condition.
* `Sys.halting_dense_of_resDrain`: certificates on `(x mod q, ⌊x/q⌋ mod q)`, checked by `decide`.
* Instances: Antihydra, int-y1 #323, BB(2,5) Hydra (`q = 2`, `d = 1`), #218 (`d = 2`; the window
  fails at `d = 1`), Bigfoot (window `d = 14`, reachable window `13`, drift certificate `7`:
  `bigfoot_halting_member`).
* T2 agreement: T2's family is the odd-supported part of `F_{L,1}` for Antihydra's data, with the
  same halting predicate (`antihydra_t2_halts_iff`, `t2_member_emb`).
-/

namespace Collatz.HydraFoils

open Collatz.Bigfoot Collatz.Antihydra

/-- A system in int-y1's `Hydra` schema: slope `p/q`, geometric offsets `g`, walk offsets `w`. -/
structure Sys where
  p : ℕ
  q : ℕ
  g : List ℤ
  w : List ℤ

namespace Sys

variable (S : Sys)

/-- The residue index `x mod q` as `hydraIterate` reads its lists. -/
def res (x : ℤ) : ℕ := (x % (S.q : ℤ)).toNat

/-- The floor image `p⌊x/q⌋ + g[x mod q]`. -/
def img (x : ℤ) : ℤ := (S.p : ℤ) * (x / (S.q : ℤ)) + S.g.getD (S.res x) 0

/-- The walk increment `w[x mod q]` at value `x`. -/
def wt (x : ℤ) : ℤ := S.w.getD (S.res x) 0

/-- One step of the defect-`d` member with choice `τ`: the image gets `τ x ∈ [0, d]` added; the
walk is unchanged. -/
def step {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) : ℤ × ℤ :=
  (S.img s.1 + ((τ s.1 : ℕ) : ℤ), s.2 + S.wt s.1)

/-- The orbit of `s` under the member `τ`. -/
def orbit {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) (n : ℕ) : ℤ × ℤ := (S.step τ)^[n] s

/-- The member `τ` halts from `s`: the walk goes negative. -/
def Halts {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) : Prop := ∃ n, (S.orbit τ s n).2 < 0

/-- **Faithfulness anchor.**  The all-zero member is int-y1's `hydraIterate`. -/
theorem step_zero (d : ℕ) :
    S.step (fun _ => (0 : Fin (d + 1))) = hydraIterate S.p S.q S.g S.w := by
  funext ⟨x, y⟩
  simp [step, hydraIterate, img, wt, res]

/-- **Faithfulness anchor.**  The cryptid `Hydra p q g w s` is "the all-zero member never
halts". -/
theorem hydra_iff (d : ℕ) (s : ℤ × ℤ) :
    Hydra S.p S.q S.g S.w s ↔ ¬ S.Halts (fun _ => (0 : Fin (d + 1))) s := by
  simp only [Hydra, Halts, orbit, step_zero, not_exists, not_lt, ge_iff_le]

@[simp] theorem orbit_zero {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) : S.orbit τ s 0 = s := rfl

theorem orbit_succ {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) (n : ℕ) :
    S.orbit τ s (n + 1) = S.step τ (S.orbit τ s n) :=
  Function.iterate_succ_apply' _ _ _

theorem step_congr {d : ℕ} {τ₁ τ₂ : ℤ → Fin (d + 1)} {s : ℤ × ℤ} (h : τ₁ s.1 = τ₂ s.1) :
    S.step τ₁ s = S.step τ₂ s := by
  simp [step, h]

/-- Two members whose choices agree at the first `n` values of the first one's orbit have the
same orbit up to step `n`. -/
theorem orbit_congr_prefix {d : ℕ} {τ₁ τ₂ : ℤ → Fin (d + 1)} {s : ℤ × ℤ} {n : ℕ}
    (h : ∀ m < n, τ₁ (S.orbit τ₁ s m).1 = τ₂ (S.orbit τ₁ s m).1) :
    ∀ m ≤ n, S.orbit τ₁ s m = S.orbit τ₂ s m := by
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [orbit_succ, orbit_succ, ← ih (by omega)]
    exact S.step_congr (h m (by omega))

theorem orbit_congr {d : ℕ} {τ₁ τ₂ : ℤ → Fin (d + 1)} {s : ℤ × ℤ}
    (h : ∀ m, τ₁ (S.orbit τ₁ s m).1 = τ₂ (S.orbit τ₁ s m).1) (n : ℕ) :
    S.orbit τ₁ s n = S.orbit τ₂ s n :=
  S.orbit_congr_prefix (n := n) (fun m _ => h m) n le_rfl

theorem res_lt (hq : 0 < S.q) (x : ℤ) : S.res x < S.q := by
  have h1 := Int.emod_nonneg x (b := (S.q : ℤ)) (by omega)
  have h2 := Int.emod_lt_of_pos x (b := (S.q : ℤ)) (by omega)
  unfold res; omega

theorem res_add (hq : 0 < S.q) (x : ℤ) (c : ℕ) : S.res (x + c) = (S.res x + c) % S.q := by
  have ha : ((S.res x : ℕ) : ℤ) = x % S.q :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have : (x + c) % (S.q : ℤ) = (((S.res x + c) % S.q : ℕ) : ℤ) := by
    rw [Int.natCast_mod, Nat.cast_add, ha, Int.emod_add_emod]
  unfold res at *
  rw [this, Int.toNat_natCast]

theorem getD_lower (l : List ℤ) : ∃ B : ℤ, 0 ≤ B ∧ ∀ i, -B ≤ l.getD i 0 := by
  induction l with
  | nil => exact ⟨0, le_rfl, fun i => by simp⟩
  | cons a l ih =>
    obtain ⟨B, hB, h⟩ := ih
    refine ⟨max B (-a), le_max_of_le_left hB, fun i => ?_⟩
    cases i with
    | zero => simp only [List.getD_cons_zero]; have := le_max_right B (-a); linarith
    | succ i => simp only [List.getD_cons_succ]; have := le_max_left B (-a); linarith [h i]

/-- **Expansion.**  For `p > q ≥ 1`, the image gains at least `W` above some height. -/
theorem exists_gap (hq : 0 < S.q) (hpq : S.q < S.p) (W : ℤ) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ x, M ≤ x → x + W ≤ S.img x := by
  obtain ⟨B, hB, hg⟩ := getD_lower S.g
  have hq' : (0 : ℤ) < S.q := by exact_mod_cast hq
  have hpq' : (S.q : ℤ) + 1 ≤ S.p := by exact_mod_cast hpq
  refine ⟨S.q * (B + S.q + |W|), by positivity, fun x hx => ?_⟩
  have ht : B + S.q + |W| ≤ x / S.q := by
    rw [Int.le_ediv_iff_mul_le hq']; linarith
  have ht0 : 0 ≤ x / S.q := le_trans (by positivity) ht
  have h1 : ((S.q : ℤ) + 1) * (x / S.q) ≤ S.p * (x / S.q) := mul_le_mul_of_nonneg_right hpq' ht0
  have h2 := Int.emod_add_mul_ediv x S.q
  have h3 := Int.emod_lt_of_pos x hq'
  have h4 := hg (S.res x)
  have h5 := le_abs_self W
  unfold img
  nlinarith

end Sys

/-- Block index of a value: blocks of `qL` consecutive integers. -/
def blk (q L : ℕ) (x : ℤ) : ℤ := x / ((q * L : ℕ) : ℤ)

/-- The member of `F_{L,d}` with block choices `σ`. -/
def member (q L : ℕ) {d : ℕ} (σ : ℤ → Fin (d + 1)) : ℤ → Fin (d + 1) := fun x => σ (blk q L x)

theorem member_zero (q L d : ℕ) :
    member q L (fun _ => (0 : Fin (d + 1))) = fun _ => 0 := rfl

namespace Sys

variable (S : Sys)

/-- **Realization.**  Above height `qL·K`, where every step gains at least `qL`, the orbit
visits each block at most once.  So a value-wise choice `τ` that is block-wise `σ₀` below that
height is, along its own orbit, the choice of a member of `F_{L,d}` agreeing with `σ₀` on the
blocks `< K`. -/
theorem realize (hq : 0 < S.q) {d L : ℕ} (hL : 1 ≤ L) {K : ℤ}
    (hgap : ∀ x, ((S.q * L : ℕ) : ℤ) * K ≤ x → x + ((S.q * L : ℕ) : ℤ) ≤ S.img x)
    (σ₀ τ : ℤ → Fin (d + 1)) (hτ : ∀ x, x < ((S.q * L : ℕ) : ℤ) * K → τ x = σ₀ (blk S.q L x))
    (s : ℤ × ℤ) :
    ∃ σ : ℤ → Fin (d + 1), (∀ b < K, σ b = σ₀ b) ∧
      ∀ n, S.orbit (member S.q L σ) s n = S.orbit τ s n := by
  classical
  set N : ℤ := ((S.q * L : ℕ) : ℤ) with hN
  have hN0 : 0 < N := by have : 0 < S.q * L := Nat.mul_pos hq hL; omega
  set x : ℕ → ℤ := fun n => (S.orbit τ s n).1 with hx
  have blk_lt : ∀ y, blk S.q L y < K ↔ y < N * K := fun y => by
    unfold blk; rw [Int.ediv_lt_iff_lt_mul hN0, mul_comm]
  have hup : ∀ n, N * K ≤ x n → x n + N ≤ x (n + 1) := fun n h => by
    have h1 := hgap (x n) h
    have h2 : x (n + 1) = S.img (x n) + ((τ (x n) : ℕ) : ℤ) := by
      simp only [hx, orbit_succ, step]
    have : (0 : ℤ) ≤ ((τ (x n) : ℕ) : ℤ) := by positivity
    linarith
  have hmono : ∀ n k, N * K ≤ x n → x n ≤ x (n + k) ∧ N * K ≤ x (n + k) := by
    intro n k h
    induction k with
    | zero => exact ⟨le_rfl, h⟩
    | succ k ih =>
      have := hup (n + k) ih.2
      rw [← add_assoc]
      constructor <;> linarith [ih.1, ih.2]
  let σ : ℤ → Fin (d + 1) := fun b =>
    if b < K then σ₀ b else if h : ∃ n, blk S.q L (x n) = b then τ (x (Nat.find h)) else 0
  refine ⟨σ, fun b hb => by simp [σ, hb], ?_⟩
  have key : ∀ n, τ (x n) = member S.q L σ (x n) := by
    intro n
    change τ (x n) = σ (blk S.q L (x n))
    by_cases hlt : x n < N * K
    · have hb := (blk_lt _).mpr hlt
      simp only [σ, hb, if_true]; exact hτ _ hlt
    · have hb : ¬ blk S.q L (x n) < K := fun h => hlt ((blk_lt _).mp h)
      have h : ∃ m, blk S.q L (x m) = blk S.q L (x n) := ⟨n, rfl⟩
      simp only [σ, hb, if_false, dif_pos h]
      have hspec : blk S.q L (x (Nat.find h)) = blk S.q L (x n) := Nat.find_spec h
      have hle : Nat.find h ≤ n := Nat.find_min' h rfl
      rcases Nat.lt_or_ge (Nat.find h) n with hlt' | hge
      · exfalso
        set m := Nat.find h
        have hm : N * K ≤ x m := by
          by_contra hc
          have := (blk_lt _).mpr (not_le.mp hc)
          rw [hspec] at this
          exact hb this
        have h1 := hup m hm
        have h2 := (hmono (m + 1) (n - (m + 1)) (by linarith)).1
        rw [show m + 1 + (n - (m + 1)) = n by omega] at h2
        have h3 : blk S.q L (x m) + 1 ≤ blk S.q L (x n) := by
          unfold blk
          rw [← hN, Int.le_ediv_iff_mul_le hN0]
          have := Int.ediv_mul_le (x m) (ne_of_gt hN0)
          linarith
        rw [hspec] at h3
        linarith
      · rw [show Nat.find h = n by omega]
  intro n
  exact (S.orbit_congr (τ₁ := τ) (τ₂ := member S.q L σ) (fun m => key m) n).symm

/-- **The general gate.**  A drain certificate for defect `d` makes halting members dense in
`F_{L,d}`.  The certificate: a trap predicate that some choice keeps, along which the potential
`m y + Φ x` falls by at least one per step; an entry predicate `Ent` from which some choice enters
the trap, holding along the orbit of the starting member `σ₀`; and strict growth at `Ent` values
above the start.  Then some member agreeing with `σ₀` on every block `< K` halts from `s`. -/
theorem halting_dense_of_drain (hq : 0 < S.q) (hpq : S.q < S.p) {d L : ℕ} (hL : 1 ≤ L)
    (Ent Trap : ℤ → Prop) (Φ : ℤ → ℕ) (m : ℕ)
    (htrap : ∀ x, Trap x → ∃ c : Fin (d + 1),
      Trap (S.img x + (c : ℕ)) ∧ (m : ℤ) * S.wt x + Φ (S.img x + (c : ℕ)) + 1 ≤ Φ x)
    (hent : ∀ x, Ent x → ∃ c : Fin (d + 1), Trap (S.img x + (c : ℕ)))
    (σ₀ : ℤ → Fin (d + 1)) (K : ℤ) (s : ℤ × ℤ)
    (horig : ∀ n, Ent (S.orbit (member S.q L σ₀) s n).1)
    (hesc : ∀ x, s.1 ≤ x → Ent x → x + 1 ≤ S.img x) :
    ∃ σ : ℤ → Fin (d + 1), (∀ b < K, σ b = σ₀ b) ∧ S.Halts (member S.q L σ) s := by
  classical
  obtain ⟨M, hM0, hM⟩ := S.exists_gap hq hpq ((S.q * L : ℕ) : ℤ)
  set N : ℤ := ((S.q * L : ℕ) : ℤ) with hN
  have hN1 : 1 ≤ N := by have : 0 < S.q * L := Nat.mul_pos hq hL; omega
  set K' := max K M
  set H := N * K' with hH
  have hHM : M ≤ H := by
    have : M ≤ K' := le_max_right K M
    nlinarith
  have hgap : ∀ x, H ≤ x → x + N ≤ S.img x := fun x hx => hM x (le_trans hHM hx)
  -- the value-wise choice: `σ₀` below `H`, steering into and along the trap above it
  let τ : ℤ → Fin (d + 1) := fun x =>
    if x < H then σ₀ (blk S.q L x) else
      if h : Trap x then Classical.choose (htrap x h) else
        if h' : Ent x then Classical.choose (hent x h') else 0
  have τ_lo : ∀ z, z < H → τ z = σ₀ (blk S.q L z) := fun z hz => by
    simp only [τ]; rw [if_pos hz]
  have τ_hi : ∀ z, H ≤ z → (h : Trap z) → τ z = Classical.choose (htrap z h) := fun z hz h => by
    simp only [τ]; rw [if_neg (not_lt.mpr hz), dif_pos h]
  have τ_ent : ∀ z, H ≤ z → ¬ Trap z → (h : Ent z) → τ z = Classical.choose (hent z h) :=
    fun z hz ht h => by simp only [τ]; rw [if_neg (not_lt.mpr hz), dif_neg ht, dif_pos h]
  clear_value τ
  obtain ⟨σ, hσ, horb⟩ := S.realize hq hL (K := K') hgap σ₀ τ (fun x hx => τ_lo x hx) s
  refine ⟨σ, fun b hb => hσ b (lt_of_lt_of_le hb (le_max_left _ _)), ?_⟩
  suffices hτ : S.Halts τ s by
    obtain ⟨n, hn⟩ := hτ
    exact ⟨n, by rw [horb]; exact hn⟩
  set x : ℕ → ℤ := fun n => (S.orbit τ s n).1 with hx
  set y : ℕ → ℤ := fun n => (S.orbit τ s n).2 with hy
  have hxs : ∀ n, x (n + 1) = S.img (x n) + ((τ (x n) : ℕ) : ℤ) := fun n => by
    simp only [hx, orbit_succ, step]
  have hys : ∀ n, y (n + 1) = y n + S.wt (x n) := fun n => by
    simp only [hx, hy, orbit_succ, step]
  have hpre : ∀ n, (∀ m < n, x m < H) →
      ∀ m ≤ n, S.orbit τ s m = S.orbit (member S.q L σ₀) s m := fun n hn =>
    S.orbit_congr_prefix fun m hm => by rw [τ_lo _ (hn m hm)]; rfl
  -- escape: the orbit reaches height `H`
  have hreach : ∃ n, H ≤ x n := by
    by_contra hne
    have hne' : ∀ n, x n < H := fun n => not_le.mp fun h => hne ⟨n, h⟩
    have hagree : ∀ n, S.orbit τ s n = S.orbit (member S.q L σ₀) s n := fun n =>
      hpre n (fun m _ => hne' m) n le_rfl
    have hgrow : ∀ n : ℕ, s.1 + n ≤ x n := by
      intro n
      induction n with
      | zero => simp [hx]
      | succ n ih =>
        have he : Ent (x n) := by
          have := horig n
          rw [← hagree n] at this
          exact this
        have h1 := hesc (x n) (by linarith) he
        have : (0 : ℤ) ≤ ((τ (x n) : ℕ) : ℤ) := by positivity
        rw [hxs]; push_cast; linarith
    have h1 := hgrow (H - s.1).toNat
    have h2 := hne' (H - s.1).toNat
    have h3 : H - s.1 ≤ ((H - s.1).toNat : ℤ) := Int.self_le_toNat _
    linarith
  set n₀ := Nat.find hreach with hn₀def
  have hn₀ : H ≤ x n₀ := Nat.find_spec hreach
  have hbelow : ∀ m < n₀, x m < H := fun m hm => not_le.mp (Nat.find_min hreach hm)
  have hEnt₀ : Ent (x n₀) := by
    have := horig n₀
    rwa [← hpre n₀ hbelow n₀ le_rfl] at this
  have habove : ∀ k, H ≤ x (n₀ + k) := by
    intro k
    induction k with
    | zero => simpa using hn₀
    | succ k ih =>
      rw [← add_assoc, hxs]
      have := hgap _ ih
      have : (0 : ℤ) ≤ ((τ (x (n₀ + k)) : ℕ) : ℤ) := by positivity
      linarith
  have hge : ∀ k, H ≤ x (n₀ + 1 + k) := fun k => by
    have := habove (1 + k); rwa [← add_assoc] at this
  -- from step `n₀ + 1` on, the orbit is in the trap
  have htr : ∀ k, Trap (x (n₀ + 1 + k)) := by
    intro k
    induction k with
    | zero =>
      rw [add_zero, hxs]
      by_cases ht : Trap (x n₀)
      · rw [τ_hi _ hn₀ ht]; exact (Classical.choose_spec (htrap _ ht)).1
      · rw [τ_ent _ hn₀ ht hEnt₀]; exact Classical.choose_spec (hent _ hEnt₀)
    | succ k ih =>
      rw [show n₀ + 1 + (k + 1) = n₀ + 1 + k + 1 by omega, hxs]
      rw [τ_hi _ (hge k) ih]; exact (Classical.choose_spec (htrap _ ih)).1
  -- the potential `m y + Φ x` falls by one per step in the trap
  set V : ℕ → ℤ := fun k => (m : ℤ) * y (n₀ + 1 + k) + Φ (x (n₀ + 1 + k)) with hV
  have hdec : ∀ k, V (k + 1) + 1 ≤ V k := by
    intro k
    have ih := htr k
    have e := τ_hi _ (hge k) ih
    have spec := (Classical.choose_spec (htrap _ ih)).2
    simp only [hV]
    rw [show n₀ + 1 + (k + 1) = n₀ + 1 + k + 1 by omega, hxs, hys, e]
    rw [mul_add]
    linarith
  have hVk : ∀ k : ℕ, V k + k ≤ V 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => have := hdec k; push_cast; linarith
  set k : ℕ := (V 0).toNat + 1
  refine ⟨n₀ + 1 + k, ?_⟩
  change y (n₀ + 1 + k) < 0
  have h1 : V k < 0 := by
    have := hVk k
    have : V 0 ≤ ((V 0).toNat : ℤ) := Int.self_le_toNat _
    have : (k : ℤ) = ((V 0).toNat : ℤ) + 1 := by push_cast [k]; ring
    linarith
  have hΦ : (0 : ℤ) ≤ Φ (x (n₀ + 1 + k)) := by positivity
  have hmy : (m : ℤ) * y (n₀ + 1 + k) < 0 := by simp only [hV] at h1; linarith
  by_contra hy0
  have : 0 ≤ (m : ℤ) * y (n₀ + 1 + k) := mul_nonneg (by positivity) (not_lt.mp hy0)
  linarith

/-- The cyclic window condition: every `d + 1` consecutive residues mod `q` contain one with
`w < 0`. -/
def Window (d : ℕ) : Prop := ∀ a < S.q, ∃ c ≤ d, S.w.getD ((a + c) % S.q) 0 < 0

/-- **Window gate.**  For every `p > q ≥ 1`, the window condition at defect `d` makes halting
members dense in `F_{L,d}` from any start above which the image grows. -/
theorem halting_dense_of_window (hq : 0 < S.q) (hpq : S.q < S.p) {d L : ℕ} (hL : 1 ≤ L)
    (hW : S.Window d) (σ₀ : ℤ → Fin (d + 1)) (K : ℤ) (s : ℤ × ℤ)
    (hesc : ∀ x, s.1 ≤ x → x + 1 ≤ S.img x) :
    ∃ σ : ℤ → Fin (d + 1), (∀ b < K, σ b = σ₀ b) ∧ S.Halts (member S.q L σ) s := by
  have hstep : ∀ x : ℤ, ∃ c : Fin (d + 1), S.wt (S.img x + (c : ℕ)) < 0 := fun x => by
    obtain ⟨c, hc, hw⟩ := hW (S.res (S.img x)) (S.res_lt hq _)
    exact ⟨⟨c, by omega⟩, by simp only [wt]; rw [S.res_add hq]; exact hw⟩
  refine S.halting_dense_of_drain hq hpq hL (fun _ => True) (fun x => S.wt x < 0) (fun _ => 0) 1
    (fun x hx => ?_) (fun x _ => hstep x) σ₀ K s (fun _ => trivial) (fun x hx _ => hesc x hx)
  obtain ⟨c, hc⟩ := hstep x
  exact ⟨c, hc, by push_cast; linarith⟩

/-- For `q = 2`, `d = 1`: any residue with `w < 0` gives the window condition. -/
theorem window_two (h2 : S.q = 2) {r : ℕ} (hr : r < 2) (hw : S.w.getD r 0 < 0) :
    S.Window 1 := by
  intro a ha
  refine ⟨(r + 2 - a) % 2, by omega, ?_⟩
  rw [h2, show (a + (r + 2 - a) % 2) % 2 = r by omega]
  exact hw

/-! ## Residue-table certificates

The steering only sees `x` through its residue `r = x mod q` and the next digit
`t = ⌊x/q⌋ mod q`, so a certificate on residues is a finite check (`decide`). -/

/-- The residue of `p t + g[r] + c` mod `q`. -/
def resNext (r t c : ℕ) : ℕ := (((S.p : ℤ) * t + S.g.getD r 0 + c) % S.q).toNat

theorem res_img_add (hq : 0 < S.q) (x : ℤ) (c : ℕ) :
    S.res (S.img x + c) = S.resNext (S.res x) ((x / S.q) % S.q).toNat c := by
  have ht : (((x / S.q) % S.q).toNat : ℤ) = (x / S.q) % S.q :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  unfold res resNext img
  rw [ht]
  congr 1
  exact ((((Int.mod_modEq (x / S.q) S.q).mul_left (S.p : ℤ)).add_right _).add_right _).symm

theorem digit_lt (hq : 0 < S.q) (x : ℤ) : ((x / S.q) % S.q).toNat < S.q := by
  have h1 := Int.emod_nonneg (x / S.q) (b := (S.q : ℤ)) (by omega)
  have h2 := Int.emod_lt_of_pos (x / S.q) (b := (S.q : ℤ)) (by omega)
  omega

/-- A residue-table drain certificate at defect `d`: from every trap residue `r ∈ R` and next
digit `t`, some choice `c ≤ d` lands in `R` with the potential `m w + φ` falling by one; from
every entry residue `r ∈ E`, some choice lands in `R`. -/
def ResDrain (d : ℕ) (E R : ℕ → Bool) (φ : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ r < S.q, R r = true → ∀ t < S.q, ∃ c ≤ d, R (S.resNext r t c) = true ∧
      (m : ℤ) * S.w.getD r 0 + φ (S.resNext r t c) + 1 ≤ φ r) ∧
    ∀ r < S.q, E r = true → ∀ t < S.q, ∃ c ≤ d, R (S.resNext r t c) = true

/-- **Residue-table gate.**  A residue-table certificate makes halting members dense, provided
the starting member's orbit stays in the entry residues and the image grows there. -/
theorem halting_dense_of_resDrain (hq : 0 < S.q) (hpq : S.q < S.p) {d L : ℕ} (hL : 1 ≤ L)
    {E R : ℕ → Bool} {φ : ℕ → ℕ} {m : ℕ} (hD : S.ResDrain d E R φ m)
    (σ₀ : ℤ → Fin (d + 1)) (K : ℤ) (s : ℤ × ℤ)
    (horig : ∀ n, E (S.res (S.orbit (member S.q L σ₀) s n).1) = true)
    (hesc : ∀ x, s.1 ≤ x → E (S.res x) = true → x + 1 ≤ S.img x) :
    ∃ σ : ℤ → Fin (d + 1), (∀ b < K, σ b = σ₀ b) ∧ S.Halts (member S.q L σ) s := by
  refine S.halting_dense_of_drain hq hpq hL (fun x => E (S.res x) = true)
    (fun x => R (S.res x) = true) (fun x => φ (S.res x)) m (fun x hx => ?_) (fun x hx => ?_)
    σ₀ K s horig hesc
  · obtain ⟨c, hc, h1, h2⟩ := hD.1 _ (S.res_lt hq x) hx _ (S.digit_lt hq x)
    exact ⟨⟨c, by omega⟩, by simp only [S.res_img_add hq]; exact h1,
      by simp only [S.res_img_add hq, wt]; exact h2⟩
  · obtain ⟨c, hc, h1⟩ := hD.2 _ (S.res_lt hq x) hx _ (S.digit_lt hq x)
    exact ⟨⟨c, by omega⟩, by simp only [S.res_img_add hq]; exact h1⟩

/-! ## Lifted certificates

A certificate on `x mod Q` (any `Q`) is a finite check over `x mod qQ`, because the image mod `Q`
depends only on `x mod qQ`.  Taking `Q = q^k` lets the steering look `k` digits ahead. -/

theorem res_shift (y k : ℤ) : S.res (y + S.q * k) = S.res y := by
  unfold res; rw [Int.add_mul_emod_self_left]

theorem img_shift (hq : 0 < S.q) (Q : ℕ) (y k : ℤ) :
    S.img (y + S.q * Q * k) = S.img y + S.p * Q * k := by
  have hq0 : (S.q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : y + (S.q : ℤ) * Q * k = y + S.q * (Q * k) := by ring
  unfold img
  rw [e, S.res_shift, Int.add_mul_ediv_left _ _ hq0]
  ring

/-- **Lifted gate.**  A potential `φ` on residues mod `Q`, with a choice `c ≤ d` at every
`u < qQ` along which `m w + φ` falls by one, makes halting members dense in `F_{L,d}`. -/
theorem halting_dense_of_modCert (hq : 0 < S.q) (hpq : S.q < S.p) {d L Q : ℕ} (hL : 1 ≤ L)
    (hQ : 0 < Q) (φ : ℕ → ℕ) (m : ℕ)
    (hcert : ∀ u < S.q * Q, ∃ c ≤ d, (m : ℤ) * S.w.getD (u % S.q) 0 +
      φ (((S.img u + c) % Q).toNat) + 1 ≤ φ (u % Q))
    (σ₀ : ℤ → Fin (d + 1)) (K : ℤ) (s : ℤ × ℤ) (hesc : ∀ x, s.1 ≤ x → x + 1 ≤ S.img x) :
    ∃ σ : ℤ → Fin (d + 1), (∀ b < K, σ b = σ₀ b) ∧ S.Halts (member S.q L σ) s := by
  refine S.halting_dense_of_drain hq hpq hL (fun _ => True) (fun _ => True)
    (fun x => φ ((x % Q).toNat)) m (fun x _ => ?_) (fun _ _ => ⟨0, trivial⟩) σ₀ K s
    (fun _ => trivial) (fun x hx _ => hesc x hx)
  have hqQ : (0 : ℤ) < (S.q : ℤ) * Q := by positivity
  set u : ℕ := (x % ((S.q : ℤ) * Q)).toNat with hu
  have hu' : (u : ℤ) = x % ((S.q : ℤ) * Q) := Int.toNat_of_nonneg (Int.emod_nonneg _ hqQ.ne')
  have hult : u < S.q * Q := by
    have := Int.emod_lt_of_pos x hqQ
    have : (u : ℤ) < (S.q * Q : ℕ) := by push_cast; omega
    exact_mod_cast this
  have hx : x = u + S.q * Q * (x / ((S.q : ℤ) * Q)) := by
    rw [hu']; have := Int.emod_add_mul_ediv x ((S.q : ℤ) * Q); linarith
  obtain ⟨c, hc, h⟩ := hcert u hult
  refine ⟨⟨c, by omega⟩, trivial, ?_⟩
  have hw : S.wt x = S.w.getD (u % S.q) 0 := by
    unfold wt
    congr 1
    rw [hx, mul_assoc, S.res_shift]
    unfold res
    rw [← Int.natCast_mod, Int.toNat_natCast]
  have hφx : (x % Q).toNat = u % Q := by
    rw [hx, mul_comm (S.q : ℤ) Q, mul_assoc, Int.add_mul_emod_self_left, ← Int.natCast_mod,
      Int.toNat_natCast]
  have hφn : ((S.img x + ((⟨c, by omega⟩ : Fin (d + 1)) : ℕ)) % Q).toNat =
      ((S.img u + c) % Q).toNat := by
    congr 1
    change (S.img x + (c : ℤ)) % Q = _
    rw [hx, S.img_shift hq Q,
      show S.img u + S.p * Q * (x / ((S.q : ℤ) * Q)) + c =
        S.img u + c + Q * (S.p * (x / ((S.q : ℤ) * Q))) by ring,
      Int.add_mul_emod_self_left]
  rw [hw, hφx, hφn]
  exact h

end Sys

/-! ## Instances: the census in the schema -/

/-- Antihydra's data (`Census.antihydra`). -/
def antihydraSys : Sys := ⟨3, 2, [0, 1], [2, -1]⟩
/-- int-y1's #323 (`Census.hydra323`). -/
def hydra323Sys : Sys := ⟨3, 2, [1, 2], [2, -1]⟩
/-- BB(2,5) Hydra (`Census.hydraBB25`). -/
def hydraBB25Sys : Sys := ⟨3, 2, [3, 3], [-1, 2]⟩
/-- int-y1's #218 (`Census.hydra218`). -/
def hydra218Sys : Sys := ⟨4, 3, [1, 2, 3], [3, 1, -1]⟩
/-- Bigfoot in the `X` coordinate (`Bigfoot.Dyn.nonhalt_iff_hydra`). -/
def bigfootSys : Sys := ⟨32, 24, Dyn.bigfootH, Dyn.bigfootW⟩

theorem antihydra_iff : Census.antihydra ↔ ¬ antihydraSys.Halts (fun _ => (0 : Fin 2)) (8, 0) :=
  antihydraSys.hydra_iff 1 (8, 0)

theorem hydra323_iff : Census.hydra323 ↔ ¬ hydra323Sys.Halts (fun _ => (0 : Fin 2)) (1, 2) :=
  hydra323Sys.hydra_iff 1 (1, 2)

theorem hydraBB25_iff : Census.hydraBB25 ↔ ¬ hydraBB25Sys.Halts (fun _ => (0 : Fin 2)) (3, 0) :=
  hydraBB25Sys.hydra_iff 1 (3, 0)

theorem hydra218_iff : Census.hydra218 ↔ ¬ hydra218Sys.Halts (fun _ => (0 : Fin 3)) (1, 3) :=
  hydra218Sys.hydra_iff 2 (1, 3)

theorem bigfoot_iff :
    (∀ n, Dyn.orbit n ≠ none) ↔ ¬ bigfootSys.Halts (fun _ => (0 : Fin 1)) (10, 2) :=
  Dyn.nonhalt_iff_hydra.trans (bigfootSys.hydra_iff 0 (10, 2))

/-- For `q = 2`, the image read off by parity. -/
theorem img_two (S : Sys) (h2 : S.q = 2) (a b : ℤ) (hg : S.g = [a, b]) (x : ℤ) :
    S.img x = S.p * (x / 2) + if x % 2 = 0 then a else b := by
  unfold Sys.img Sys.res
  rw [h2, hg]
  rcases Int.emod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- **T3, target 2 (Antihydra).**  Halting members are dense in `F_{L,1}` for Antihydra's data:
every member agrees on all blocks `< K` with a member that halts from `(8, 0)`. -/
theorem antihydra_halting_dense {L : ℕ} (hL : 1 ≤ L) (σ₀ : ℤ → Fin 2) (K : ℤ) :
    ∃ σ : ℤ → Fin 2, (∀ b < K, σ b = σ₀ b) ∧ antihydraSys.Halts (member 2 L σ) (8, 0) :=
  antihydraSys.halting_dense_of_window (by decide) (by decide) hL
    (antihydraSys.window_two rfl (r := 1) (by norm_num) (by decide)) σ₀ K (8, 0)
    (fun x hx => by
      rw [img_two antihydraSys rfl 0 1 rfl]
      change x + 1 ≤ 3 * (x / 2) + _
      split_ifs <;> omega)

/-- **T3, target 2 (#323).** -/
theorem hydra323_halting_dense {L : ℕ} (hL : 1 ≤ L) (σ₀ : ℤ → Fin 2) (K : ℤ) :
    ∃ σ : ℤ → Fin 2, (∀ b < K, σ b = σ₀ b) ∧ hydra323Sys.Halts (member 2 L σ) (1, 2) :=
  hydra323Sys.halting_dense_of_window (by decide) (by decide) hL
    (hydra323Sys.window_two rfl (r := 1) (by norm_num) (by decide)) σ₀ K (1, 2)
    (fun x hx => by
      rw [img_two hydra323Sys rfl 1 2 rfl]
      change x + 1 ≤ 3 * (x / 2) + _
      split_ifs <;> omega)

/-- **T3, target 2 (BB(2,5) Hydra).** -/
theorem hydraBB25_halting_dense {L : ℕ} (hL : 1 ≤ L) (σ₀ : ℤ → Fin 2) (K : ℤ) :
    ∃ σ : ℤ → Fin 2, (∀ b < K, σ b = σ₀ b) ∧ hydraBB25Sys.Halts (member 2 L σ) (3, 0) :=
  hydraBB25Sys.halting_dense_of_window (by decide) (by decide) hL
    (hydraBB25Sys.window_two rfl (r := 0) (by norm_num) (by decide)) σ₀ K (3, 0)
    (fun x hx => by
      rw [img_two hydraBB25Sys rfl 3 3 rfl]
      change x + 1 ≤ 3 * (x / 2) + _
      split_ifs <;> omega)

/-! ## T2's family is the odd-supported part of `F_{L,1}` for Antihydra -/

/-- T2's choice `τ : ℕ → Bool`, read in the generic family: `+1` (ceiling) at the odd values
where `τ` says so, `0` elsewhere (T2's choice is inert at even values). -/
def t2emb (τ : ℕ → Bool) : ℤ → Fin 2 := fun x => if x % 2 = 1 ∧ τ x.toNat = true then 1 else 0

theorem t2emb_floor : t2emb Foils.floorChoice = fun _ => 0 := by
  funext x; simp [t2emb, Foils.floorChoice]

theorem t2_step_fst (τ : ℕ → Bool) (u : ℕ × ℕ) (y : ℤ) :
    ((Foils.step τ u).1 : ℤ) = (antihydraSys.step (t2emb τ) ((u.1 : ℤ), y)).1 := by
  simp only [Foils.step, Sys.step]
  rw [img_two antihydraSys rfl 0 1 rfl]
  change (((3 * u.1 + if τ u.1 then 1 else 0) / 2 : ℕ) : ℤ) =
    3 * ((u.1 : ℤ) / 2) + (if (u.1 : ℤ) % 2 = 0 then 0 else 1) + ((t2emb τ u.1 : ℕ) : ℤ)
  simp only [t2emb, Int.toNat_natCast]
  split_ifs <;> simp_all <;> omega

theorem t2_orbit_fst (τ : ℕ → Bool) (x c : ℕ) (n : ℕ) :
    ((Foils.orbit τ (x, c) n).1 : ℤ) = (antihydraSys.orbit (t2emb τ) ((x : ℤ), (c : ℤ)) n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Foils.orbit_succ, Sys.orbit_succ, t2_step_fst τ _ (antihydraSys.orbit _ _ n).2, ih]

/-- Before T2's machine halts, its counter is the generic walk. -/
theorem t2_orbit_snd (τ : ℕ → Bool) (x c : ℕ) (n : ℕ)
    (h : ∀ m < n, ¬ Foils.HaltsAt τ (x, c) m) :
    ((Foils.orbit τ (x, c) n).2 : ℤ) =
      (antihydraSys.orbit (t2emb τ) ((x : ℤ), (c : ℤ)) n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih := ih fun m hm => h m (by omega)
    have hn := h n (by omega)
    have hf := t2_orbit_fst τ x c n
    rw [Foils.orbit_succ, Sys.orbit_succ]
    simp only [Foils.HaltsAt] at hn
    simp only [Sys.step, Sys.wt, Sys.res, ← hf, ← ih]
    change _ = _ + [2, -1].getD (((Foils.orbit τ (x, c) n).1 : ℤ) % 2).toNat 0
    rcases Nat.mod_two_eq_zero_or_one (Foils.orbit τ (x, c) n).1 with he | ho
    · rw [Foils.step_snd_even _ _ he]
      have : ((Foils.orbit τ (x, c) n).1 : ℤ) % 2 = 0 := by omega
      rw [this]; simp
    · rw [Foils.step_snd_odd _ _ ho]
      have hc : (Foils.orbit τ (x, c) n).2 ≠ 0 := fun hc => hn ⟨ho, hc⟩
      have : ((Foils.orbit τ (x, c) n).1 : ℤ) % 2 = 1 := by omega
      rw [this]; simp; omega

/-- **T2 and T3 agree.**  T2's member `τ` halts from `(x, c)` iff its embedding in the generic
family for Antihydra's data halts from `(x, c)`. -/
theorem antihydra_t2_halts_iff (τ : ℕ → Bool) (x c : ℕ) :
    Foils.Halts τ (x, c) ↔ antihydraSys.Halts (t2emb τ) ((x : ℤ), (c : ℤ)) := by
  classical
  constructor
  · intro h
    have hn : Foils.HaltsAt τ (x, c) (Nat.find h) := Nat.find_spec h
    have hy := t2_orbit_snd τ x c (Nat.find h) fun m hm => Nat.find_min h hm
    have hf := t2_orbit_fst τ x c (Nat.find h)
    refine ⟨Nat.find h + 1, ?_⟩
    rw [Sys.orbit_succ]
    simp only [Sys.step, Sys.wt, Sys.res, ← hf, ← hy]
    change _ + [2, -1].getD (((Foils.orbit τ (x, c) (Nat.find h)).1 : ℤ) % 2).toNat 0 < 0
    have : ((Foils.orbit τ (x, c) (Nat.find h)).1 : ℤ) % 2 = 1 := by have := hn.1; omega
    rw [this, hn.2]; simp
  · rintro ⟨n, hn⟩
    by_contra hnh
    have := t2_orbit_snd τ x c n fun m _ hm => hnh ⟨m, hm⟩
    omega

/-- T2's block members are the odd-supported block members of `F_{L,1}` (at values `≥ 0`). -/
theorem t2_member_emb (L : ℕ) (σ : ℕ → Bool) (x : ℤ) (hx : 0 ≤ x) :
    t2emb (Foils.member L σ) x =
      if x % 2 = 1 then member 2 L (fun b => if σ b.toNat then (1 : Fin 2) else 0) x else 0 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  have hb : ((n : ℤ) / ((2 * L : ℕ) : ℤ)).toNat = n / (2 * L) := by
    rw [← Int.natCast_div, Int.toNat_natCast]
  simp only [t2emb, member, blk, Foils.member, Foils.blk, Int.toNat_natCast, hb]
  by_cases h1 : (n : ℤ) % 2 = 1 <;> by_cases h2 : σ (n / (2 * L)) = true <;> simp [h1, h2]

/-- **T2 recovered in the schema.**  For every `L ≥ 1` and `K`, a T2 member agreeing with
Antihydra below block `K` halts from `(8, 0)` as a member of the generic family. -/
theorem antihydra_t2_recovered {L : ℕ} (hL : 1 ≤ L) (K : ℕ) :
    ∃ σ : ℕ → Bool, (∀ b < K, σ b = false) ∧
      antihydraSys.Halts (t2emb (Foils.member L σ)) (8, 0) := by
  obtain ⟨σ, hσ, h⟩ := Foils.exists_halting_member hL K
  exact ⟨σ, hσ, (antihydra_t2_halts_iff _ 8 0).mp h⟩

/-- #218 meets the window condition at defect `2`, not at defect `1` (`d_min = 2`). -/
theorem hydra218_window : hydra218Sys.Window 2 ∧ ¬ hydra218Sys.Window 1 := by
  unfold Sys.Window; decide

/-- #218's image grows from `x ≥ 1`. -/
theorem hydra218_esc (x : ℤ) (hx : (1, 3).1 ≤ x) : x + 1 ≤ hydra218Sys.img x := by
  unfold Sys.img Sys.res
  change x + 1 ≤ 4 * (x / 3) + [1, 2, 3].getD (x % 3).toNat 0
  have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [h] <;> omega

/-- **T3, target 3 (#218).**  Halting members are dense in `F_{L,2}` for #218. -/
theorem hydra218_halting_dense {L : ℕ} (hL : 1 ≤ L) (σ₀ : ℤ → Fin 3) (K : ℤ) :
    ∃ σ : ℤ → Fin 3, (∀ b < K, σ b = σ₀ b) ∧ hydra218Sys.Halts (member 3 L σ) (1, 3) :=
  hydra218Sys.halting_dense_of_window (by decide) (by decide) hL hydra218_window.1 σ₀ K (1, 3)
    hydra218_esc

/-! ## Bigfoot -/

/-- Bigfoot's reachable residues of `X mod 24`: `X ≢ 0 (mod 4)` (`X ≡ 3c`, `c ∈ {2, 3, 5}`). -/
def bigfootE (r : ℕ) : Bool := r % 4 != 0

/-- Residues of `X mod 24` with negative walk: `14, 17, 23`. -/
def bigfootNeg (r : ℕ) : Bool := decide (Dyn.bigfootW.getD r 0 < 0)

/-- The plain cyclic window condition needs defect `14` for Bigfoot. -/
theorem bigfoot_window : bigfootSys.Window 14 ∧ ¬ bigfootSys.Window 13 := by
  unfold Sys.Window; decide +kernel

/-- **The window condition on the reachable set needs defect `13`**: from reachable residues,
some choice `≤ 13` lands on a negative residue, and `12` does not suffice. -/
theorem bigfoot_resWindow :
    bigfootSys.ResDrain 13 bigfootE bigfootNeg (fun _ => 0) 1 ∧
      ¬ bigfootSys.ResDrain 12 bigfootE bigfootNeg (fun _ => 0) 1 := by
  unfold Sys.ResDrain Sys.resNext
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- Bigfoot's potential, found by value iteration on the residue game (`notes/35` §3). -/
def bigfootφ : List ℕ := [2, 6, 3, 1, 2, 2, 2, 6, 2, 3, 6, 2, 2, 5, 0, 3, 2, 0, 2, 5, 2, 1, 5, 0]

/-- **A drift certificate at defect `7`.**  With the trap the whole residue set, multiplier `3`
and potential `bigfootφ`, every residue and next digit admit a choice `≤ 7` along which
`3 a + φ` falls by one.  (Mean walk `≤ -1/3` per step under steering.) -/
theorem bigfoot_drift :
    bigfootSys.ResDrain 7 bigfootE (fun _ => true) (fun r => bigfootφ.getD r 0) 3 := by
  unfold Sys.ResDrain Sys.resNext; decide +kernel

/-- The all-zero map keeps `X ≢ 0 (mod 4)`. -/
theorem bigfoot_E_step (x : ℤ) (h : bigfootE (bigfootSys.res x) = true) :
    bigfootE (bigfootSys.res (bigfootSys.img x + ((0 : ℕ) : ℤ))) = true := by
  have hfin : ∀ r < 24, bigfootE r = true → ∀ t < 24,
      bigfootE (bigfootSys.resNext r t 0) = true := by
    unfold Sys.resNext; decide +kernel
  rw [bigfootSys.res_img_add (by decide)]
  exact hfin _ (bigfootSys.res_lt (by decide) x) h _ (bigfootSys.digit_lt (by decide) x)

theorem bigfoot_E_orbit {d : ℕ} (L : ℕ) (n : ℕ) :
    bigfootE (bigfootSys.res
      (bigfootSys.orbit (member 24 L (fun _ => (0 : Fin (d + 1)))) (10, 2) n).1) = true := by
  induction n with
  | zero => exact (by decide : bigfootE (bigfootSys.res 10) = true)
  | succ n ih =>
    rw [Sys.orbit_succ]
    exact bigfoot_E_step _ ih

/-- At reachable residues above `10`, Bigfoot's image grows. -/
theorem bigfoot_esc (x : ℤ) (hx : 10 ≤ x) (hE : bigfootE (bigfootSys.res x) = true) :
    x + 1 ≤ bigfootSys.img x := by
  have hfin : ∀ r < 24, bigfootE r = true →
      (10 ≤ r → (r : ℤ) + 1 ≤ Dyn.bigfootH.getD r 0) ∧ (r : ℤ) + 1 ≤ 8 + Dyn.bigfootH.getD r 0 := by
    decide +kernel
  have hr : bigfootSys.res x < 24 := bigfootSys.res_lt (by decide) x
  obtain ⟨h1, h2⟩ := hfin _ hr hE
  have hres : (bigfootSys.res x : ℤ) = x % 24 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  change x + 1 ≤ 32 * (x / 24) + Dyn.bigfootH.getD (bigfootSys.res x) 0
  rcases (show x / 24 = 0 ∨ 1 ≤ x / 24 by omega) with ht | ht
  · have := h1 (by omega)
    omega
  · omega

/-- **T3, target 3 (Bigfoot).**  For every `L ≥ 1` and `K`, some member of `F_{L,7}` agreeing
with Bigfoot on every block `< K` halts from `(10, 2)`. -/
theorem bigfoot_halting_member {L : ℕ} (hL : 1 ≤ L) (K : ℤ) :
    ∃ σ : ℤ → Fin 8, (∀ b < K, σ b = 0) ∧ bigfootSys.Halts (member 24 L σ) (10, 2) :=
  bigfootSys.halting_dense_of_resDrain (by decide) (by decide) hL bigfoot_drift (fun _ => 0) K
    (10, 2) (bigfoot_E_orbit L) (fun x hx hE => bigfoot_esc x hx hE)

end Collatz.HydraFoils
