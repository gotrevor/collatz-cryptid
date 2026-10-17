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
* Instances: Antihydra, int-y1 #323, BB(2,5) Hydra (`q = 2`, `d = 1`), #218 (`d = 2`), Bigfoot.
* T2 agreement: T2's family is the odd-supported part of `F_{L,1}` for Antihydra's data, with the
  same halting predicate (`antihydra_t2_halts_iff`, `t2_member_emb`).
-/

namespace Collatz.HydraFoils

open Collatz.Bigfoot

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

end Sys

end Collatz.HydraFoils
