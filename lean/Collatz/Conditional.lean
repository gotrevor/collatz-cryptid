import Collatz.Conjecture

/-!
# Theorems conditional on the Collatz conjecture

Each non-trivial theorem here takes `h : Conjecture` as a hypothesis.
-/

namespace Collatz

/-- The trivial cycle from `1`. Restated here for convenience. -/
theorem trivial_cycle : T^[3] 1 = 1 := T_iter_three_one

/-- Every forward iterate of `1` lies in the trivial cycle `{1, 4, 2}`. -/
private theorem iter_one_in_cycle (r : ℕ) :
    T^[r] 1 = 1 ∨ T^[r] 1 = 4 ∨ T^[r] 1 = 2 := by
  induction r with
  | zero => left; rfl
  | succ r ih =>
    rcases ih with h1 | h4 | h2
    · right; left; rw [Function.iterate_succ_apply', h1]; decide
    · right; right; rw [Function.iterate_succ_apply', h4]; decide
    · left; rw [Function.iterate_succ_apply', h2]; decide

/-- Under the Collatz conjecture, the only periodic points of `T` are
`{1, 2, 4}` (the trivial cycle).

Proof outline:
1. By the conjecture, `T^[j] n = 1` for some `j`.
2. From `T^[k] n = n`, every multiple `T^[m * k] n = n`.
3. Pick `m = j`: then `T^[j * k] n = n`, and using `T^[j] n = 1`,
   we get `n = T^[j * k - j] 1`.
4. Every iterate of `1` lies in `{1, 4, 2}` (by `iter_one_in_cycle`). -/
theorem no_nontrivial_cycle
    (h : Conjecture) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hcyc : T^[k] n = n) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨j, hj⟩ := h n hn
  -- Step 1: Every multiple of `k` is itself a period for `n`.
  have hperiod : ∀ m, T^[m * k] n = n := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.succ_mul, Function.iterate_add_apply, hcyc, ih]
  -- Step 2: `j ≤ j * k` since `1 ≤ k`.
  have hmk : j ≤ j * k := by nlinarith
  -- Step 3: `n = T^[j * k - j] 1`.
  have hn_iter : T^[j * k - j] 1 = n := by
    have heq : j * k - j + j = j * k := Nat.sub_add_cancel hmk
    calc T^[j * k - j] 1
        = T^[j * k - j] (T^[j] n) := by rw [hj]
      _ = T^[j * k - j + j] n := (Function.iterate_add_apply T _ j n).symm
      _ = T^[j * k] n := by rw [heq]
      _ = n := hperiod j
  -- Step 4: `T^[j*k - j] 1 ∈ {1, 4, 2}`.
  rcases iter_one_in_cycle (j * k - j) with h1 | h4 | h2
  · left; rw [← hn_iter]; exact h1
  · right; right; rw [← hn_iter]; exact h4
  · right; left; rw [← hn_iter]; exact h2

/-- The total stopping time `τ n` - the least `k` with `T^[k] n = 1`.
Conditional on `h : Conjecture`, this is a well-defined `ℕ`-valued function. -/
noncomputable def τ (h : Conjecture) (n : ℕ) (hn : 1 ≤ n) : ℕ :=
  Nat.find (h n hn)

/-- Iterating `T` exactly `τ n` times from `n` lands on `1`. -/
theorem T_iter_τ_eq_one
    (h : Conjecture) (n : ℕ) (hn : 1 ≤ n) :
    T^[τ h n hn] n = 1 :=
  Nat.find_spec (h n hn)

/-- `τ n` is minimal: any other `k` with `T^[k] n = 1` is at least `τ n`. -/
theorem τ_le_of_iter_eq_one
    (h : Conjecture) (n : ℕ) (hn : 1 ≤ n) {k : ℕ} (hk : T^[k] n = 1) :
    τ h n hn ≤ k :=
  Nat.find_min' (h n hn) hk

/-- Helper: every Collatz step halves the value at worst.
`T n ≥ n / 2` (with integer division). For even `n`, equality; for odd
`n`, `T n = 3n + 1` which dominates `n / 2`. -/
private theorem T_ge_div_two (n : ℕ) : n / 2 ≤ T n := by
  unfold T
  split_ifs with _h_even
  · exact le_refl _
  · omega

/-- Helper: iterating `T` for `k` steps decreases the value by at most a factor
of `2^k`. Hence `n / 2^k ≤ T^[k] n`. -/
private theorem iter_T_ge_div_pow (n k : ℕ) : n / 2^k ≤ T^[k] n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, ← Nat.div_div_eq_div_mul]
    calc n / 2^k / 2
        ≤ T^[k] n / 2 := Nat.div_le_div_right ih
      _ ≤ T (T^[k] n) := T_ge_div_two _

/-- Lower bound on total stopping time.

Each `T`-step changes the value by at most a factor of `1/2` (downwards).
Reaching `1` from `n ≥ 1` requires a value decrease of `log₂ n`, so
`τ n ≥ Nat.log2 n`. -/
theorem τ_ge_log2
    (h : Conjecture) (n : ℕ) (hn : 1 ≤ n) :
    Nat.log2 n ≤ τ h n hn := by
  set k := τ h n hn with _hk_def
  have htau : T^[k] n = 1 := T_iter_τ_eq_one h n hn
  have iter_ge : n / 2^k ≤ T^[k] n := iter_T_ge_div_pow n k
  rw [htau] at iter_ge
  -- iter_ge : n / 2^k ≤ 1
  have h2pk_pos : (0 : ℕ) < 2^k := Nat.two_pow_pos k
  have hdiv_lt : n / 2^k < 2 := by omega
  have h_n_lt_mul : n < 2 * 2^k := (Nat.div_lt_iff_lt_mul h2pk_pos).mp hdiv_lt
  have h_n_lt_pow : n < 2^(k + 1) := by rw [pow_succ]; linarith
  have h_n_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have h_log_lt : Nat.log2 n < k + 1 := (Nat.log2_lt h_n_ne).mpr h_n_lt_pow
  omega

end Collatz
