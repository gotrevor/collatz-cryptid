import Collatz.Erdos.Syracuse

/-!
# The Lagarias identity for Syracuse iterates

For any natural `m` and any `k ≥ 0`, iterating the Syracuse step
`σ(n) = (3n+1) / 2^{v₂(3n+1)}` produces the **unconditional** identity

  2^{σ_k(m)} · σ^k(m)  =  3^k · m  +  S_k(m)

where
  σ_k(m)  =  Σ_{i=0}^{k-1} v₂(3·σ^i(m) + 1)        (cumulative halvings)
  S_k(m)  =  3 · S_{k-1}(m) + 2^{σ_{k-1}(m)},  S_0 = 0.

This is the bridge between Collatz parity vectors and the base-3
expansion of powers of 2 sketched in `notes/22-erdos-collatz.md`.

Note: the identity is **unconditional** — it does *not* require the
trajectory to reach 1.  Specializing to `σ^k(m) = 1` recovers the
familiar form `2^{σ_k} = 3^k · m + S_k`.
-/

namespace Collatz.Erdos

/-- Cumulative halvings sum after `k` Syracuse steps starting from `m`. -/
def syracuseSigma (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => syracuseSigma m k + syracuseExp (syracuse^[k] m)

/-- The Lagarias `S` coefficient.
`S_k` satisfies `2^{σ_k(m)} · σ^k(m) = 3^k · m + S_k(m)`. -/
def lagariasS (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * lagariasS m k + 2 ^ syracuseSigma m k

/-- For any positive `m`, the 2-adic factorization computed by
`twosCount`/`stripTwos` recombines to `m`. -/
theorem twosCount_stripTwos (m : ℕ) (hm : 0 < m) :
    2 ^ twosCount m * stripTwos m = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hmod : 0 < m ∧ m % 2 = 0
    · rw [twosCount_step hmod, stripTwos_step hmod]
      have hlt : m / 2 < m := Nat.div_lt_self hm (by decide)
      have h2 : 2 ≤ m := by omega
      have hpos : 0 < m / 2 := Nat.div_pos h2 (by decide)
      have ihm := ih (m / 2) hlt hpos
      have hmul : (2 : ℕ) * (m / 2) = m := by
        have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod.2)
        omega
      calc 2 ^ (1 + twosCount (m / 2)) * stripTwos (m / 2)
          = 2 * (2 ^ twosCount (m / 2) * stripTwos (m / 2)) := by ring
        _ = 2 * (m / 2) := by rw [ihm]
        _ = m := hmul
    · rw [twosCount_stop hmod, stripTwos_stop hmod]
      simp

/-- The defining identity of one Syracuse step: `2^{e(n)} · σ(n) = 3n + 1`. -/
theorem syracuse_eq (n : ℕ) :
    2 ^ syracuseExp n * syracuse n = 3 * n + 1 := by
  unfold syracuse syracuseExp
  exact twosCount_stripTwos (3 * n + 1) (by omega)

/-- **Lagarias identity** for Syracuse iterates (unconditional). -/
theorem syracuse_lagarias (m k : ℕ) :
    2 ^ syracuseSigma m k * syracuse^[k] m = 3 ^ k * m + lagariasS m k := by
  induction k with
  | zero => simp [syracuseSigma, lagariasS]
  | succ k ih =>
    set m_k := syracuse^[k] m with hmk
    have hstep : syracuse^[k + 1] m = syracuse m_k :=
      Function.iterate_succ_apply' syracuse k m
    have hsyr : 2 ^ syracuseExp m_k * syracuse m_k = 3 * m_k + 1 :=
      syracuse_eq m_k
    have hsigma : syracuseSigma m (k + 1) = syracuseSigma m k + syracuseExp m_k := by
      simp [syracuseSigma, hmk]
    have hS : lagariasS m (k + 1) = 3 * lagariasS m k + 2 ^ syracuseSigma m k := by
      simp [lagariasS]
    have hpow : (2 : ℕ) ^ (syracuseSigma m k + syracuseExp m_k) * syracuse m_k
              = 2 ^ syracuseSigma m k * (2 ^ syracuseExp m_k * syracuse m_k) := by
      rw [pow_add]; ring
    calc 2 ^ syracuseSigma m (k + 1) * syracuse^[k + 1] m
        = 2 ^ (syracuseSigma m k + syracuseExp m_k) * syracuse m_k := by
            rw [hsigma, hstep]
      _ = 2 ^ syracuseSigma m k * (2 ^ syracuseExp m_k * syracuse m_k) := hpow
      _ = 2 ^ syracuseSigma m k * (3 * m_k + 1) := by rw [hsyr]
      _ = 3 * (2 ^ syracuseSigma m k * m_k) + 2 ^ syracuseSigma m k := by ring
      _ = 3 * (3 ^ k * m + lagariasS m k) + 2 ^ syracuseSigma m k := by rw [ih]
      _ = 3 ^ (k + 1) * m + (3 * lagariasS m k + 2 ^ syracuseSigma m k) := by ring
      _ = 3 ^ (k + 1) * m + lagariasS m (k + 1) := by rw [hS]

/-- Specialization: if `m` reaches `1` in `k` Syracuse steps, then
`2^{σ_k(m)} = 3^k · m + S_k(m)`. -/
theorem syracuse_lagarias_of_reach_one {m k : ℕ} (h : syracuse^[k] m = 1) :
    2 ^ syracuseSigma m k = 3 ^ k * m + lagariasS m k := by
  have := syracuse_lagarias m k
  rw [h, mul_one] at this
  exact this

/-- **Low-`k`-digit bridge**: the first `k` base-3 digits of
`2^{σ_k(m)} · σ^k(m)` agree with the first `k` base-3 digits of `S_k(m)`. -/
theorem syracuse_lagarias_mod (m k : ℕ) :
    (2 ^ syracuseSigma m k * syracuse^[k] m) % 3 ^ k = lagariasS m k % 3 ^ k := by
  rw [syracuse_lagarias m k, Nat.add_comm, Nat.add_mul_mod_self_left]

/-- Specialization at reach-1: `2^{σ_k(m)} mod 3^k = S_k(m) mod 3^k`.
This is the "low-`k`-digit bridge" between Collatz parity vectors and
the base-3 expansion of powers of 2. -/
theorem lagarias_two_pow_mod_three_pow {m k : ℕ} (h : syracuse^[k] m = 1) :
    2 ^ syracuseSigma m k % 3 ^ k = lagariasS m k % 3 ^ k := by
  have := syracuse_lagarias_mod m k
  rw [h, mul_one] at this
  exact this

/-! ## Verifications on the Erdős-exceptional witnesses

The two non-trivial Erdős exceptions `N ∈ {2, 8}` correspond to `m = 1`
and `m = 85` respectively (one Syracuse step each).  Lagarias's identity
then reproduces the base-3 structure of `2^N`.
-/

/-- For `m = 1`: σ(1) = 1, σ_1 = 2, S_1 = 1, giving `2^2 = 3·1 + 1`. -/
example : 2 ^ syracuseSigma 1 1 = 3 ^ 1 * 1 + lagariasS 1 1 := by
  apply syracuse_lagarias_of_reach_one
  exact syracuse_one

/-- For `m = 85`: σ(85) = 1, σ_1 = 8, S_1 = 1, giving `2^8 = 3·85 + 1`. -/
example : 2 ^ syracuseSigma 85 1 = 3 ^ 1 * 85 + lagariasS 85 1 := by
  apply syracuse_lagarias_of_reach_one
  change stripTwos (3 * 85 + 1) = 1
  -- 3·85+1 = 256 = 2^8; strip 8 factors of 2 to reach 1
  rw [stripTwos_step (by decide), stripTwos_step (by decide),
      stripTwos_step (by decide), stripTwos_step (by decide),
      stripTwos_step (by decide), stripTwos_step (by decide),
      stripTwos_step (by decide), stripTwos_step (by decide),
      stripTwos_stop (by decide)]

end Collatz.Erdos
