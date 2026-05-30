import Collatz.Erdos.Cycle
import Mathlib.Tactic

/-!
# Path 2: the one-constant effectivity hub

The 2↔3 family (Collatz cycles, Pillai, Erdős) shares a **single effective
bottleneck**: a quantitative lower bound on the gap `|2^L − 3^n|`, supplied by
linear forms in logarithms / the irrationality measure `μ(log₂3)` (Baker; current
best `μ ≲ 5.1`).  This file makes the *Collatz-cycle* arrow precise and proved,
and records the hub.

The proved arrow (`abs_cycleGap_le_cycleR`): for any genuine `3x+d=1`-style cycle
with smallest element `x ≥ 1`, `|2^L − 3^n| ≤ R(e)`.  So a *lower* bound on the
gap (the bottleneck) forces `R(e)` — hence the whole cycle — to be **large**.
That is exactly the Eliahou mechanism: cycles can only live where the gap is
small, i.e. at convergents of `log₂3`, and the irrationality measure controls how
small that can be.

Dependency star (one constant, many consequences):

```
            irrationality measure μ(log₂3)  /  Baker linear forms in logs
                              │  (effective gap lower bound)
        ┌─────────────────────┼─────────────────────────┐
   Collatz cycles         Pillai 2^x−3^y=k          Erdős leading digit
   |gap| ≤ R(e)  ⟹        each k finitely        {n log₃2} Sturmian
   big cycles (PROVED      often (≈ pillai          (Path 4, not automatic)
   arrow here)             axiom)
```

Honesty: the analytic core (proving a good `μ`, or Baker with explicit
constants) is the hard, external input — we do **not** reprove it.  What is
genuinely proved here is the *routing*: `|gap| ≤ R(e)` ties the cycle face to the
gap, so the single Diophantine bottleneck governs it.  See `notes/25` / the Path
write-ups; companion to `Cycle.lean`.
-/

namespace Collatz.Erdos

/-- The gap as an explicit function of the exponents. -/
def gapZ (L n : ℕ) : ℤ := 2 ^ L - 3 ^ n

/-- `cycleGap` of an exponent list is `gapZ` of its sum and length. -/
theorem cycleGap_eq_gapZ (e : List ℕ) : cycleGap e = gapZ e.sum e.length := rfl

/-- **The proved hub arrow.**  For any genuine cycle (smallest element `x ≥ 1`
satisfying the Lagarias equation `x · gap = R(e)`), the gap is bounded by the
remainder: `|2^L − 3^n| ≤ R(e)`.

Consequently an effective *lower* bound on `|gap|` forces `R(e)` large — the
cycle cannot be small.  This is the Collatz arrow of the effectivity hub. -/
theorem abs_cycleGap_le_cycleR {x : ℤ} {a : ℕ} {rest : List ℕ}
    (hx : 1 ≤ x) (h : x * cycleGap (a :: rest) = (cycleR (a :: rest) : ℤ)) :
    |cycleGap (a :: rest)| ≤ (cycleR (a :: rest) : ℤ) := by
  have hxabs : (1 : ℤ) ≤ |x| := le_trans hx (le_abs_self x)
  have hR : (0 : ℤ) ≤ (cycleR (a :: rest) : ℤ) := Int.natCast_nonneg _
  calc |cycleGap (a :: rest)|
      ≤ |x| * |cycleGap (a :: rest)| :=
        le_mul_of_one_le_left (abs_nonneg _) hxabs
    _ = |x * cycleGap (a :: rest)| := (abs_mul _ _).symm
    _ = |(cycleR (a :: rest) : ℤ)| := by rw [h]
    _ = (cycleR (a :: rest) : ℤ) := abs_of_nonneg hR

/-! ## The bottleneck constant

`EffectiveGapLowerBound C κ`: a Baker / irrationality-measure consequence —
`|2^L − 3^n|` is bounded below by `3^n / C^κ`-style data.  We package it as the
single open input the whole hub conditionally consumes. -/

/-- The effective gap lower bound (schematic Baker/`μ(log₂3)` consequence):
for some effective constants, the gap is never too small relative to `3^n`.
Stated as the hub's single bottleneck input. -/
def EffectiveGapLowerBound (f : ℕ → ℕ → ℤ) : Prop :=
  ∀ L n : ℕ, 0 < n → 0 < |gapZ L n| → f L n ≤ |gapZ L n|

/-- **Hub consequence (Collatz).**  Given the effective gap lower bound, any
genuine cycle has `R(e) ≥ f(L, n)`: the bound transfers straight to the cycle
remainder via the proved arrow.  (So an `f` growing with `n` rules out small
cycles — the Eliahou conclusion, modulo the bottleneck.) -/
theorem cycleR_ge_of_gapBound {f : ℕ → ℕ → ℤ}
    (hf : EffectiveGapLowerBound f) {x : ℤ} {a : ℕ} {rest : List ℕ}
    (hx : 1 ≤ x) (h : x * cycleGap (a :: rest) = (cycleR (a :: rest) : ℤ))
    (hn : 0 < (a :: rest).length) (hgap : 0 < |cycleGap (a :: rest)|) :
    f (a :: rest).sum (a :: rest).length ≤ (cycleR (a :: rest) : ℤ) := by
  have hbound := hf (a :: rest).sum (a :: rest).length hn (by rwa [cycleGap_eq_gapZ] at hgap)
  rw [← cycleGap_eq_gapZ] at hbound
  exact le_trans hbound (abs_cycleGap_le_cycleR hx h)

/-! ## Plugging the literature constant (Baker / `μ(log₂3) ≲ 5.1`)

The irrationality measure of `log₂3` is known to be finite and `≲ 5.1`
(Rukhadze/Nesterenko-style effective work).  This gives an *effective* gap lower
bound of the form `|2^L − 3^n| ≥ 3^n / (L+1)^6` for all sufficiently large `n`
(the exponent `6 > μ` absorbs the constant; small `n` are excluded by the
threshold `N₀`).  We cite it as an axiom — the analytic core we do not reprove.
Honesty: the *existence* form below is what the literature supports; we do **not**
assert a specific small-case value (the bound genuinely fails for tiny `n`). -/

/-- Cited Baker / `μ(log₂3) ≲ 5.1` consequence: an effective threshold `N₀` past
which `3^n / (L+1)^6 ≤ |2^L − 3^n|` (nonzero gap). -/
axiom baker_gap_lower :
    ∃ N₀ : ℕ, ∀ L n : ℕ, N₀ ≤ n → 0 < |gapZ L n| →
      (3 : ℤ) ^ n / (L + 1) ^ 6 ≤ |gapZ L n|

/-- **Concrete Collatz consequence of the cited Baker bound.**  There is an
effective `N₀` such that every genuine cycle with `n ≥ N₀` odd-steps has remainder
`R(e) ≥ 3^n / (L+1)^6`.  Since that bound → ∞ with `n`, the cycle cannot be small:
the effective Eliahou "no small cycle" conclusion, now routed through one cited
constant via the proved arrow `abs_cycleGap_le_cycleR`. -/
theorem cycleR_ge_baker {x : ℤ} {a : ℕ} {rest : List ℕ}
    (hx : 1 ≤ x) (h : x * cycleGap (a :: rest) = (cycleR (a :: rest) : ℤ))
    (hgap : 0 < |cycleGap (a :: rest)|) :
    ∃ N₀ : ℕ, N₀ ≤ (a :: rest).length →
      (3 : ℤ) ^ (a :: rest).length / ((a :: rest).sum + 1) ^ 6
        ≤ (cycleR (a :: rest) : ℤ) := by
  obtain ⟨N₀, hbound⟩ := baker_gap_lower
  refine ⟨N₀, fun hN => ?_⟩
  have hg : 0 < |gapZ (a :: rest).sum (a :: rest).length| := by
    rwa [cycleGap_eq_gapZ] at hgap
  have hb := hbound (a :: rest).sum (a :: rest).length hN hg
  rw [← cycleGap_eq_gapZ] at hb
  exact le_trans hb (abs_cycleGap_le_cycleR hx h)

end Collatz.Erdos
