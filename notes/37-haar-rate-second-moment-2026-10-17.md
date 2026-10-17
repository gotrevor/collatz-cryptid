# 37. The Haar-mean digit rate: a spine reduction to one cross-energy bound (2026-10-17)

**Question** (Fornet, `antihydra-autoresearch/notes/stationary-cost-variational.md`): is the
Haar-mean optimal base-3/2 digit rate `a_*` below `1/3`?  Known: `0.3042471157… ≤ a_* ≤ 0.36661`.
notes/36 fits `a_* = c* = 0.30425` with a parameter-free branching-random-walk law.

**Update (2026-10-17, lap 2).**  Theorems A and B are now proved in Lean, so
`haarRate_le_eight_twentyfifths : CrossEnergyBounded candidate → a_* ≤ 8/25` has no `sorry`.
Lean-friendly proofs replaced the paper ones:

* Theorem A is the one-step recursion `M_{N+1} ≤ q M_N + r Λ_N^s` (`moment_succ_le`).  It comes
  from the first-digit split, subadditivity, `m ↦ 3m + c` permuting residues, and concave Jensen
  under the weights `Z_N`.
* Theorem B has four pieces:
  - a Chernoff bound through the tilted partition function: `Z_N l^{V_N} ≤ Z_N(p_d l^d)`
    (`Z_mul_pow_V_le`, `chernoff`);
  - a Young bound `x ≤ K + x^{1+s}/K^s` in place of Hölder (`mass_le`, `cheap_card`);
  - the block-commitment squeeze, with exactly uniform block starts (`sum_block`) and block-cost
    variance `≤ qL²` (`squeeze`);
  - subadditivity (`A_mul_le`, `A_add_le`).

**Outcome of this note.**  The kickoff's route (truncated second moment of `Z_N`) is replaced by
a sharper one: a *spine* (size-biased) decomposition of the density martingale of Fornet's iid
self-similar law `μ_p`.  It reduces `a_* ≤ p₁ + 2p₂` to a single hypothesis on one number per
depth: the adjacent cross-energy `Λ_N = ∫ ρ_N(y) ρ_N(y+1) dm(y)` must stay bounded.  That bound is
the precisely stated obstruction.  Numerically it holds with a flat profile (`Λ_N ≈ 0.547` for
Fornet's cost-8/25 candidate, `N ≤ 46`).  A known-false sibling system violates it, as it must.

Lean: `lean/Collatz/Antihydra/HaarDigitRate.lean` (commit `bf91f8c`).  Tags below:
**[Lean]** proved in Lean, **[Lean-sorry c%]** stated in Lean, proof on paper here,
**[paper c%]**, **[computed]**.

## 1. Setup

Legal step `x ↦ (3x+d)/2`, `d ∈ {0,1,2}`, `d ≡ x (2)`, cost `d`.  `V_N(x)` is the least cost of a
legal length-`N` word.  **[Lean]** `V`, `V_isLeast` (Bellman recursion = min over legal words),
`V_succ_even`/`V_succ_odd` (Fornet's recurrence), `V_add_pow_mul` (period `2^N`), `V_le`,
anchors `sumV_four : 2^4 A_4 = 31`, `sumV_eight : 2^8 A_8 = 936` (by `decide`).

For a digit law `p = (p₀,p₁,p₂)` let `D_j` be iid `p`, `X = −∑ D_j 2^j/3^{j+1} ∈ ℤ_2`,
`μ_p = law(X)`, `c(p) = p₁ + 2p₂`, and `X_k = −∑_i D_{k+i} 2^i/3^{i+1}`.  Then
`X_{k+1} = (3X_k + D_k)/2` and `X_k ≡ D_k (2)`: the digit sequence is a legal word from `X`
(Fornet IC1).  The dyadic density is `ρ_N(x) = 2^N μ_p(x + 2^N ℤ_2) = 2^N Z_N(x)` with
`Z_N(x) = ∑_{legal w, |w|=N} ∏ p_{w_j}` (Fornet PT1.2/IC1.2).  **[Lean]** `Z` (first-digit
recursion), `Z_add_pow_mul`, `rho`.  Fornet's IC1.1/AC4: `μ_p ≪ m ⇒ a_* ≤ c(p)`.

## 2. Theorem A: the spine moment bound  [Lean: `moment_bound`]

For `0 < s ≤ 1` put `q(s) = 2^s ∑_d p_d^{1+s}` (`spineRatio`) and
`r(s) = 2^s (p₀ p₂^s + p₂ p₀^s)` (`siblingWeight`).  For every `N`,

    ∫ ρ_N^{1+s} dm  ≤  q^N + r ∑_{j<N} q^j Λ_{N−1−j}^s,     Λ_n = ∫ ρ_n(y) ρ_n(y+1) dm(y).

*Proof.*  `∫ ρ_N^{1+s} dm = E_μ[ρ_N(X)^s]`.  Every legal `N`-word from `X` other than the spine
`D_0…D_{N−1}` first leaves it at some `j` with `X_j` even and digit `2 − D_j`; its next state is
`(3X_j + 2 − D_j)/2 = X_{j+1} + 1 − D_j`.  Hence the exact **spine identity**

    ρ_N(X) = 2^N ∏_{i<N} p_{D_i}
           + ∑_{j<N} 1[D_j even] 2^{j+1} (∏_{i<j} p_{D_i}) p_{2−D_j} ρ_{N−j−1}(X_{j+1} + 1 − D_j).

Apply `(a+b)^s ≤ a^s + b^s`.  The tail point `X_{j+1}` is a function of `D_{j+1}, D_{j+2}, …`,
so it is independent of `D_0…D_j` and has law `μ_p`.  The spine factors therefore average to
`q^j` times `2^s E[1[D even] p_{2−D}^s] = r`, and the first term to `q^N`.  For the sibling factor,
Jensen (concavity of `x^s` under the probability `μ_p`) gives
`E_μ[ρ_n(Y ± 1)^s] ≤ (E_μ ρ_n(Y ± 1))^s`, and
`E_μ ρ_n(Y+σ) = ∫ ρ_n(y+σ) ρ_n(y) dm = Λ_n` for `σ = ±1`, since `ρ_n(·+σ)` is depth-`n`
measurable and translation preserves `m`.  ∎

In finite form every step is a sum over `{0,1,2}^N` with product weights: the tail residue
`X_{j+1} mod 2^{N−j−1}` is the residue class of the tail word (Fornet OE1), so independence is
the product structure.  That is what `moment_bound` states.

`q(s) < 1` for small `s` iff `H(p) > log 2`: `d/ds log q |_{s=0} = log 2 − H(p)`.  For Fornet's
candidate `p = (18,6,1)/25`, `H(p) = 0.7078 > log 2` and `q(1/32) ≈ 0.99978`
(**[Lean]** `candidate_spineRatio_lt_one`, rational upper bounds on four 32nd roots).

**Corollary A′ [paper 90%].**  If `H(p) > log 2` and `sup_n Λ_n < ∞`, then `μ_p ≪ m` with a
density in `L^{1+s}` for every `s ∈ (0,1]` with `q(s) < 1`.  (Uniform `L^{1+s}` bound on the
density martingale `ρ_N` ⇒ uniform integrability ⇒ absolute continuity.)  For the candidate
this is Fornet's `L^{33/32}` target (IE2.3), reached by a different hypothesis.

## 3. The crux: the adjacent cross-energy  [Lean: `def CrossEnergyBounded`, open]

**(C1)** `sup_N Λ_N < ∞`.  Equivalent forms [paper, elementary]:

1. *Difference law.*  `Λ_N = 2^N P(E ≡ 1 mod 2^N)`, `E = X' − X = ∑_j e_j 2^j/3^{j+1}` with
   `e_j = D'_j − D_j` iid with law `π = p ∗ p̃`.  (C1) says the self-similar law of `E` has bounded
   dyadic density at the point `1`.  Its density at `0` is the diagonal `∫ ρ_N²`, which grows like
   `(2∑π(e)²)^N`-ish (at `θ = 1.3` the measured rate is `1.19`).
2. *Shift recursion.*  `λ_N(δ) = 2 ∑_{e ≡ δ (2)} π(e) λ_{N−1}((3δ − e)/2)`, `λ_0 ≡ 1`,
   `Λ_N = λ_N(1)`.  From odd `δ` the two successors `(3δ ∓ 1)/2` are consecutive integers.  From
   even `δ` the three successors `3δ/2 − 1, 3δ/2, 3δ/2 + 1` are consecutive integers.  `|δ|` never
   decreases; the only fixed points are `±1, ±2`.  `0` is never reached from `δ ≠ 0`.  Hence
   `v_2(δ_j) ≤ log₂|δ_j| ≤ j log₂(3/2) + 2` along every path.
3. *Feynman–Kac.*  `Λ_N = E[∏_{j<N} w(δ_j)]` for the chain `δ_{j+1} = (3δ_j − e_j)/2`, `δ_0 = 1`,
   with `e_j ∼ π` conditioned on `e_j ≡ δ_j (2)`, and `w = 2π(odd)` or `2π(even)` by the parity
   of `δ_j`.  The two weights average to `1`; (C1) says the chain from the integer `1` has no
   parity bias, in a summable sense.
4. *Fourier.*  `Λ_N = ∑_{ξ ∈ 2^{−N}ℤ/ℤ} |μ̂_p(ξ)|² e(ξ)`.  The terms sum to `∫ρ_N² → ∞` in absolute
   value, so (C1) is a cancellation statement, not a decay statement.

**Evidence [computed]** (`tools/sandbox/haar_digit_rate/cross_energy{,_p}.c`, `cross_dense.c`; the forward recursion keeps
`δ mod 2^{N−j}` exactly, sparse then dense).  The two programs agree at `N = 28` (`0.4276`).

| law | Λ_16 | Λ_24 | Λ_32 | Λ_40 | Λ_46/48 |
|---|---|---|---|---|---|
| candidate (18,6,1)/25 | 0.5507 | 0.5401 | 0.5504 | 0.5475 | 0.5463 |
| tilted θ = 1.24 (c = 0.3327) | 0.4696 | 0.4607 | 0.4685 | 0.4663 | |
| tilted θ = 1.30 (c = 0.3127) | | | 0.4330 | 0.4301 | 0.4296 |
| tilted θ* = 1.326 (c = c*) | 0.4190 | 0.4070 | 0.4176 | 0.4144 | |
| tilted θ = 2.0 | 0.1153 | 0.0887 | 0.0852 | 0.0827 | |

(Tilted: `p ∝ (1, e^{−θ}, e^{−2θ})`.)  The profile is flat at every law tried, including the
singular regime `θ > θ*`, where `Λ_N` decreases.  So (C1) looks like a property of the point `1`
("`1` is not special for the difference law"), uniform in `p`.

**Control (known-false sibling).** (`cross_control.py`)  Replace the multiplier `3` by `1` (step `x ↦ (x+d)/2`, uniform
`p`).  This gives `H = log 3 > log 2`, but `μ` is singular: its binary digits form a hidden Markov
process, not a fair coin.  The same recursion closes on `δ ∈ {−1,0,1}` with transfer matrix
`[[2/3, 4/9],[4/9, 4/9]]`, spectral radius `(10+√68)/18 ≈ 1.0137 > 1`.  So `Λ_N` diverges there,
as Theorem A requires.  The difference is structural: for multiplier `3`, `|δ|` grows, and `δ`
never returns to `0`; for multiplier `1` it shrinks onto `0`.

**Confidence that (C1) holds for the candidate: ~75%.**

## 4. Theorem B: from the moment bound to `a_* ≤ c(p)`  [Lean: `haarRate_le_of_crossEnergyBounded`]

Assume `q(s) < 1` and (C1), so `M := sup_N ∫ρ_N^{1+s} dm < ∞` by Theorem A.  A self-contained
argument (Fornet IC1.1 is the alternative citation):

1. *Cheap set has Haar mass.*  Let `B_N = {r mod 2^N : V_N(r) ≤ (c+ε)N}`.  For `w ∼ p^{⊗N}` the
   word is legal from its residue `r_w`, so `μ_p(B_N) ≥ P(cost(w) ≤ (c+ε)N) ≥ 1 − 1/(ε²N)`
   (Chebyshev).  Hölder: `μ(B) ≤ m(B)^{s/(1+s)} M^{1/(1+s)}`, so `m(B_N) ≥ κ > 0` for large `N`.
2. *Concentration from above* (Fornet OE2/AC1, Chebyshev version).  For a block length `L` with
   `A_L/L ≤ a_* + η`, committing to an optimal `L`-word at each block start makes the
   block-start residues iid uniform (the endpoint is `y + 3^L U` with `U` Haar).  Hence
   `m(V_N > (a_* + 2η)N + L) ≤ 1/(4qη²)` with `q = ⌊N/L⌋`.
3. *Squeeze.*  With `X_N = V_N/N ∈ [0,1]` and `E X_N = A_N/N ≥ a_*`:
   `E(a_* − X_N)^+ ≤ E(X_N − a_*)^+ ≤ 2η + o(1)`, so `m(X_N ≤ a_* − δ) → 0` as `η → 0`.
   Steps 1 and 3 together force `c + ε ≥ a_* − δ`.  Since `ε, δ` are arbitrary, `a_* ≤ c`.
   Then `A_N/N → a_*` (Fekete) gives the finite form
   `∑_{x<2^N} V_N(x) ≤ (c+ε) N 2^N` for all large `N`.  ∎

**Corollaries.**
* **[Lean]** `haarRate_le_eight_twentyfifths`: (C1) for the candidate
  ⇒ `a_* ≤ 8/25 < 1/3`.  That refutes Fornet's mean inequality `a_* ≥ 1/3`.
* [paper 85%] (C1) for the tilted law at one `θ ∈ (1.2382, θ*)` ⇒ `a_* < 1/3`.  (C1) for all
  `θ < θ*` ⇒ `a_* = c*`, the notes/36 prediction: `c(θ) ↓ c*` as `θ ↑ θ*`, and `a_* ≥ c*` is OE3.

## 5. Why not the truncated second moment  [paper 80%]

Expanding `E[Z_N²]` by the divergence depth `j` of two words gives `S_N = ∑_j (prefix) × K(1)`.
Here `K(1)` is the cross-correlation of the two child subtrees, whose roots differ by exactly `1`.
In this exact form it is `Λ` at the tilt `θ`.  The barrier truncation controls the prefix sum (the
diagonal growth `1.19^N`).  The pair term is still the shift-1 cross energy, now *cost-resolved*:
pairs of continuation words with prescribed costs and residues differing by `1`.  Bounding it by
`C ×` the independent count is a local-limit refinement of (C1).  With Chernoff it loses
polynomial factors, which a barrier second moment cannot absorb.  So the barrier route needs
strictly more than (C1), and the spine route needs exactly (C1).

## 6. Toward (C1)  [direction, not results]

* Any proof must use the arithmetic of the integers visited.  An adversary who chooses the
  valuation of each new even shift, subject only to `v_2(δ_j) ≤ j log₂(3/2) + 2`, makes the
  weighted sum grow like `γ^{N}` up to `N^{O(1)}` (one long zero-run per valuation creation;
  `γ = 2π(0) = 1.19` at `θ = 1.3`).  Potentials built from valuation and size alone cannot close.
* The integer `δ_j = (3/2)^j − ½∑_{i<j} e_i (3/2)^{j−1−i}` mixes the real and 2-adic structure.
  Its real profile is a ratio-`2/3` self-similar law with entropy `H(π) ≈ 1.16 ≫ log(3/2)`, and
  `H(π) > log 3`, the solenoid volume rate.  The likely mechanism for (C1) is equidistribution of
  `δ_j mod 2^k` for `k ≤ j log₂(3/2)`, driven by the random late digits.  That is the next
  concrete target.
* Fornet's IE/HE/IO criteria use Hellinger (`q = 1`) or `L^q` refinement energies of the same
  adjacent pair `μ, τμ`; IO1 proves their common mass is positive.  (C1) is the `q = 2` cross
  energy, and the spine converts it to AC without needing `∫ρ²` bounded.  A grep of Fornet's
  `notes/` and `LOG.md` for spine, size-biased and cross/mutual-energy arguments found none.
  Discord and the wider literature were not searched.

## 7. Not claimed

No unconditional bound on `a_*` is proved: everything is conditional on (C1).  Nothing here
touches the fixed-integer rate, global (G), or Antihydra's orbit.  Theorems A and B are proved
in Lean (no `sorry`); (C1) is the single open hypothesis of the headline.

Build: `lake build Collatz.Antihydra.HaarDigitRate`.

## 8. Lap 3: the minimal crux and how hard it is  [Lean + paper]

**Minimal hypothesis [Lean].**  `MomentBounded p s` (`sup_N ∫ρ_N^{1+s} < ∞`) is all Theorem B
needs (`haarRate_le_of_momentBounded`, `haarRate_le_eight_twentyfifths_of_momentBounded`).  For
`q(s) < 1` it is equivalent to bounded shift moments `K^±_N = E_μ[ρ_N(Y±1)^s]`
(`momentBounded_iff_shiftMomentBounded`).  Forward: `K ≤ M` by weighted AM–GM.  Backward:
`moment_succ_le_shift`, which is Theorem A before Jensen.  (C1) implies it
(`momentBounded_of_crossEnergyBounded`).

**(C1) is AC plus a Diophantine condition [paper 80%].**  `ρ` has singularities of strength
`|y − T_w(0)|^{−log₂(2p₀)} = |·|^{−0.526}` at the dense set of points `T_w(0)`.  That is
compatible with `L^{1+s}`, but `∫ρ(y)ρ(y+1)` diverges if two singularities sit at distance exactly
`1`.  This never happens exactly: the δ-chain never reaches 0.  (C1) asks that near-alignments be
rare in the weighted sense, so (C1) is strictly stronger than `MomentBounded`.  It is attractive
because it is linear.

**Hardness [paper 75%].**  `MomentBounded candidate (1/32)` gives `μ_p ≪ m` for a 2-adic
self-similar measure with three maps `x ↦ (2x−d)/3`.  Its similarity dimension is
`H/log 2 = 1.021`.  It has no exact overlaps, and level-`n` atoms are `≥ 3^{−n}/2` apart (product
formula).  This is the 2-adic analogue of absolute continuity of a self-similar measure with an
algebraic contraction (for example, the real λ = 2/3).  That problem is open.  Varjú/Kittle need a
dimension excess far beyond 2%, and Garsia's argument works here only for uniform `p`, where the
density is `≤ 4`, at cost 1.  Every law of cost `< 1/3` has `2∑p_d² > 1`, so the `L²` regime is
unavailable.  In the Galton–Watson model, with independent sibling subtrees, the criterion is
exactly Biggins' `H > log 2`.  The only obstruction is the dependence of the subtrees at `y`
and `y+1`.

**Fourier/odd–even recursion (direction).**  `F_n(θ) = ∑_t m_n(t)e(tθ)` (forward measure on the
integers) satisfies `F_{n+1}(θ) = 4π(1)cos(πθ)·O_n(3θ/2) + (2π(0) + 4π(2)cos 2πθ)·E_n(3θ/2)`,
where `O_n` and `E_n` are the odd and even parts.  The fair coin at odd δ kills the parity
character in one step (the `cos(π/2) = 0` term).  Also `Λ_{n+k} = Λ_n + ∑_{ξ∈2^{−k}ℤ∖0}
|μ̂(ξ)|² F_n(−ξ)`.  **Sufficient condition (S):** `max_{ξ ∈ 2^{−k}ℤ∖0}|F_n(ξ)| ≤ C Λ_n e^{−cn}`
for `k = αn` with `c > α log γ`, where `γ ≈ 1.155` is the diagonal growth.  (S) implies (C1).
Numerics: `T_k` (`tmp/mdp/tk`, `k ≤ 30`) has `|T_k|/absmass ≈ 1.7e−4` at `k = 30`, far below
`γ^{−30} = 0.013`.

## 9. Lap 4: the crux as an integer recursion and a parity sum  [Lean + computed]

**Residue-free form [Lean].**  `lean/Collatz/Antihydra/HaarShift.lean`.  `crossShift p N δ =
∫ρ_N(y)ρ_N(y+δ)` obeys `C_{N+1}(2u+1) = 2π(1)(C_N(3u+1)+C_N(3u+2))`,
`C_{N+1}(2u+2) = 2π(0)C_N(3u+3) + 2π(2)(C_N(3u+2)+C_N(3u+4))` and
`C_{N+1}(0) = 2π(0)C_N(0) + 4π(2)C_N(1)`, with `π = (∑p², p₁(p₀+p₂), p₀p₂)`
(`crossShift_succ_odd/even/zero`).  Hence `crossEnergy p N = shiftKernel p N 1`
(`crossEnergy_eq_shiftKernel`), where `shiftKernel` is defined by the recursion alone.  Anchor:
`crossEnergy_candidate_one` (`Λ₁ = 456/625`).

**Parity form [Lean].**  With `𝒦` the one-step operator (`kernelOp`), `𝒦1 = 1 + βχ`, where
`χ(δ) = (−1)^δ` and `β = (p₀−p₁+p₂)²` (`kernelOp_one`).  So
`Λ_N = 1 + β∑_{n<N} P_n` with `P_n = (𝒦^nχ)(1)` (`crossEnergy_eq_one_add_sum`).  The crux is
exactly a bound on the partial sums of `P_n` (`crossEnergyBounded_iff_parity`).  The odd parents
cancel: `𝒦χ = (2π(0)−4π(2))χ₄` (`kernelOp_parity`, `parityCorr_succ`).  Absolute
summability `ParityCorrSummable` (open) is sufficient (`crossEnergyBounded_of_paritySummable`).

**Numerics for (S) [computed]** (`tools/sandbox/haar_digit_rate/{parity_corr,fwd_tv,
fwd_fourier}.c`, forward measure `m_n` from `δ = 1`, `n ≤ 44`).
* `P_n/Λ_n`: `8e−2` (n=10), `1.5e−2` (20), `1.8e−2` (30), `3e−3` (40), `−4.6e−3` (42).  The
  signs oscillate and the decay is slow, about `e^{−0.07n}`.  The identity
  `Λ_{n+1} − Λ_n = βP_n` matches the program to all printed digits.
* Fourier form of (S): at fixed `k`, `max_{ξ∈2^{−k}ℤ∖0}|F_n(ξ)|/Λ_n` decays at rate about
  `0.15` (k=8) and `0.06` (k=12), with plateaus.  So (S) is plausible only for `α ≲ 0.2`.  It is
  marginal at `α ≈ 0.3`.
* Total variation from uniform mod `2^k`: `TV_{n,k} ≈ 0.18·exp(−0.10n + 0.33k)`
  (`16 ≤ n ≤ 44`, `k ≤ 20`).  `Λ_{n+k} − Λ_n = ∑_r (C_k(r) − 1)(h_n(r) − Λ_n2^{−k})` gives
  `|Λ_{n+k} − Λ_n| ≤ C_k(0)·Λ_n·TV_{n,k}`.  With `C_k(0) ≈ γ^k`, `γ = 2∑p² = 1.155`, the TV
  form of (S) closes for `α < 0.21`.  In Lean: `crossEnergy_add_sub_le` (with `crossEnergy_add_eq`, `sum_crossShift`).  The `k = 1`
  case alone (`ParityCorrSummable`) already suffices, so larger `k` adds nothing logically.

**No mechanism [paper 75%].**  Every reformulation reached so far (Fourier `T_k`, the dual
transfer operator `t ↦ (3t+ε)/2` on `ℝ/ℤ`, the real lattice form, renewal over zero runs) is
the same object.  Each one needs exponential equidistribution of the weighted integer chain
`δ ↦ (3δ+e)/2` modulo `2^k`.  The forward measure carries a forced `3`-adic pattern
(`m'(3u) = 2π(0)m(2u)`, `m'(3u+1) = 2π(1)m(2u+1) + 2π(2)m(2u)`, …).  So it is never smooth at
unit scale.  Parity decorrelation needs the CRT heuristic: the `2`-adic, `3`-adic and real
coordinates are asymptotically independent.  Here are four reformulations, and what each needs:
* **Real lattice form** (paper, elementary).  `Λ_N = 2^N P(R_N ∈ −3 + 3(2/3)^Nℤ)` with
  `R_N = ∑_{j<N} e_j(2/3)^j`, `e_j` iid `π`.  This is a finest-scale lattice local limit
  statement.  Heavy atoms (short representations) are provably avoided below complexity `0.63N`
  (the chain never hits `0`).  The heuristic count then gives `Λ = O(1)`, but nothing controls
  the arithmetic correlations above that.
* **Known AC theorems do not reach it.**  Real-line AC theorems (Varjú, Kittle, Kittle–Varjú)
  need entropy/contraction excess far beyond the `2%` (candidate) or `≤ 5%` (any law of cost
  `≤ 1/3`) available here.  The excess is intrinsically small because `h(1/3) − log 2 ≈ 0.037`.
* **`L^q`-dimension route.**  Shmerkin's `L^q`-dimension theorem, transported to `ℤ_2`, would
  give `M_N = e^{o(N)}`, hence only `m(B_N) ≥ e^{−o(N)}`.  Turning that into `a_* ≤ c` needs
  exponential lower-tail concentration of `V_N` under Haar, which is open and not easier.
* **Literature.**  A web search for `p`-adic/`2`-adic self-similar AC found nothing.

**Obstruction, precisely.**  `a_* ≤ 8/25` follows from bounded partial sums of
`P_n = ∑_δ m_n(δ)(−1)^δ` for one explicit nonnegative integer chain.  The bound is equivalent
to that statement (`crossEnergyBounded_iff_parity`).  It is the `2`-adic analogue of a
finest-scale smoothness question for a self-similar measure with contraction `2/3`, and no
proof technique is known.
