# 36. The Haar-mean base-3/2 digit rate looks like a branching random walk (2026-10-17)

**Context.**  `notes/33` §3 names mfornet's global digit bound (G) (`antihydra-autoresearch`
`notes/digit-sum-route.md` §2: `S(n) ≥ (1/3) log_{3/2} n − C` for every `n`) as the one live
Antihydra route that passes the Foils gate.  Fornet's inventory reduces (G) to slopes of optimal
canonical-digit cost: the root slope `γ = liminf V_N(1)/N` (`global-digit-slope.md`) and the Haar
mean `a_* = lim A_N/N`, `A_N = ∫ V_N dm` over `Z_2` (`stationary-cost-variational.md`), with
rigorous bounds `0.3042471157… ≤ a_* ≤ 0.36661`.  The lower bound is the first-moment (counting)
threshold `c*` (`optimal-extension-mean.md` OE2).  Whether `a_* ≥ 1/3` is recorded there as open.  Fornet also has a *conditional* route below 1/3: absolute continuity of a specified biased
self-similar law would give `a_* ≤ 8/25` (`stationary-cost-variational.md` AC4, via
`iid-affinity-energy.md` HE2.4 and `iid-refinement-energy.md` IE2.3); that hypothesis is unproved.

Recurrence (Fornet's AC/PT1): legal step `x ↦ (3x + d)/2`, `d ≡ x (mod 2)`, cost `d`;
`V_{N+1}(2m) = min(V_N(3m), 2 + V_N(3m+1))`, `V_{N+1}(2m+1) = 1 + V_N(3m+2)`, arguments mod `2^N`.

## 1. Exact means to N = 33 [computed]

`tools/sandbox/haar_digit_rate/bellman.c` evaluates `2^N A_N = Σ_{x mod 2^N} V_N(x)` exactly.
Control: `N = 24` gives `160192352`, Fornet's value (`160192352/(24·2^24)`).  Output
`bellman33.txt`.  `A_33/33 = 0.382816`; increments `ΔA_N = A_N − A_{N−1}`: `0.34908` (24),
`0.34144` (30), `0.33793` (33), falling about `0.0012` per step with no visible deceleration.

## 2. A parameter-free branching-random-walk prediction fits [computed, ~85%]

Under Haar measure each node's parity is a fair bit, so the legal-word tree is a branching walk with
mean offspring generating function `(1 + t + t²)/2` (even node: costs 0, 2; odd node: cost 1).
For an iid branching random walk, Biggins' theorem makes the minimal speed equal to the counting
threshold, and Aïdékon's theorem gives `E[min_N] = c* N + (3/(2θ*)) ln N + O(1)`.  Here
`θ* = 1.3261624301`, `c* = 0.3042471158`, `3/(2θ*) = 1.1311`.

The prediction `ΔA_N ≈ c* + 1.1311/N` has no free parameter.  Residual `ΔA_N − prediction`:
`−0.0105` (N=14), `−0.0029` (20), `−0.0023` (24), `−0.0005` (28), `−0.0005` (31), `−0.0006` (33).
Fitting only the `1/N` coefficient with the limit fixed at `c*` gives `1.090` (theory `1.131`).
Unconstrained power-law fits are ill-conditioned on this window; those that converge give limits
`0.29–0.31`.

**The same law fits the root.**  Along Fornet's beam witnesses (`experiments/digit-sum/
beam-200.json`, costs 20–200, word lengths 52–624), `C₀ = B − c* N − 1.1311 ln N` stays in
`[−2.3, 3.3]`; without the log term `B − c* N` drifts from 4 to 10.  Beam pruning makes these
lengths lower bounds, consistent with the mild upward drift of `C₀`.

**Reading.**  The evidence points to `a_* = c* < 1/3`, with the root `1` behaving like a typical
point.  If so, the deficit `Δ(n) = log_{3/2} n − 3S(n)` along optimal words grows like
`(1 − 3c*) N − 3.39 ln N ≈ 0.087 N − 3.39 ln N`, unbounded, and (G) is false.  At `N ≈ 590` this
gives `Δ ≈ 29.8`; the beam's largest observed deficit is `29.56` (cost 187).  This says nothing
about Antihydra's own orbit from 7, which is one specific path, not an optimal one.

## 3. The second moment is smaller than the iid model's [computed]

`second_moment.c` computes `E[Z_N²]/E[Z_N]²` exactly for `Z_N(x; e^{−θ}) = Σ_w e^{−θ cost(w)}`
(Fornet's PT1.1).  At N = 27: θ = 0.6 → `1.474` (iid branching limit `1.886`); θ = 0.8 → `2.269`,
still creeping up (iid `3.35`); θ = 0.9 → `3.59`, growing (iid `7.73`); θ = 1.0 → `7.31`, growing
(iid diverges; the iid L² boundary is θ ≈ 0.96).  Siblings are forced to opposite parities at the
next step, which lowers pair overlap.  The untruncated second moment cannot reach tilted cost
below 1/3 (that needs θ > 1.21), as in the iid case; the standard remedy is the truncated
(barrier) second moment.

## 4. Proof route for `a_* < 1/3` [paper outline, not done]

1. For θ with tilted mean cost `c(θ) < 1/3`, restrict `Z_N` to words whose running cost stays below
   a linear barrier, and bound the truncated second moment by the pair-divergence sum.  Two legal
   words that diverge at depth `j` differ by a deterministic, exponentially growing 2-adic
   difference `δ`; the pair's legality is a function of one fair parity sequence and the bits of `δ`.
2. Paley–Zygmund then gives `Pr(V_N ≤ c N + o(N)) ≥ ε` for all large `N`.
3. Upgrade to `a_* ≤ c` with subtree restarts and Fornet's almost-sure constancy
   (`integrable-dual-boundary.md` ID).

Any `c < 1/3` refutes Fornet's mean inequality `a_* ≥ 1/3`; equality `a_* = c*` would follow from
step 1 at every `θ < θ*`.  Neither implies Antihydra halts or not.

Prior-work instrument: grep over Fornet's `notes/` and `LOG.md` for "branching random walk",
"Biggins", "Aïdékon", "first-birth", and for second-moment arguments on cheap-word counts found
none; their second moments are Fourier and energy estimates.  Discord not searched.
