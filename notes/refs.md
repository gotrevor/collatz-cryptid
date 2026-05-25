# Reference Library 📚

Canonical Collatz / 3x+1 papers, kept locally at `data/refs/`. Pulled from arXiv where possible.

## Headline modern result

- **[Tao 2019](../data/refs/tao-2019-almost-all-orbits.pdf)** — "Almost all orbits of the Collatz map attain almost bounded values" (arXiv:1909.03562, v5 2022, 49pp).
  - **Theorem 1.3**: For any function `f : ℕ+ → ℝ` with `lim_{N→∞} f(N) = +∞`, `Colmin(N) < f(N)` for almost all `N ∈ ℕ+` *in the sense of logarithmic density*.
  - Stronger than all prior "almost all" results (Terras, Everett, Allouche, Korec). Brings the bound from `N^θ` for some `θ < 1` down to any divergent `f` whatsoever, e.g. `log log log log N`.
  - Method: probability theory on 3-adic cyclic groups, characteristic function estimates, two-dimensional renewal process. The proof is *not* number-theoretic in flavour - it's probability + harmonic analysis on `ℤ/3ⁿℤ`.
  - **Lean target**: state Theorem 1.3 (see `lean/Collatz/Tao.lean` once written).

## Surveys / canonical references

- **[Lagarias 1985-2011 Annotated Bibliography I](../data/refs/lagarias-2003-survey-1.pdf)** — "The 3x+1 Problem: An Annotated Bibliography (1963-1999)" (arXiv:math/0309224v13, 74pp). The definitive survey of the first ~35 years. Author-sorted, with one-paragraph summaries.
- **[Lagarias 2006-2012 Annotated Bibliography II](../data/refs/lagarias-2006-survey-2.pdf)** — "The 3x+1 Problem: An Annotated Bibliography, II (2000-2009)" (arXiv:math/0608208v6, 42pp). Continuation of part I.

## Best known computational / density bound

- **[Krasikov-Lagarias 2003](../data/refs/krasikov-lagarias-2003-density.pdf)** — "Bounds for the 3x+1 Problem using Difference Inequalities" (arXiv:math/0205002, 21pp). Density bound: `#{N ≤ x : Colmin(N) = 1} ≫ x^{0.84}` for large `x`. Cited heavily in Tao 2019.

## Not in repo (paywalled / pre-arXiv)

- **Lagarias 2010** (ed.), *The Ultimate Challenge: The 3x+1 Problem*, AMS. Comprehensive book. Most chapters draw on Lagarias's two arXiv bibliographies (above).
- **Conway 1972**, "Unpredictable Iterations." Pre-arXiv. Establishes Turing-completeness of generalized 3x+1 maps (via what became FRACTRAN). Key reference for the cryptid bridge (`notes/04-bb-bridge.md`).
- **Conway 1987**, "FRACTRAN: A simple universal programming language for arithmetic." In *Open Problems in Communication and Computation*, ed. Cover & Gopinath.

## Known verification milestones (Collatz checked up to)

| Year | `N ≤` | Source |
|---|---|---|
| 2008 | 5.78 × 10^18 | Oliveira e Silva |
| 2017 | 1 × 10^20 | Roosendaal (BOINC) |
| 2020 | 2^68 ≈ 2.95 × 10^20 | Barina |

Tao 2019, end of §1.1, cites these.

## Conventions in Tao 2019 (worth pinning for Lean)

- `Col : ℕ+ → ℕ+` is the **slow** Collatz map. `Col(N) = 3N+1` if N odd; `Col(N) = N/2` if N even. (Matches our `Collatz.T`, except domain is `ℕ+` not `ℕ`.)
- `Syr : ℕ+_odd → ℕ+_odd` is the **Syracuse map**: `Syr(N) = (3N+1) / 2^{ν₂(3N+1)}`. The "fast" version restricted to odd integers.
- `Colmin(N) := inf_{n ∈ ℕ} Col^n(N)`.
- **Almost all** = logarithmic density 1.
  - `Log(R)` = log-uniform distribution on finite `R ⊂ ℕ+`: `P(Log(R) ∈ A) = (Σ_{N ∈ A ∩ R} 1/N) / (Σ_{N ∈ R} 1/N)`.
  - Logarithmic density of `A ⊂ ℕ+` = `lim_{x→∞} P(Log(ℕ+ ∩ [1, x]) ∈ A)`.
- All probability variables are written in **boldface** in Tao's paper.

## Why log density (not natural density)

Tao §1.1 explains: log density "has better approximate multiplicative invariance properties than the more familiar notion of natural density." The Collatz map roughly multiplies/divides, so multiplicative-invariance matters. Korec-style natural-density "almost all" results can't be iterated (the image of `[1, x]` under `Col` lands in a sparse subset of `[1, x^θ]`, breaking the density bound). Log density doesn't have this problem.

Pinning this here because it explains *why the theorem statement uses log density instead of natural density* - a subtle distinction that's easy to lose when translating to Lean.

## Update / refresh

- `data/refs/` files: PDFs frozen at arXiv versions cited above.
- `notes/refs.md`: keep this index current as new references are added.
