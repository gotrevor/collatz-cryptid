# 20: Erdős-on-base-3-of-2ⁿ ↔ Collatz?

**Started**: 2026-05-27

## The two conjectures

### Collatz (1937)
For every `n ≥ 1`, iterating
```
T(n) = n/2        if n even
T(n) = 3n + 1     if n odd
```
eventually reaches `1`.

### Erdős (1979)
For every `n > 8`, the base-3 representation of `2^n` contains the digit `2`.

The known exceptions are `n ∈ {0, 2, 8}`:
```
2^0 = 1                  base 3: [1]
2^2 = 4                  base 3: [1,1]
2^8 = 256                base 3: [1,1,1,0,0,1]
```
For every other `n` up to a long verified range, `2^n` in base 3 has at
least one `2`.

## Reductions and easy facts

**Erdős is trivial for odd `n`.** Since `2^2 ≡ 1 (mod 3)`,
`2^n mod 3 = 1` if `n` even and `2` if `n` odd.  So for odd `n` the
*lowest* digit of `2^n` in base 3 is already `2`. The whole open content
of Erdős is therefore the **even `n > 8`** case.

That's what `Collatz/Erdos/Partial.lean` formalizes:
- `erdos_odd`: odd `n` case proved
- `erdos_of_even`: reduction to the even case
- `erdos_exceptions_no_two`: the three known exceptions `{0,2,8}` verified
  by `decide`

## Why the conjectures *feel* related

Both are about how powers of `2` and powers of `3` interact:
- Collatz alternates "multiply by 3 (then +1), then strip 2-power factors".
  A trajectory hitting `1` is a balance equation `2^σ = 3^k · n + c_k(n)`
  for some explicit `c_k`.
- Erdős is exactly the question of whether `2^n` is in the "Cantor-set
  numbers" `S = {Σᵢ εᵢ 3^i : εᵢ ∈ {0,1}}` for infinitely many `n`.

Both questions reduce to "obstructions to 2-power / 3-power coincidences".

## Why they may **not** be logically equivalent

I'm not aware of a published proof of an implication in either direction.

The strongest honest statement I can make: a counterexample to Collatz
would impose strong constraints on the base-2 / base-3 representations of
iterates (cf. Eliahou's lower bounds on cycle lengths, and the
`3^k n + c_k(n)` form of Syracuse iterates).  Similarly, the existence of
exceptional Erdős `n` would force `2^n` to lie in a sparse `3`-adic set.
But the **two sparseness conditions don't obviously map onto each other**.

So in `CollatzLink.lean` we package three open questions as `Prop`s:
- `CollatzImpliesErdos`
- `ErdosImpliesCollatz`
- `CollatzEquivErdos`

…without proving any of them. If we ever resolve one of these — even
without resolving Collatz or Erdős themselves — that would be a real
unification.

## What we *might* try

Things that are tractable and would chip at the link without overclaiming:

1. **Verified bound**: prove "Erdős holds for `n ≤ N`" for some large `N`
   by computation. Already trivially true for the bounds humans have
   checked (10⁵+); the Lean version is a `decide`/`Nat.iter` exercise.

2. **Joint statement over residue classes**: study `2^n mod 3^k` and ask
   what densities of `n` force a `2`-digit at position `< k`. Quantitative
   3-adic Erdős already has partial results (Lagarias, others).

3. **Collatz parity sequences vs. base-3 digit sequences**: a Collatz
   trajectory's parity vector and a power-of-2's base-3 digit string are
   both `ℕ → {0,1,2}` sequences with combinatorial constraints. If we
   could exhibit a "good" map between them, the implication question
   would have a target.

4. **Negative result**: prove that *some* weak version of Erdős (e.g.
   "infinitely many `n` have `2 ∈ digits 3 (2^n)`") does **not** imply
   Collatz. This direction is much more reachable and would clarify
   that any equivalence has to use strong content.

## Layout

```
lean/Collatz/Erdos.lean              -- aggregator (entry point)
lean/Collatz/Erdos/Basic.lean        -- 2^n mod 3 facts + digit helpers
lean/Collatz/Erdos/Conjecture.lean   -- ErdosConjecture (Prop) + reformulation
lean/Collatz/Erdos/Partial.lean      -- odd-n proof + known exceptions
lean/Collatz/Erdos/CollatzLink.lean  -- the three open implication Props
notes/22-erdos-collatz.md            -- this file
```

Built with `cd lean && lake build Collatz.Erdos` (not pulled in from root).

## Open content (intended next steps)

- [ ] Verify build is sorry-free on the partial results
- [ ] Empirical check: smallest even `n > 8` where `2^n base 3` has no `2`
      (should be: none up to ~10⁵, by published computations)
- [ ] Encode Eliahou-style Collatz-cycle base-`6` constraints (do they
      have a base-3 echo?)

## What the `#eval` showed (added 2026-05-27)

`Erdos/Compare.lean` dumps, for small `n`, the triple `(n, F(n,k), G(n,k),
digits_3(2^n))` where `F` is the Syracuse parity vector and `G = 2^n mod 3^k`.

The visible structure:

* Every Syracuse parity vector for odd `n ≤ 15` converges to a "tail of
  all 2s" — the Syracuse fixed point `1 → 1` contributes exponent 2 forever.
* There is **no term-by-term correspondence** between `F(n, k)` and the
  base-3 digits of `2^n`.  The two sequences live at different "time
  scales" (parity vector at step `k` is Syracuse-step `k`; base-3 digit
  at position `k` is power-of-3 `k`).
* But the data made the **right** correspondence visible — see below.

## The real bridge: Lagarias's Syracuse formula

For an odd `m` that reaches `1` in `k` Syracuse steps with parity vector
`(e_1, …, e_k)`, define partial sums `σ_j = e_1 + … + e_j`.  Then
**Lagarias 1985** gives the exact identity:

  2^{σ_k}  =  3^k · m  +  S_k(m)

where  S_k(m) = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{σ_j}.

Taking mod `3^k`:

  **`2^{σ_k} mod 3^k  =  S_k(m) mod 3^k`**

So **the first `k` base-3 digits of `2^{σ_k}` are determined entirely by the
Syracuse parity vector of `m`** (i.e. by which odd integer `m` produces
this trajectory).  This is the bridge between Collatz parity vectors and
the base-3 digits of powers of 2.

### What the bridge actually says

Rearranging `2^N = 3^k · m + S_k(m)` (with `N = σ_k(m)`) gives a clean
two-piece decomposition of the base-3 expansion of `2^N`:

  **`digits_3(2^N)`  =  `digits_3(S_k(m))` in the low `k` positions,
                      then `digits_3(m)` shifted up by `k`, modulo
                      any carry between the two pieces.**

Verification on `N = 8, m = 85, k = 1`:

  m = 85 = `[1, 1, 0, 0, 1]` (base 3)
  S_1(85) = 1 = `[1]`
  2^8 = 3·85 + 1 = 256
  digits_3(256) = `[1, 1, 1, 0, 0, 1]`  ✓
  = `[S_1] ++ [shifted m]` with no carry.

Verification on `N = 2, m = 1, k = 1`:

  m = 1 = `[1]`,  S_1(1) = 1 = `[1]`
  2^2 = 4,  digits_3(4) = `[1, 1]`  =  `[S_1] ++ [shifted m]`.

So **the Erdős-exceptional `N ∈ {2, 8}` correspond exactly to odd `m`'s
whose base-3 expansion has no `2`** (and whose Syracuse step `S_k(m)`
also has no `2`, and no carry between the two pieces introduces one):

| `N` | `m` reaching 1 | base-3 of `m` | `S_k(m)` | base-3 of `2^N` |
|-----|----------------|---------------|----------|-----------------|
| 2   | 1 (k=1)        | `[1]`         | 1        | `[1, 1]`        |
| 8   | 85 (k=1)       | `[1, 1, 0, 0, 1]` | 1    | `[1, 1, 1, 0, 0, 1]` |

(`N = 0` is degenerate: `k = 0`, no Syracuse step.)

This is **a real research-shaped framework**: searching for a new Erdős
exception `N > 8` reduces (conditional on Collatz for the relevant `m`)
to searching for odd `m` whose base-3 expansion has no `2`, whose
Syracuse trajectory's `S_k(m)` also has no `2`, and where the addition
`3^k · m + S_k(m)` introduces no carry-`2`.

### What it doesn't give

* **An implication in either direction between the two open problems.**
  The bridge presupposes `m → 1` (i.e. assumes Collatz for `m`); it does
  not let us derive Collatz from Erdős nor vice versa.
* **A characterization of all Erdős-exceptional `N`.**  The bridge runs
  through `(m, k)` with `σ_k(m) = N`, but not every `N` arises this way
  for small `k` (e.g. no odd `m ≥ 1` reaches `1` in `k ≥ 2` Syracuse
  steps with `σ_k = 8`, since `3^k > 2^8` for `k ≥ 6`).

But it is a **real, concrete object to formalize**, and it crystallized
out of the `#eval` data — which was the point of (2).

## Updated next steps

- [x] **Formalize the Lagarias identity** (done 2026-05-27, sorry-free).
      `Erdos/Lagarias.lean` proves the **unconditional** identity

         2^{σ_k(m)} · σ^k(m)  =  3^k · m + S_k(m)

      for *any* `m, k` (no Collatz hypothesis needed).  Specialization
      `syracuse_lagarias_of_reach_one` extracts `2^{σ_k} = 3^k m + S_k`
      when `m` reaches `1`.  The two Erdős-exceptional witnesses
      `(m, k, σ_k, S_k) = (1, 1, 2, 1)` and `(85, 1, 8, 1)` are
      machine-verified examples in the same file.
- [x] **Low-k digit bridge** (done 2026-05-27).  `Erdos/Lagarias.lean`
      adds `syracuse_lagarias_mod`:
        `(2^{σ_k(m)} · σ^k(m)) mod 3^k = S_k(m) mod 3^k`
      unconditionally, and `lagarias_two_pow_mod_three_pow` for the
      reach-1 specialization `2^{σ_k(m)} mod 3^k = S_k(m) mod 3^k`.
      This is the "first k base-3 digits" bridge in its tightest form.
- [x] **Computable Erdős witness search** (done 2026-05-27, extended
      same day).  `Erdos/Search.lean` enumerates `(m, k, σ_k(m))` for
      odd `m` and `k`-step Syracuse prefixes, filtering to those where
      `2^{σ_k(m)}` has no `2` in base 3.
      **Empirical result**: at every scale tested —
      `(100, 6)`, `(300, 10)`, `(1000, 12)`, `(5000, 18)`,
      `(20000, 22)` (≈ 440,000 prefixes total, ~6 s of `#eval`) —
      the search returns exactly `[0, 2, 8]`.  Lean's interpreted
      runtime handles real scale.

- [x] **Carry-aware Erdős reformulation** (done 2026-05-27).
      `Erdos/CarrySplit.lean` proves the base-3 divmod split
      `2 ∈ digits_3(N) ↔ 2 ∈ digits_3(N mod 3^k) ∨ 2 ∈ digits_3(N / 3^k)`,
      then composes with Lagarias to get the proper bridge

         `2^{σ_k(m)}` has no `2` in base 3   (Erdős condition at `N = σ_k`)
           ↔
         `S_k(m) mod 3^k` has no `2`  ∧  `m + ⌊S_k(m) / 3^k⌋` has no `2`

      for any odd `m` reaching `1` in `k` Syracuse steps.  The bridge
      is now a Lean theorem (`no_two_iff_split_of_reach_one`).

      The witness `(m, k) = (85, 1)` is verified: `S_1(85) = 1`, so
      `S_1 mod 3 = 1` (no `2`) and `85 + 0 = 85 = [1,1,0,0,1]_3` (no
      `2`), implying `2^8 = 256` has no `2`.

## Axiomatized: abc, Pillai, Catalan

Added 2026-05-27.  `Erdos/Axioms.lean` declares three axioms:

```lean
axiom abc     : AbcConjecture     -- open (Masser-Oesterlé)
axiom pillai  : PillaiConjecture  -- open, implied by abc
axiom catalan : CatalanMihailescu -- theorem (Mihailescu 2002)
```

Catalan is genuinely proved (Mihailescu 2002), but we cite it as an
axiom rather than reproving it in Lean.  abc and Pillai are open;
Trevor authorized using them on faith.

### First derivation: Erdős for 2-term sums

`two_pow_eq_two_term_three_pow_sum` (proved):

> If `2^n = 3^a + 3^b` with `b < a`, then `(n, a, b) = (2, 1, 0)`.

Proof sketch:
1. `3 ∤ 2^n` (coprimality) forces `b = 0`, reducing to `2^n = 3^a + 1`.
2. Small cases `n < 2`, `a < 2` handled by `omega`.
3. `n, a ≥ 2`: **Catalan applies directly**.  `2^n = 3^a + 1` with
   `n, a ≥ 2` would force `(x, y, p, q) = (3, 2, 2, 3)` per Mihailescu,
   but we have `x = 2`, contradiction.

This identifies the Erdős exception `N = 2` as the *unique* `n` whose
`2^n` is a 2-term sum of distinct powers of 3.  Note the elegant
catalogue:

| Erdős exception `N` | `2^N` as sum of distinct 3-powers   | term count |
|---|---|---|
| `N = 0` | `1 = 3^0`                              | 1 |
| `N = 2` | `4 = 3 + 1 = 3^1 + 3^0`                | 2 |
| `N = 8` | `256 = 243 + 9 + 3 + 1 = 3^5+3^2+3^1+3^0` | 4 |

(There is no `N` with `2^N` a sum of exactly 3 distinct powers of 3 —
**proved 2026-05-27** in `Erdos/SumsOfPowers.lean` as
`two_pow_ne_three_term_three_pow_sum`.  The proof is elementary: a
**mod-8 argument**.  After forcing `c = 0`, the equation becomes
`2^n = 3^a + 3^b + 1` with `a > b ≥ 1`; for `n ≥ 3` we have
`2^n ≡ 0 (mod 8)`, but `3^a + 3^b + 1 ∈ {3, 5, 7} (mod 8)` always.
No Catalan needed for this case.)

### Catalogue, with proof status

| `k` | unique witness?   | `2^N` form                       | Lean status                |
|---|---|---|---|
| 1 | `(N, a) = (0, 0)`    | `2^0 = 3^0`                       | **proved** (elementary)    |
| 2 | `(N, a, b) = (2, 1, 0)` | `2^2 = 3 + 1`                  | **proved** (uses Catalan)  |
| 3 | none                 | —                                 | **proved** (mod 8)         |
| 4 | `(N, a,b,c,d) = (8, 5,2,1,0)` | `2^8 = 243+9+3+1`        | open in Lean               |
| ≥5| none (conjectural)   | —                                 | open in Lean (Erdős)       |

## The open-problem triple: Collatz, Erdős, Mahler

Added 2026-05-27.  `Erdos/Mahler.lean` encodes **Mahler's 3/2 problem**
(1968) alongside Collatz and Erdős's conjecture as the third member of
the "joint multiplicative behavior of 2 and 3" family:

| problem  | shape                                | conjecture     |
|----------|--------------------------------------|----------------|
| Collatz  | iterate `×3, ÷2` on ℕ                | every `n ≥ 1` reaches 1 |
| Erdős    | digits of `2^n` in base 3            | every `n > 8` has a `2` |
| Mahler   | orbit of `x` under `× (3/2)` mod 1   | no `x` keeps it in `[0, 1/2)` |

```lean
def IsZNumber (x : ℝ) : Prop :=
  0 < x ∧ ∀ n : ℕ, Int.fract (x * (3 / 2 : ℝ) ^ n) < 1 / 2

def MahlerNoZNumber : Prop := ∀ x : ℝ, ¬ IsZNumber x

def OpenTriple : Prop :=
  Conjecture ∧ ErdosConjecture ∧ MahlerNoZNumber
```

Plus four open `Prop`s asking about implications:
`MahlerImpliesCollatz`, `CollatzImpliesMahler`, `MahlerImpliesErdos`,
`ErdosImpliesMahler`.  None is known.

The Collatz–Mahler kinship is concrete on the iterate side: the
Syracuse map `T(n) = (3n+1)/2` for odd `n` is exactly the integer
analogue of multiplying by `3/2` and adding `1/2`, so Collatz orbits
are arithmetic shadows of the `×(3/2)` orbits Mahler studies.  But no
*logical* implication is known.

## Wider family (for future reference)

Lined up by "shape":

* **Iterate ×2 / ×3 dynamics**: Mahler 3/2 (open), Furstenberg ×2,×3
  closed-set theorem (proved, 1967), Furstenberg ×2,×3 invariant-measure
  conjecture (open; positive-entropy case by Rudolph 1990).
* **Digits of `a^n` in base `b`**: Erdős's conjecture (open), Stewart's
  digit-sum theorem (proved, 1980 — gives the asymptotic version).
* **Distinct-prime interaction**: Catalan / Mihailescu (proved, 2002 —
  `3² - 2³ = 1` is the unique solution to `x^p - y^q = 1`), Pillai
  (open), Baker's theorem on linear forms in logarithms (proved,
  effective `|n log 2 - m log 3|` lower bounds), abc (open).
* **Probabilistic shadow**: Weyl equidistribution of `(n log_2 3) mod 1`,
  Tao 2019's almost-all-Collatz result.

The honest unification claim isn't "these are all equivalent" — they
aren't.  It's that they all consume the same algebraic fact
`log_2 3 ∉ ℚ` and run it through different machinery (orbit closure,
digit position, exponent diophantine equation, equidistribution).

## Why "linear independence of 2 and 3" is the right intuition

Trevor's intuition (`sqrt(2)`, `sqrt(3)` linearly independent) points
at the right family of facts.  The version relevant here is
**multiplicative independence of 2 and 3** — equivalently,
`log_2 3 ∉ ℚ`.  This is what makes Lagarias's identity
`2^σ = 3^k m + S_k` resist algebraic simplification: there is no
reduction of `3^k` to a power of 2 (or vice versa), so the base-3
digits of a power of 2 carry irreducible joint 2-adic / 3-adic
information.  Both Collatz and Erdős live in the gap that
independence opens.

(The square-root form Trevor mentioned —
`1, √2, √3, √6` linearly independent over ℚ — is a different
algebraic fact, about the degree of ℚ(√2, √3) over ℚ.  It belongs
to the same family of "2 and 3 are genuinely independent" facts
but doesn't directly imply either conjecture.)
- [ ] Look at higher k: is there an `m` reaching `1` in `k ≥ 2` steps
      with `σ_k = 8`?  Probably not (`3^2 · 1 = 9 > 8`), confirming
      `N = 8` is "isolated" as an Erdős-exceptional σ value.
