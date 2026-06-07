# Conway, "Unpredictable Iterations" (1972)

## Provenance
- **Author**: J. H. Conway (Trinity College, Cambridge / Caltech)
- **Title**: Unpredictable Iterations
- **Original venue**: *Proceedings of the Number Theory Conference* (Univ. of Colorado, Boulder, 1972), pp. 49–52. Reprinted (with an added Editorial Commentary) in *The Ultimate Challenge: The 3x+1 Problem*, ed. J. C. Lagarias, AMS 2010, pp. 219–223.
- **Local PDF**: `papers/1972-conway-unpredictable-iterations.pdf` (gitignored — copyrighted full-text, kept local for reading; this repo is eventually-public so only this summary is committed). Scan source: gwern.net `/doc/cs/computable/1972-conway.pdf`.
- **Why it's here**: theoretical floor under collatz-cryptid. This is the paper that proves *generalized* Collatz maps are Turing-complete, hence the stopping problem is undecidable in general — the reason "conditional Collatz → Busy Beaver" reductions exist at all.

## One-paragraph abstract
Conway takes Collatz's `g(n) = n/2` (even) `/ 3n+1` (odd) and generalizes to piecewise-linear maps `g(n) = aᵢn + bᵢ` for `n ≡ i (mod P)`, with rational coefficients chosen so `g` stays integer-valued. He proves these maps can simulate **any** computable function, so the iteration `gᵏ(n)` is in general undecidable — even in the purely multiplicative case `bᵢ = 0`. The construction is the direct ancestor of **FRACTRAN** (named by Conway only in 1987).

## The main theorem
For any computable `f`, there is a generalized-Collatz `g` with:
1. `g(n)/n` periodic (rational values, period dividing the lcm of the denominators), and
2. `2^{f(n)} = gᵏ(2ⁿ)`, where `k` is the least positive exponent making `gᵏ(2ⁿ)` a power of 2.

**Corollary.** No algorithm decides, given such a `g` and an `n`, whether some `k` has `gᵏ(n) = 1`. The generalized-Collatz stopping problem is undecidable.

## The three-layer reduction (the engine)
1. **Minsky machines** — register/counter machines, two instruction types: `a+` (increment `a`, goto `n`) and `b−` (if `b>0` decrement & goto `n`, else goto `p`). Compute all partial recursive functions. (= Minsky's 1961 counter machines used for unsolvability of Post's tag problem.)
2. **Vector games** — finite list of integer vectors; from a nonneg vector repeatedly add the *first* listed vector keeping all coords ≥ 0. One coord per register + two control coords encode any Minsky program. Each `a+`/`b−` order maps to a fixed vector (or pair), listed in decreasing order of the program-counter coordinate.
3. **Rational games** — encode vector `(a,b,c,…)` as `2ᵃ3ᵇ5ᶜ…`. "Add the first legal vector" becomes "replace `n` by `rᵢ·n` for the least `i` making it an integer." **This is FRACTRAN.** So a rational game sends `2ⁿ → 2^{f(n)}` hitting no intermediate power of 2.

## Honest caveats (Conway's own)
- Says **nothing** about the actual 3x+1 problem. Particular maps (Collatz included) may still be predictable; what's killed is any *general* method, plus the existence of provably-unsolvable special cases.
- Byproduct: the construction contains the **Kleene Normal Form theorem** for partial recursive functions (since `g(n)`, `2ⁿ` are primitive recursive).

## Editorial Commentary notes (from the AMS reprint)
- One of the earliest math papers on 3x+1.
- Conway's "industrious reader, produce a prime-generating vector game" challenge → answered by R. K. Guy 1983 (*Conway's Prime Producing Machine*, Math. Mag. 56), i.e. PRIMEGAME.
- The fraction model was formalized as **FRACTRAN** in Conway 1987 (a pun on FORTRAN).
- Minsky machines here = the counter machines of Minsky 1961 (*Annals of Math.* 74).

## Relevance to this repo
- The "encode state as `2ᵃ3ᵇ5ᶜ…`" move is Gödel-numbering by prime exponents; FRACTRAN is its clean distillation. Same spirit as encoding cryptid configurations for the BB reductions.
- Establishes *why* conditional-Collatz → BB(n) deciders are even possible: generalized Collatz is Turing-complete. The cryptid project rides this into specific small-machine deciders (Bigfoot, Holdout 153, BB(6) batches).
