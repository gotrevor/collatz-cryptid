# BMO#7 proof (pomme_de_terre, 2025-10-24) 📄

**Source:** a 4-page PDF, `BMO_P7_2.pdf`, posted by Discord user `pomme_de_terre_` in the bbchallenge
forum thread for `1RB1RF_1RC0RA_1LD1RC_1LE0LE_0RA0LD_0RB---` ("bell eats counter"):
<https://discord.com/channels/960643023006490684/1421782442213376000/1431483206208852001>.
This is the link the [BMO wiki](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) §7 cites.
The PDF is kept locally (`papers add`), not committed.

**Credit.** The key step is an ansatz by `planet246` (2025-09-30, same thread), checked numerically
to n = 33,333,333 by `vy.x`.  `sligocki` found the `(4^k, 3·4^k + 1)` regularity first.  The machine
and its reformulation are by `mxdys` (2025-09-28).  `vy.x` reviewed the proof ("lgtm") on 2025-10-25.

## Statement

`f(n) = n + 1 + (v₂(n+1) mod 2)`, `a₀ = 1`, `a_{n+1} = f^{n+2}(⌊a_n / 2⌋)`.  Claim: every `a_k` is odd.

## Proof outline

- `f(n) = n + 2` when `v₂(n+1)` is odd, `n + 1` when it is even.  So `f` climbs one step at a time
  and jumps over the `m` with `v₂(m)` odd.  All of its orbits land on one chain.
- Write `b_n = a_n - 1`.  While `a_n` is odd, `⌊a_n/2⌋ = b_n/2`, so `b_{n+1} = f^{n+2}(b_n/2) - 1`.
- Call `k` *higheven* when `v₂(k) ≥ 4` and `v₂(k)` is even.  **Ansatz (Claim 3):** for `n ≥ 3`,
  the `b_n` list, in increasing order, exactly the `k` with `v₂(k) = 1`, or `k` higheven, or
  `k > 4` with `k - 4` higheven.  It fails at `n = 0` and `n = 2` (`b = 0` and `b = 4`).
- Strong induction on `N > 10`, base cases `b_3 … b_10` checked by hand.  The trick in every case
  is that `f^{N+2}(b_N/2)` and `f^{N+1}(b_{N-1}/2)` follow the same orbit.  So `b_{N+1}` is `f`
  applied a few times to `b_N + 1`, and the conditions on `b_N`, `b_{N-1}` decide those steps.
  - **3.1** `b_N` higheven ⇒ `b_{N+1}, b_{N+2}, b_{N+3} = b_N + 2, +4, +6`.
  - **3.2** `b_N + 2` higheven ⇒ `b_{N+1} = b_N + 2`.
  - **3.3** `v₂(b_N) = 1` and neither `b_N ± 2` higheven ⇒ `b_{N+1} = b_N + 4`.  This splits into
    three subcases by `v₂(b_N ± 2)` and whether `b_N - 6` is higheven.
- Every `b_n` is even, so every `a_n` is odd.

**Imprecision to fix when formalizing:** the induction actually needs "`b_{N-1}` is the element of
the set just before `b_N`", not only "the values form the set".  The case proofs use that
predecessor fact.  The final paragraph proves the successor form, so the right invariant is
`b_{n+1} = next(b_n)`, where `next` gives the following element of the set.

Numerically re-checked in this repo (2026-10-01): the ansatz matches `b_3 … b_3000`.
