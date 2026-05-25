# First Sightings (N ≤ 10^6) 🔍

Initial sweep with `stopping.py 1000000`. 5.7 seconds, plain Python.

## The canonical specimen: **n = 27** 🦄

The Collatz cryptid everyone knows. We pinned it on our first scan:

- τ(27) = 111 (steps to 1)
- σ(27) = 96 (steps to first drop below 27)
- peak = 9,232 = 342·27 (well, 341.93·27 - 9232/27 = 341.925...)

For a number this small, that altitude is absurd. Used in pop-math demos for a reason.

## Altitude record at N = 10^6: **n = 159,487** 🚀

- peak = **17,202,377,752** (over 17 billion)
- ratio peak/n ≈ **107,861**

Starts at ~160K, climbs through 17 *billion* before eventually surrendering to 1. Of the entries in our altitude-champion list, this is the first to cross a 5-digit ratio.

## τ record at N = 10^6: **n = 837,799** 🏔

- τ(837,799) = **524 steps** to reach 1

Matches OEIS A006877 (record-setting starting values for τ). Sanity check passed.

## σ record at N = 10^6: **n = 626,331** 🐢

- σ(626,331) = **287 steps** to first drop below itself

The stubborn specimens. σ is the more "structural" statistic - σ(n) is determined by `n mod 2^σ(n)`, which is the foothold we want for v0.2/v0.3.

## What's striking

Both σ and τ records are *integer multiples of small numbers in suggestive ways* worth checking:
- 837,799 is prime
- 626,331 = 3 · 7 · 7 · 4259 (need to verify - just eyeballing)
- 159,487 - prime? composite? unchecked

Not sure this means anything. Cryptid hunting often turns up red herrings. Worth noting for follow-up.

## What I want next (v0.2)

1. **Parity vector capture.** For each champion, record the sequence of odd/even (or v_2) values. This is the actual "fingerprint" of an orbit.
2. **Trajectory twins.** Find consecutive `(n, n+1)` pairs with identical τ. Conjecturally these cluster on residue classes mod 2^k.
3. **A plot.** `peak vs n` and `τ vs log(n)` for n ≤ 10^4 - eyeball the shape.

Probably want matplotlib for #3, which means deciding on Python env (sandbox? uv-shebang? local venv?).
