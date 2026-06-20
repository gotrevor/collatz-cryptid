# Collatz Cryptid 🦄

> A field guide to specimens of the Collatz dynamical system, organized by
> *species* — residue classes mod `2^k` — rather than by record-breaking
> magnitudes. No claim to prove the conjecture. We're here to map territory.

## The framework (one-paragraph version)

Iterate the **fast Collatz map**:

```
T(n) = (3n+1)/2   if n odd
T(n) = n/2        if n even
```

At each step, the parity of `T^i(n)` is a bit. The first `k` bits — the **parity prefix** — depend only on `n mod 2^k`, and the map `(n mod 2^k) → (first k parities)` is a **bijection** onto `{0,1}^k`. So at depth `k` there are exactly `2^k` species, each a residue class with a unique parity prefix. A species **graduates** at depth `k` when its smallest representative `r` has `T^i(r) < r` for some `i ≤ k`. The Collatz conjecture says: every species graduates eventually.

See `notes/02-species-taxonomy.md` for the careful version.

## The field guide

- 🧬 **Species** — residue classes mod `2^k`, indexed by parity prefix
- 📊 **Graduation curve** `ρ(k)` — fraction of species graduated by depth `k`
- 🦴 **Stubborn species** — residue classes whose smallest rep hasn't dropped below itself in `k` fast-T steps. The actual cryptids.

Calibration data (records, peak heights) is kept in `data/champions.json` but not the headline. We're not chasing trophies.

## Repo layout

```
collatz-cryptid/
├── species.py       # v0.2 — species enumeration + graduation curve
├── stopping.py      # v0.1 — records/champions (calibration only)
├── data/
│   ├── graduation.json   # rate ρ(k) for each k
│   ├── stubborn.csv      # residue classes ungraduated at K_MAX
│   └── champions.json    # records sanity-check
└── notes/
    ├── 01-first-sightings.md     # v0.1 records run
    ├── 02-species-taxonomy.md    # the framework
    └── 03-graduation-at-k20.md   # first species findings (97.4% at K=20)
```

## Run it

```bash
cd ~/src/collatz-cryptid
python3 species.py 20      # default; ~1.5s, dumps graduation + stubborn
python3 species.py 24      # ~25s estimated; ~0.5% expected stubborn
python3 stopping.py 1000000  # records calibration; ~6s
```

## Findings so far

At K=20: **97.4%** of species have graduated; **2.6%** (27,329) are stubborn. Stubborn species' parity prefixes average **71% ones** vs 50% uniform — odd-heavy lineages are the holdouts. Convergence shows **plateaus** at every odd `k → k+1` transition. Why is the next question.

## Roadmap

- **v0.1** ✅ records calibration (`stopping.py`)
- **v0.2** ✅ species enumeration + graduation curve (`species.py`)
- **v0.3** stubborn-lineage tree: how often does both-children-stubborn happen at depth `k+1`?
- **v0.4** push to `K=24` or `K=28`; revisit convergence rate
- **v0.x** Lean formalization of `T`, parity-vector bijection, residue determinism — once we know which lemma earns its keep

No mathlib dependency yet. Pure Python until the data tells us what to formalize.

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
