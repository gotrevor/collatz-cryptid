# 33 - Rounding-choice foils for Antihydra: a gate, and the ceiling of rounding-blind arguments

*2026-10-15, branch `wip/t2-antihydra-gate`.  Target T2 of the cross-lane review
(`tmp/context/crossreview.md` §4.1, §5).  Tags: **[Lean]** proved in
`lean/Collatz/Antihydra/Foils.lean`, **[paper]** argued here or in a cited note, **[source]** read in
a primary file this lap.  Every Lean declaration below builds with `#print axioms` = `propext,
Classical.choice, Quot.sound` (`even_run_dvd`: no `Classical.choice`).*

## 0. Question and convention

Antihydra: `a_0 = 8`, `a_{k+1} = H(a_k) = a_k + ⌊a_k/2⌋`, counter `+2` on even and `−1` on odd
values, halt when an odd value meets counter `0`.  This is sligocki's rule set and mfornet's
`AntihydraHalts` (`∃k, O_k > 2E_k`).  **[Lean]** `halts_floor_iff`: the all-floor member of our
family halts from `(8,0)` iff `AntihydraHalts`.  `trace_check` pins `a 3 = 27`, `a 14 = 2296`,
`E 14 = 8`, `O 14 = 6` against mfornet's table.

**The family.**  Keep the even branch `x ↦ 3x/2` exact.  At an odd value `x`, allow either
rounding: `⌊3x/2⌋` or `⌈3x/2⌉`.  A choice function `τ : ℕ → Bool` gives one member (`step`,
`orbit`, `Halts`).  In `F_L` (`member L σ`) the choice is constant on blocks of `L` consecutive
odd values: odd `x = 2j+1` lies in block `j / L = x / (2L)` (`blk`).  Antihydra is the all-floor
member of every `F_L` (`member_floor`).

## 1. Results

| # | statement | declaration | tag |
|---|---|---|---|
| 1 | Above height `2LK` (`K ≥ 2`) an orbit visits each block at most once.  So any value-wise choice along an orbit is realized by a member of `F_L` that agrees with a given member below block `K`. | `realize` | [Lean] |
| 2 | **Halting members are dense.**  For `L ≥ 1`, every member of `F_L` agrees, on any finite set of blocks, with a member that halts from any start of height `≥ 2`. | `halting_dense` | [Lean] |
| 3 | **T2 target 2.**  For every `L ≥ 1` and every `K`, some member agreeing with Antihydra below block `K` halts from `(8,0)`. | `exists_halting_member` | [Lean] |
| 4 | Those members have an **odd tail**: from some step on every value is odd and the counter falls by one per step.  Odd runs are unbounded and `E_k` is bounded. | `exists_eventually_odd_member`, `evenCount_bounded` | [Lean] |
| 5 | **Gate.**  No property of orbits shared by all members agreeing with Antihydra below block `K` implies non-halting. | `rounding_blind_cannot_decide` | [Lean] |
| 6 | **Ceiling, lower half.**  Every member agreeing with Antihydra below block `K` has `E_k ≥ E^{Antihydra}_{min(k, h)}`.  Here `h = horizon L K` is the first step at which Antihydra meets an odd value of height `≥ 2LK`. | `evenCount_ceiling_lower` | [Lean] |
| 7 | **Ceiling, sharp.**  For `K ≥ 2` some such member has `E_k = E^{Antihydra}_{min(k,h)}` for every `k`. | `evenCount_ceiling_sharp` | [Lean] |
| 8 | Both behaviours in `F_1`: one member halts from `(8,0)` and one never does (take the even image at every odd value). | `F_one_both`, `exists_nonhalting_member_one` | [Lean] |
| 9 | For general `L`: a member that survives to the first step of height `≥ 2LK` agrees below block `K` with a member that never halts. | `nonhalting_member_of_survives` | [Lean] |
| 10 | Rounding-blind facts that do hold for every member: the even-run cap `2^e ∣ x`, and infinitely many odd values. | `even_run_dvd`, `odd_infinitely_often` | [Lean] |
| 11 | `3x/2 ≡ 1` and `(3x+1)/2 ≡ 2 (mod 3)` at odd `x`, so "`H` misses `2 mod 3`" is rounding-sensitive. | `floor_step_mod_three`, `ceil_step_mod_three` | [Lean] |

**Reading of 6–7: the exact ceiling (target 4).**  Theorem S in the amusical lane gave a
constant (`c* = log_{4/3} 3`).  Here the ceiling has no growth term at all.  Take any argument
whose inputs hold for every member agreeing with Antihydra below block `K`: the exact even
branch, the defect `≤ 1`, sizes, the real cocycle `(3/2)^k`, and any finite simulation up to
height `2LK`.  The best lower bound it can give on `E_k` is Antihydra's own even count up to
`horizon L K`, frozen there.  That is a finite computation, and it is attained.  The upper bound
on `O_k` is correspondingly trivial (`O_k ≤ k − E_{min(k,h)}`).  So the blind facts point the
wrong way: they bound `O` *below* (row 10; mfornet WR4 below) and never `E`.  Non-halting needs
`O_k ≤ 2E_k`.

**The general-`L` non-halting member is open** (row 9 is conditional, and that is the truth, not
a gap in the proof).  For `L` large, block 0 holds every odd value below `2L`.  A member then
makes one choice for all of them, and follows either Antihydra or the all-ceiling orbit (= the
floor orbit of `9`, minus 1) up to height `2L`.  An unconditional non-halting member for every
`L` would need one of those two orbits to survive to every height.  That is a two-orbit Antihydra
statement (85%; argued, not formalized).  Recorded as the open `def` `AllNonhaltingMember`,
with `allNonhaltingMember_of_not_halts` [Lean]: Antihydra's non-halting implies it.  `F_one_both` settles `L = 1`; any fixed small `L` is a
finite check.  Not done.

**On the kickoff's suggested construction.**  The kickoff idea ("pick the odd image at each odd
`x`, blocks decided once past `x > 2L`") does not work as stated below height `4L`.  There a
block holds many odd values, and one choice cannot give the odd image at all of them.  The
proof (`halting_dense`) runs any fixed member until height `2LK`, then switches.  Either that
member halts first, or `realize` applies.  No case split is needed: the odd tail halts from any
counter value.

## 2. Classification of the published partial results (target 3)

Source: Marcelo Fornet's `github.com/mfornet/antihydra-autoresearch`, local clone
`~/src/reservoir/mfornet/antihydra-autoresearch` at `5962e62` (2026-09-14).  This is the
inventory notes/30 cites.  "Blind" means the proof uses only the exact even branch and an odd
step landing in `{⌊3x/2⌋, ⌈3x/2⌉}`.  The verdict "fails for a member" rests on rows 3–4 (the
odd-tail member), so it is a [Lean] fact about the *statement*.  Which law each *proof* uses is
[source] (read this lap, quotes below) or marked otherwise.

| result (mfornet label, file) | statement | law the proof uses | true for every member? |
|---|---|---|---|
| RL1, even half (`notes/runs.md`) | an even run from `2^v u` lasts `v` steps | blind: "`f(2^j·s) = 3·2^{j−1}·s`" | **yes**, `even_run_dvd` [Lean] |
| RL1, odd half (`runs.md`) | an odd run from `1 + 2^w m` lasts `w = v_2(a−1)` steps | floor: "`f(a) = (3a−1)/2 = 1 + 3·2^{w−1} m`" | **no**: odd tails are unbounded (row 4) |
| RL2, RL3 (`runs.md`) | runs `≤ log₂ a_k`; `E, O ≥ 0.75 log₂ k` | the odd cap is floor-exact | for `E` **no** (`evenCount_bounded`); for `O`, yes in substance (WR4) |
| ED2 (`extremal-digit-sums.md`) | sharper constant, `1.505 log₂ j` | the `E` part needs the floor endpoint of an odd run | `E`: **no**.  `O`: blind in substance [subagent reading, not re-derived] |
| RL4, RR7 (`runs.md`, `run-rigidity.md`) | run trichotomy by residue | floor: `w = v_2(3^v u − 1)` | **no** |
| RR1 (`run-rigidity.md`) | Matveev bound for `3^v u − 2^w m = 1` | a pure Diophantine statement, no map | true outright; the map enters only in RR2–4 |
| RR2–RR4 (`run-rigidity.md`) | no two consecutive near-cap runs; a `log log k` term | floor: the junction `c = 1 + 2^w m` comes from RL1 | for `E` **no** |
| RR5, RR11 (`run-rigidity.md`) | caps plus bounded-window Baker are satisfiable with `E = Θ(log k)`; death needs frequency, not long runs | a meta-result on abstract length sequences | not an orbit claim.  Row 4 is a sharper foil, an integer map with `E` bounded |
| ES3, `E` part (`sparse-sunit-digit-growth.md`) | `E_N / log N → ∞` | floor: "use the exact ceiling conjugacy and digit bridge: `E_N(a)=S(g^N(a−1))−S(a−1)`" [source] | **no** (`evenCount_bounded`) |
| ES3, `O` part (same file, ES3.2) | `O_N / log N → ∞` (Evertse, ineffective) | written with floor digits `p_i ∈ {0,1}`.  Blind in substance: only the negative coordinates matter, and WR4 redoes it over all choices | **yes** (WR4) |
| ES4 (same file) | parity switches `/ log N → ∞` | floor (summation by parts on `p_i`) | **no**: the odd tail has finitely many switches |
| Dubickas repeat bound (`dubickas-repeat-source-audit.md`; mfornet `lean/ParityCylinders.lean`) | equal parity blocks force growth | floor: parity-prefix injectivity mod `2^m` | **no**: the odd tail's parity word is eventually constant |
| I1–I6 (`identities.md`) | exact unrolled step; `a_k mod 3 ∈ {0,1}` | floor | **no**: `ceil_step_mod_three` [Lean] |
| Mahler identity `H^k(8) = g^k(7)+1` (`lean/CeilingBridge.lean`) | floor orbit = ceiling orbit + 1 | floor | **no** (a ceiling at 27 gives 41, but `g^4(7)+1 = 40`) |
| mfornet Lean `odds_unbounded` / `evens_unbounded` (`lean/Runs.lean`) | both parities recur | odds: blind.  Evens: floor | odds **yes** (`odd_infinitely_often` [Lean]); evens **no** |
| WR4 (`sparse-word-rewrite-obstruction.md`) | `R_N(d) = min over all choice paths of the odd count`, and `R_N(d)/log N → ∞` | **choice-uniform by construction**: "`R_(N+1)(d)=1+min(R_N((3d−1)/2), R_N((3d+1)/2))` if `d` is odd" [source] | yes.  This *is* the blind `O`-bound |
| (G) (`digit-sum-route.md` §2) | `S(n) ≥ (1/3) log_{3/2} n − C` for all `n` | the exact canonical digit system | not an orbit statement.  **It passes the gate** (§3) |
| BEC, QET, UPM, TVC, TGC, UBG, RSG, BCI, APS, UER | auxiliary measures, digit costs, ceiling-ray records | — | [not opened beyond STATUS.md] |

**Verdict.**  Every published result that bounds `E` from below, caps odd runs, or constrains the
parity word's repetitions uses the exact floor law: each is false for some member (rows 3–4).
The blind results bound `O` from below: RL1 even half, WR4, and ES3's `O` part.  That direction
helps halting.  The crossreview's §5 T2 (ii) expected "every result holds verbatim for every
member".  That was **wrong**, and the opposite is the useful fact.  The run caps and ES3-for-`E`
are rounding-sensitive, which is exactly why they say something about Antihydra.  They stall
at `log` for other reasons (RR5; the Evertse effectivity wall, notes/30).

## 3. Prior work, and the route that passes the gate

**Pre-empted in part [source].**  mfornet already has the `F_1` dynamics.
`notes/real-rounding-boundary.md`: "use fair stochastic rounding: `Z_(n+1)=3Z_n/2`, `Z_n` even;
`Z_(n+1)=(3Z_n−1)/2` or `(3Z_n+1)/2`, `Z_n` odd".  It also has the gap chain between two floor
orbits (`gap-mismatch-canonical.md` GM1.1).  WR4 proves the blind `O` lower bound over all
choices.  RBM3 relates linear growth of `min O_N` to a Rényi dimension, and calls it open.
grep over their `notes/`, `lean/` and `LOG.md` for foil, rounding-blind, bounded `E` or a
halting member found nothing.  The block family `F_L` is absent.  **New here:** the halting
member and its density (rows 2–3), the bounded-`E` member (row 4), the gate (row 5) and the
exact `E` ceiling (rows 6–7).  As mathematics, row 3 is one line in their language ("always
take the odd child").  The value is the gate stated, sharp, and checked.  Discord prior-work
check: not done (no egress); the obvious half may be folklore there (crossreview's 20%).

**What passes the gate.**  mfornet's main route goes through the canonical base-3/2 digit sum
`S`.  Their identity is `b_k(8) = 3S(g^k(7)) − k − 21` (`digit-sum-route.md` §1, in their
`lean/DigitSumBridge.lean`).  The open sufficient estimate (G) is recorded as the `def`
`GlobalDigitBound`; anchor `canonDigitSum_seven`.  (G) is a statement about every integer's
canonical digits, not about the parity statistics of an orbit.  The digit cost charges floor and
ceiling differently.  So the gate does not touch it, and it is the one live route here that is
not rounding-blind.  mfornet's own `C = 0` counterexample refutes only `C = 0`.  Credence that
(G) holds: no opinion (not studied).

**Practical gate (pre-flight for collatz-cryptid).**  Before proposing an Antihydra lemma, ask
whether its inputs hold for every member of `F_L` near Antihydra.  If they do,
`rounding_blind_cannot_decide` kills it, and `evenCount_ceiling_sharp` says it cannot even give
`E_k → ∞`.  The useful controls are the odd-tail member (halting, `E` bounded) and, for `F_1`,
the even-image member (immortal).

## 4. Not claimed

- Nothing about Antihydra's own halting.  The family members are foils, not models.
- The general-`L` unconditional non-halting member (§1).
- A blind *effective* `O` bound in Lean: ED2's `1.505 log₂ k` adaptation is a subagent reading.
- Any `min O` over members beyond WR4's `log`: linear growth is open (mfornet RBM3).
- Prior-work search: mfornet's repo only, plus notes/28's Discord digest.  No Discord search,
  no literature search beyond what mfornet cites.

## 5. Build

`lake build Collatz.Antihydra.Foils` (in the default target via `Collatz.Antihydra`).
