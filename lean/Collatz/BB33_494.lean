import Mathlib.Tactic
import Collatz.BB
import Collatz.BB.SideTape
import Collatz.BB.Multistep
import Collatz.BB.Tactics

/-!
# BB(3,3) unofficial holdout 494 — non-halting in Lean

Lean port of `busycoq/verify/BB33_494.v` (Coq proof by Jason Yuen; proof
sketch by Matthew L. House). Demonstrates the "longitudinal analysis"
template that recently closed BB(3,3) machines 650, 412, 279 in Rocq.

## Status of this file

* ✅ **Number-theory core**: the paired recursive sequences `a`, `c`,
  `cc` are defined, and the dominance inequality `cc_bounds` (the
  Lyapunov-equivalent) is proven in full.
* ⏳ **Tape-level rules** (`C_0b1`, `C_1b1`, `C_2b1`, `C_3b0`, `D_gt`,
  `D_lt`, etc.): stated with the right signatures, `sorry`-bodied
  pending a side-stream model refactor with head-direction tracking
  (needed for verbatim port of busycoq's `l <{{q}} r` style).
* ⏳ **Framework lemma** `progress_nonhalt_simple` (in `BB/Multistep.lean`):
  signature frozen, proof TODO.

The number-theory core is the *load-bearing* mathematical content;
the rest is mechanical translation that doesn't reveal further math.
Filling the tape sorries is multi-session "infrastructure carpentry".

## Reference
`~/src/bb-deep-dive/busycoq-ccz/verify/BB33_494.v`, 329 lines.
-/

namespace BB33_494

open BB

/-! ## Machine 494 -/

/-- BB(3,3) machine `1RB2LA0LA_2LC---2RA_0RA2RC1LC`. -/
def machine : Machine := fun q s =>
  match q, s with
  | State.A, Sym.s0 => some ⟨State.B, Sym.s1, Dir.R⟩  -- 1RB
  | State.A, Sym.s1 => some ⟨State.A, Sym.s2, Dir.L⟩  -- 2LA
  | State.A, Sym.s2 => some ⟨State.A, Sym.s0, Dir.L⟩  -- 0LA
  | State.B, Sym.s0 => some ⟨State.C, Sym.s2, Dir.L⟩  -- 2LC
  | State.B, Sym.s1 => none                            -- ---
  | State.B, Sym.s2 => some ⟨State.A, Sym.s2, Dir.R⟩  -- 2RA
  | State.C, Sym.s0 => some ⟨State.A, Sym.s0, Dir.R⟩  -- 0RA
  | State.C, Sym.s1 => some ⟨State.C, Sym.s2, Dir.R⟩  -- 2RC
  | State.C, Sym.s2 => some ⟨State.C, Sym.s1, Dir.L⟩  -- 1LC

/-! ## Configuration `C(a, b, c)` and rule statements

These mirror busycoq's:
```
C(a, b, c) = 0^∞ (12)^a 2^b C> 202 (202)^c 000
```
The Lean form takes an optional "tail" `r : Side`. -/

/-- Configuration form `C(a, b, c) := 0^∞ (1 2)^a 2^b C> 2 0 2 (2 0 2)^c 0 0 0 r`.

Encoded in canonical `Cfg2` with head reading the first `2` of the
`2 0 2 ...` block:
* `state = State.C`, `headSym = Sym.s2`
* `left` (head outward): `[2]^b` then `[2, 1]^a` then blanks. The `(1 2)`
  pairs of the paper, when scanned outward from the head, give `s2`
  innermost then `s1` then `s2` then `s1` — matching busycoq's `[2;1]^^a`.
* `right` (head outward, head cell NOT included): `0 2 (2 0 2)^c 0 0 0 r`. -/
def C (a b c : ℕ) (r : Side) : Cfg2 where
  state := State.C
  left  := repeatList [Sym.s2] b (repeatList [Sym.s2, Sym.s1] a Side.blank)
  headSym := Sym.s2
  right :=
    Sym.s0 >> Sym.s2 >>
      repeatList [Sym.s2, Sym.s0, Sym.s2] c
        (Sym.s0 >> Sym.s0 >> Sym.s0 >> r)

/-! ### Helper multistep lemmas (`l2_r1`, `r1_l2`, `l2_r0`)

The three "sweep" lemmas. Each takes `n` cells of one symbol from one
side and deposits `n` cells of another symbol on the other side. Stated
with `Cfg2.dirL` / `Cfg2.dirR` to mirror busycoq's `l <{{q}} r` and
`l {{q}}> r` notations. -/

/-- State C, head looking left at n `s2`'s ahead of `l` → state C
looking left at `l`, with n `s1`'s deposited on right. Mirrors `l2_r1`. -/
theorem l2_r1 (n : ℕ) (l r : Side) :
    Cfg2.dirL State.C (repeatList [Sym.s2] n l) r -[machine]->*
      Cfg2.dirL State.C l (repeatList [Sym.s1] n r) := by
  induction n generalizing r with
  | zero => simp only [Side.repeatList_zero]; tm_finish
  | succ n ih =>
      rw [show repeatList [Sym.s2] (n + 1) l =
        Sym.s2 >> repeatList [Sym.s2] n l from rfl]
      simp only [Cfg2.dirL_cons]
      tm_step
      tm_follow (ih (Sym.s1 >> r))
      rw [Side.merge_1]
      tm_finish

/-- State C, head looking right at n `s1`'s ahead of `r` → state C
looking right at `r`, with n `s2`'s deposited on left. Mirrors `r1_l2`. -/
theorem r1_l2 (n : ℕ) (l r : Side) :
    Cfg2.dirR State.C l (repeatList [Sym.s1] n r) -[machine]->*
      Cfg2.dirR State.C (repeatList [Sym.s2] n l) r := by
  induction n generalizing l with
  | zero => simp only [Side.repeatList_zero]; tm_finish
  | succ n ih =>
      rw [show repeatList [Sym.s1] (n + 1) r =
        Sym.s1 >> repeatList [Sym.s1] n r from rfl]
      simp only [Cfg2.dirR_cons]
      tm_step
      tm_follow (ih (Sym.s2 >> l))
      rw [Side.merge_1]
      tm_finish

/-- State A, head looking left at n `s2`'s ahead of `l` → state A
looking left at `l`, with n `s0`'s deposited on right. Mirrors `l2_r0`. -/
theorem l2_r0 (n : ℕ) (l r : Side) :
    Cfg2.dirL State.A (repeatList [Sym.s2] n l) r -[machine]->*
      Cfg2.dirL State.A l (repeatList [Sym.s0] n r) := by
  induction n generalizing r with
  | zero => simp only [Side.repeatList_zero]; tm_finish
  | succ n ih =>
      rw [show repeatList [Sym.s2] (n + 1) l =
        Sym.s2 >> repeatList [Sym.s2] n l from rfl]
      simp only [Cfg2.dirL_cons]
      tm_step
      tm_follow (ih (Sym.s0 >> r))
      rw [Side.merge_1]
      tm_finish

/-! ### Boundary-sweep helpers (`l12_r20`, `r20_2_l12`, `R2`, `R2_finish`,
`r20_l12`, `R3`, `R3_finish`)

These mirror busycoq's lemmas at lines 38-94 of `busycoq/verify/BB33_494.v`.
All statements use `Cfg2.dirL` / `Cfg2.dirR` to mirror busycoq's `l <{{q}} r`
and `l {{q}}> r` notations, so LHS/RHS using opposite "directions" over the
same physical state collapse to the same canonical `Cfg2`. -/

/-- State A, looking left at `(s2 s1)^t l` → looking left at `l` with
`(s2 s0)^t` deposited on right. Mirrors busycoq's `l12_r20`. -/
theorem l12_r20 (t : ℕ) (l r : Side) :
    Cfg2.dirL State.A (repeatList [Sym.s2, Sym.s1] t l) r -[machine]->*
      Cfg2.dirL State.A l (repeatList [Sym.s2, Sym.s0] t r) := by
  induction t generalizing r with
  | zero => simp only [Side.repeatList_zero]; tm_finish
  | succ t ih =>
      rw [show repeatList [Sym.s2, Sym.s1] (t + 1) l =
        Sym.s2 >> Sym.s1 >> repeatList [Sym.s2, Sym.s1] t l from rfl]
      simp only [Cfg2.dirL_cons]
      tm_step
      tm_step
      tm_follow (ih (Sym.s2 >> Sym.s0 >> r))
      rw [Side.merge_2]
      tm_finish

/-- State A, looking left at blank with `(s2 s0)^t · s2 · r` to the right
→ looking right at `(s2 s1)^(t+1) blank · r`. Mirrors `r20_2_l12`. -/
theorem r20_2_l12 (t : ℕ) (r : Side) :
    Cfg2.dirL State.A Side.blank
        (repeatList [Sym.s2, Sym.s0] t (Sym.s2 >> r)) -[machine]->*
      Cfg2.dirR State.A
        (repeatList [Sym.s2, Sym.s1] (t + 1) Side.blank) r := by
  induction t generalizing r with
  | zero =>
      simp only [Side.repeatList_zero, Cfg2.dirL_blank]
      rw [show repeatList [Sym.s2, Sym.s1] 1 Side.blank =
        Sym.s2 >> Sym.s1 >> Side.blank from rfl]
      tm_step
      tm_step
      tm_finish
  | succ t ih =>
      rw [show repeatList [Sym.s2, Sym.s0] (t + 1) (Sym.s2 >> r) =
        repeatList [Sym.s2, Sym.s0] t
          (Sym.s2 >> Sym.s0 >> Sym.s2 >> r)
        from (Side.merge_2 Sym.s2 Sym.s0 t (Sym.s2 >> r)).symm]
      tm_follow (ih (Sym.s0 >> Sym.s2 >> r))
      rw [show repeatList [Sym.s2, Sym.s1] (t + 1 + 1) Side.blank =
        Sym.s2 >> Sym.s1 >> repeatList [Sym.s2, Sym.s1] (t + 1) Side.blank
        from rfl]
      tm_step
      tm_step
      tm_finish

/-- One round of the (21)^t accumulator: consume one `1` from right, add
one `[2;1]` block to left. Mirrors busycoq's `R2`. -/
theorem R2 (t u : ℕ) (r : Side) :
    Cfg2.dirR State.A (repeatList [Sym.s2, Sym.s1] t Side.blank)
        (repeatList [Sym.s1] (u + 1) r) -[machine]->*
      Cfg2.dirR State.A (repeatList [Sym.s2, Sym.s1] (t + 1) Side.blank)
        (repeatList [Sym.s1] u r) := by
  rw [show repeatList [Sym.s1] (u + 1) r =
    Sym.s1 >> repeatList [Sym.s1] u r from rfl]
  tm_step
  tm_follow (l12_r20 t Side.blank (Sym.s2 >> repeatList [Sym.s1] u r))
  tm_follow (r20_2_l12 t (repeatList [Sym.s1] u r))
  tm_finish

/-- Iterate `R2`: consume all `1`s from right. Mirrors `R2_finish`. -/
theorem R2_finish (s : ℕ) (r : Side) :
    Cfg2.dirR State.A Side.blank (repeatList [Sym.s1] s r) -[machine]->*
      Cfg2.dirR State.A (repeatList [Sym.s2, Sym.s1] s Side.blank) r := by
  induction s generalizing r with
  | zero => simp only [Side.repeatList_zero]; tm_finish
  | succ s ih =>
      rw [show repeatList [Sym.s1] (s + 1) r =
        repeatList [Sym.s1] s (Sym.s1 >> r)
        from (Side.merge_1 Sym.s1 s r).symm]
      tm_follow (ih (Sym.s1 >> r))
      tm_follow (R2 s 0 r)
      tm_finish

/-- State A, looking left at blank with `(s2 s0)^t · r` to the right →
looking right at `(s2 s1)^t blank · s0 · r`. Mirrors busycoq's `r20_l12`.

With the canonical `Cfg2` encoding, the base case is now `rfl`:
`dirL A blank r = ⟨A, blank, s0, r⟩ = dirR A blank (s0 >> r)`. -/
theorem r20_l12 (t : ℕ) (r : Side) :
    Cfg2.dirL State.A Side.blank (repeatList [Sym.s2, Sym.s0] t r)
        -[machine]->*
      Cfg2.dirR State.A (repeatList [Sym.s2, Sym.s1] t Side.blank)
        (Sym.s0 >> r) := by
  induction t generalizing r with
  | zero =>
      simp only [Side.repeatList_zero, Cfg2.dirL_blank, Cfg2.dirR_cons]
      tm_finish
  | succ t ih =>
      rw [show repeatList [Sym.s2, Sym.s0] (t + 1) r =
        repeatList [Sym.s2, Sym.s0] t (Sym.s2 >> Sym.s0 >> r)
        from (Side.merge_2 Sym.s2 Sym.s0 t r).symm]
      tm_follow (ih (Sym.s2 >> Sym.s0 >> r))
      rw [show repeatList [Sym.s2, Sym.s1] (t + 1) Side.blank =
        Sym.s2 >> Sym.s1 >> repeatList [Sym.s2, Sym.s1] t Side.blank
        from rfl]
      tm_step
      tm_step
      tm_finish

/-- One round of the (12)·(202) accumulator. Mirrors `R3`.

Coq proof is `execute. follow l12_r20. follow r20_l12. trivial.` The
`execute` runs 27 concrete steps; after that the head reads
`(rep [s2,s1] t blank).head` which is symbolic. We then chain `l12_r20`
to sweep the (21)-blocks rightward as (20)-blocks, then `r20_l12` to
sweep back. `tm_finish` closes via defeq
`rep [s2,s0,s2] (u+1) r = s2 >> s0 >> s2 >> rep [s2,s0,s2] u r`. -/
theorem R3 (t u : ℕ) (r : Side) :
    Cfg2.dirR State.A (repeatList [Sym.s2, Sym.s1] (t + 1) Side.blank)
        (Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >>
          repeatList [Sym.s2, Sym.s0, Sym.s2] u r) -[machine]->*
      Cfg2.dirR State.A (repeatList [Sym.s2, Sym.s1] t Side.blank)
        (Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >>
          repeatList [Sym.s2, Sym.s0, Sym.s2] (u + 1) r) := by
  rw [show repeatList [Sym.s2, Sym.s1] (t + 1) Side.blank =
    Sym.s2 >> Sym.s1 >> repeatList [Sym.s2, Sym.s1] t Side.blank from rfl]
  simp only [Cfg2.dirR_cons]
  repeat tm_step
  tm_follow (l12_r20 t Side.blank
    (Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s2 >> Sym.s0 >> Sym.s2 >>
      repeatList [Sym.s2, Sym.s0, Sym.s2] u r))
  tm_follow (r20_l12 t
    (Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s2 >> Sym.s0 >> Sym.s2 >>
      repeatList [Sym.s2, Sym.s0, Sym.s2] u r))
  tm_finish

/-- Iterate `R3`. Mirrors `R3_finish`. -/
theorem R3_finish (s : ℕ) (r : Side) :
    Cfg2.dirR State.A (repeatList [Sym.s2, Sym.s1] s Side.blank)
        (Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >> r) -[machine]->*
      Cfg2.dirR State.A Side.blank
        (Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >> Sym.s0 >>
          repeatList [Sym.s2, Sym.s0, Sym.s2] s r) := by
  induction s generalizing r with
  | zero => simp only [Side.repeatList_zero]; tm_finish
  | succ s ih =>
      tm_follow (R3 s 0 r)
      tm_follow (ih (Sym.s2 >> Sym.s0 >> Sym.s2 >> r))
      rw [Side.merge_3 Sym.s2 Sym.s0 Sym.s2 s r]
      tm_finish

/-! ### The four C-rules

Still sorry'd — they wire up the boundary-sweep helpers above plus
`l2_r1`/`r1_l2`/`l2_r0`. The pattern is established. -/

/-- `C(0, b, c+1) → C(b+2, 1, c)`.

Proof technique: alternate `repeat tm_step` (run as many concrete steps
as possible) with `tm_follow (lemma b _ _)` (use Lean unification to fill
in the Side arguments from goal context). The `rw [Side.merge_1 ..]`
folds a `rep [s1] b (s1 >> r')` pattern into `rep [s1] (b+1) r'`. -/
theorem C_0b1 (b c : ℕ) (r : Side) :
    C 0 b (c + 1) r -[machine]->* C (b + 2) 1 c r := by
  unfold C
  tm_step
  tm_follow (l2_r1 b _ _)
  tm_step
  rw [Side.merge_1 Sym.s1 b _]
  tm_follow (R2_finish (b + 1) _)
  repeat tm_step
  tm_follow (l12_r20 b _ _)
  tm_follow (r20_2_l12 b _)
  repeat tm_step

/-- `C(1, b, c+1) → C(b+5, 1, c)`. Mirrors busycoq's `C_1b1` proof. -/
theorem C_1b1 (b c : ℕ) (r : Side) :
    C 1 b (c + 1) r -[machine]->* C (b + 5) 1 c r := by
  unfold C
  -- Expose s2 >> s1 inside `rep [s2,s1] 1 blank` so the head cells are concrete cons forms
  simp only [show repeatList [Sym.s2, Sym.s1] 1 Side.blank =
    Sym.s2 >> Sym.s1 >> Side.blank from rfl]
  tm_step
  tm_follow (l2_r1 b _ _)
  repeat tm_step
  tm_follow (r1_l2 b _ _)
  rw [Side.merge_1 Sym.s2 b _]
  rw [Side.merge_1 Sym.s2 (b + 1) _]
  repeat tm_step
  tm_follow (l2_r1 b _ _)
  tm_step
  rw [Side.merge_1 Sym.s1 b _]
  rw [Side.merge_1 Sym.s1 (b + 1) _]
  rw [Side.merge_1 Sym.s1 (b + 2) _]
  rw [Side.merge_1 Sym.s1 (b + 3) _]
  rw [Side.merge_1 Sym.s1 (b + 4) _]
  tm_follow (R2_finish (b + 5) _)
  repeat tm_step
  tm_follow (l12_r20 b _ _)
  tm_follow (r20_l12 b _)
  repeat tm_step

/-- `C(a+2, b, c+1) → C(a, b+7, c)`. The only rule that decrements `a`. -/
theorem C_2b1 (a b c : ℕ) (r : Side) :
    C (a + 2) b (c + 1) r -[machine]->* C a (b + 7) c r := by
  unfold C
  -- Expose the two leading (s2, s1) blocks from rep [s2,s1] (a+2) blank
  simp only [show repeatList [Sym.s2, Sym.s1] (a + 2) Side.blank =
    Sym.s2 >> Sym.s1 >> Sym.s2 >> Sym.s1 >>
      repeatList [Sym.s2, Sym.s1] a Side.blank from rfl]
  tm_step
  tm_follow (l2_r1 b _ _)
  repeat tm_step
  tm_follow (r1_l2 b _ _)
  repeat tm_step
  tm_follow (l2_r1 b _ _)
  repeat tm_step
  tm_follow (r1_l2 b _ _)
  rw [Side.merge_1 Sym.s2 _ _, Side.merge_1 Sym.s2 _ _,
      Side.merge_1 Sym.s2 _ _, Side.merge_1 Sym.s2 _ _]
  repeat tm_step

/-- `C(a+3, b, 0) → C(1, 5, a)` (with tail rewritten). The "restart" rule.
Mirrors busycoq's `C_3b0`. -/
theorem C_3b0 (a b : ℕ) (r : Side) :
    C (a + 3) b 0 r -[machine]->+
      C 1 5 a (repeatList [Sym.s0] b
        (Sym.s2 >> Sym.s0 >> Sym.s2 >> r)) := by
  unfold C
  -- Expose three (s2, s1) blocks from rep [s2,s1] (a+3) blank
  simp only [show repeatList [Sym.s2, Sym.s1] (a + 3) Side.blank =
    Sym.s2 >> Sym.s1 >> Sym.s2 >> Sym.s1 >> Sym.s2 >> Sym.s1 >>
      repeatList [Sym.s2, Sym.s1] a Side.blank from rfl]
  tm_step_plus
  tm_follow (l2_r1 b _ _)
  repeat tm_step
  tm_follow (r1_l2 b _ _)
  repeat tm_step
  tm_follow (l2_r1 b _ _)
  repeat tm_step
  tm_follow (r1_l2 b _ _)
  repeat tm_step
  tm_follow (l2_r0 b _ _)
  repeat tm_step
  tm_follow (l12_r20 a _ _)
  rw [Side.merge_2 _ _ _ _]
  tm_follow (r20_l12 (a + 1) _)
  tm_follow (R3_finish (a + 1) _)
  rw [Side.merge_1 Sym.s0 _ _, Side.merge_1 Sym.s0 _ _,
      Side.merge_1 Sym.s0 _ _]
  repeat tm_step

/-- Aggregate `D := C a 1 c`. -/
def D (a c : ℕ) (r : Side) : Cfg2 := C a 1 c r

/-- `k`-fold iteration of `C_2b1`. Mirrors busycoq's `C_2k_b_k`. -/
theorem C_2k_b_k (k a b c : ℕ) (r : Side) :
    C (2 * k + a) b (k + c) r -[machine]->* C a (7 * k + b) c r := by
  induction k generalizing a b c with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add]
      tm_finish
  | succ k ih =>
      have h1 : 2 * (k + 1) + a = (2 * k + a) + 2 := by ring
      have h2 : (k + 1) + c = (k + c) + 1 := by ring
      have h3 : 7 * (k + 1) + b = 7 * k + (b + 7) := by ring
      rw [h1, h2, h3]
      tm_follow (C_2b1 (2 * k + a) b (k + c) r)
      tm_follow (ih a (b + 7) c)
      tm_finish

/-- `D_gt`: `D(k, c + k/2 + 1) → D(3k + k/2 + 3, c)`. Uses `C_2k_b_k` then
case-splits on `k` even/odd to apply `C_0b1` or `C_1b1`. -/
theorem D_gt (k c : ℕ) (r : Side) :
    D k (c + k / 2 + 1) r -[machine]->* D (3 * k + k / 2 + 3) c r := by
  unfold D
  -- Decompose k = 2*(k/2) + (k%2); rewrite the index forms
  have hdiv := Nat.div_add_mod k 2
  -- Goal: C k 1 (c + k/2 + 1) r -->* C (3*k + k/2 + 3) 1 c r
  -- Mirror Coq: rewrite first k via Nat.div_mod, then ring-normalize c index.
  nth_rewrite 1 [show k = 2 * (k / 2) + k % 2 from hdiv.symm]
  have hc : c + k / 2 + 1 = k / 2 + (c + 1) := by ring
  rw [hc]
  tm_follow (C_2k_b_k (k / 2) (k % 2) 1 (c + 1) r)
  -- Goal: C (k % 2) (7 * (k/2) + 1) (c + 1) r -->* C (3*k + k/2 + 3) 1 c r
  -- Case-split on k%2
  rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
  · -- k % 2 = 0: use C_0b1
    rw [hmod]
    tm_follow (C_0b1 (7 * (k / 2) + 1) c r)
    -- Goal: C (7 * (k/2) + 1 + 2) 1 c r -->* C (3*k + k/2 + 3) 1 c r
    have heq : 7 * (k / 2) + 1 + 2 = 3 * k + k / 2 + 3 := by omega
    rw [heq]
    tm_finish
  · -- k % 2 = 1: use C_1b1
    rw [hmod]
    tm_follow (C_1b1 (7 * (k / 2) + 1) c r)
    -- Goal: C (7 * (k/2) + 1 + 5) 1 c r -->* C (3*k + k/2 + 3) 1 c r
    have heq : 7 * (k / 2) + 1 + 5 = 3 * k + k / 2 + 3 := by omega
    rw [heq]
    tm_finish

/-- `D_lt`: when `c < k/2 - 1`, the chain ends in a "restart" via `C_3b0`.
Result: `D(10, k)` with a tail expansion `[0]^(7c+1) 2 0 2 r`. Mirrors
busycoq's `D_lt`. -/
theorem D_lt (k c : ℕ) (r : Side) :
    D (k + 2 * c + 4) c r -[machine]->+
      D 10 k (repeatList [Sym.s0] (7 * c + 1)
        (Sym.s2 >> Sym.s0 >> Sym.s2 >> r)) := by
  unfold D
  -- Mirror Coq: replace (k + 2c + 4) with 2c + (k + 4), and c with c + 0.
  have h1 : k + 2 * c + 4 = 2 * c + (k + 4) := by ring
  rw [h1]
  nth_rewrite 2 [show c = c + 0 from rfl]
  -- Goal: C (2*c + (k+4)) 1 (c+0) r -->+ D 10 k (...)
  refine MultistepPlus.trans_right (C_2k_b_k c (k + 4) 1 0 r) ?_
  -- Goal: C (k+4) (7*c + 1) 0 r -->+ D 10 k (...)
  have hk : k + 4 = (k + 1) + 3 := by ring
  rw [hk]
  refine MultistepPlus.append (C_3b0 (k + 1) (7 * c + 1) r) ?_
  -- After C_3b0: C 1 5 (k+1) (rep [s0] (7*c+1) (s2 >> s0 >> s2 >> r))
  -- C_1b1 with b=5, c=k closes to C 10 1 k r'.
  tm_follow (C_1b1 5 k (repeatList [Sym.s0] (7 * c + 1)
    (Sym.s2 >> Sym.s0 >> Sym.s2 >> r)))
  tm_finish

/-! ## Number-theory core (no `sorry`s)

The paired recursive sequences and the dominance inequality
`cc_bounds`. This is the load-bearing mathematical content that ports
"longitudinal analysis" from Coq to Lean. -/

/-- `a(0) = 10, a(i+1) = 3·a(i) + a(i)/2 + 3`.
Concrete values: `10, 38, 136, 479, 1679, 5879, ...` -/
def a : ℕ → ℕ
  | 0     => 10
  | i + 1 => 3 * a i + a i / 2 + 3

/-- Growth lemma: `7·a(i) + 5 ≤ 2·a(i+1)`. -/
theorem a_le_aS (i : ℕ) : 7 * a i + 5 ≤ 2 * a (i + 1) := by
  show 7 * a i + 5 ≤ 2 * (3 * a i + a i / 2 + 3)
  have h := Nat.div_add_mod (a i) 2
  omega

/-- `c(0) = 0, c(i+1) = c(i) + a(i)/2 + 1`.
Concrete values: `0, 6, 26, 95, 335, 1175, 4115, ...` -/
def c : ℕ → ℕ
  | 0     => 0
  | i + 1 => c i + a i / 2 + 1

/-- The auxiliary `cc` sequence:
`cc(0) = 0, cc(i+1) = a(i) - 2·(cc(i) - c(i)) - 4`.
Concrete: `0, 6, 34, 116, 433, 1479, 5267, ...` -/
def cc : ℕ → ℕ
  | 0     => 0
  | i + 1 => a i - 2 * (cc i - c i) - 4

/-- `a(i) ≤ 5·c(i) + 10`, by induction. Used in `cc_bounds`. -/
theorem a_le_5c10 (i : ℕ) : a i ≤ 5 * c i + 10 := by
  induction i with
  | zero => decide
  | succ i ih =>
      show 3 * a i + a i / 2 + 3 ≤ 5 * (c i + a i / 2 + 1) + 10
      have h := Nat.div_add_mod (a i) 2
      omega

/-- `a(i) ≥ 4` always, by induction. -/
theorem a_ge_4 (i : ℕ) : 4 ≤ a i := by
  induction i with
  | zero => decide
  | succ i ih =>
      show 4 ≤ 3 * a i + a i / 2 + 3
      omega

/-- **The dominance inequality.** This is the Lyapunov-equivalent: the
`c` sequence dominates `cc`, and `2·cc(i) + 6 ≤ c(i+1)` — meaning the
"gap" `cc(i) - c(i)` is bounded enough that the longitudinal trajectory
can keep going. -/
theorem cc_bounds (i : ℕ) : c i ≤ cc i ∧ 2 * cc i + 6 ≤ c (i + 1) := by
  induction i with
  | zero => decide
  | succ i ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨?_, ?_⟩
      · -- c (i+1) ≤ cc (i+1) = a i - 2*(cc i - c i) - 4
        -- We have c (i+1) = c i + a i / 2 + 1 (def)
        -- and h2: 2*cc i + 6 ≤ c (i+1)
        -- Suffices: c (i+1) ≤ a i - 2*(cc i - c i) - 4
        -- i.e., c (i+1) + 2*(cc i - c i) + 4 ≤ a i
        -- i.e., (c i + a i / 2 + 1) + 2*(cc i - c i) + 4 ≤ a i
        show c (i + 1) ≤ a i - 2 * (cc i - c i) - 4
        -- Standard mathlib ℕ subtraction headache: rewrite via inequality
        have hai := Nat.div_add_mod (a i) 2
        -- The chain: 2 c (i+1) ≤ a i + 2 c i + 2
        have hc1 : 2 * c (i + 1) ≤ a i + 2 * c i + 2 := by
          show 2 * (c i + a i / 2 + 1) ≤ a i + 2 * c i + 2
          have := Nat.div_mul_le_self (a i) 2
          omega
        omega
      · -- 2 * cc (i+1) + 6 ≤ c (i+2).
        -- Goal arrives as `... ≤ c (i + 1 + 1)`; keep that form so omega
        -- doesn't see two distinct vars for the same term.
        have hcci1 : cc (i + 1) = a i - 2 * (cc i - c i) - 4 := rfl
        have hci2 : c (i + 1 + 1) = c (i + 1) + a (i + 1) / 2 + 1 := rfl
        have hai2 : a (i + 1 + 1) = 3 * a (i + 1) + a (i + 1) / 2 + 3 := rfl
        have hai := a_ge_4 i
        have hSi' := a_le_aS i              -- 7 a i + 5 ≤ 2 a (i+1)
        have hSi := a_le_aS (i + 1)         -- 7 a (i+1) + 5 ≤ 2 a (i+1+1)
        have hac := a_le_5c10 (i + 1 + 1)   -- a (i+1+1) ≤ 5 c (i+1+1) + 10
        have hdiv1 := Nat.div_add_mod (a (i + 1)) 2
        have hdiv0 := Nat.div_add_mod (a i) 2
        omega

/-! ## Headline theorem (modulo Phase 1 sorries)

The proof structure: define an indexed family `Cfam : ℕ → Cfg2` with
`Cfam i = D (a 0) (cc i - c 0) ...`, and use `progress_nonhalt_simple`
with the family-step provided by `D_next`. -/

/-- `D_step_cc`: one "restart" cycle via `D_lt`, taking `D (a i) (cc i - c i)`
to `D (a 0) (cc (i+1) - c 0)`. -/
theorem D_step_cc (i : ℕ) (r : Side) : ∃ r',
    D (a i) (cc i - c i) r -[machine]->+ D (a 0) (cc (i + 1) - c 0) r' := by
  refine ⟨repeatList [Sym.s0] (7 * (cc i - c i) + 1)
    (Sym.s2 >> Sym.s0 >> Sym.s2 >> r), ?_⟩
  -- a i = (a i - 2*(cc i - c i) - 4) + 2*(cc i - c i) + 4
  -- via cc_bounds: c (i+1) ≥ 6 ≥ 1, and c (i+1) ≤ cc (i+1) = a i - 2*(cc i - c i) - 4.
  have hcc_i := cc_bounds i
  have hcc_i1 := cc_bounds (i + 1)
  have hcceq : cc (i + 1) = a i - 2 * (cc i - c i) - 4 := rfl
  have hage4 := a_ge_4 i
  -- Extract useful hypotheses for omega
  have hccge : c i ≤ cc i := hcc_i.left
  have hc1ge : 2 * cc i + 6 ≤ c (i + 1) := hcc_i.right
  have hcc1ge : c (i + 1) ≤ cc (i + 1) := hcc_i1.left
  -- Chain: 2*cc i + 6 ≤ c (i+1) ≤ cc (i+1) = a i - 2*(cc i - c i) - 4
  -- So a i - 2*(cc i - c i) - 4 ≥ 6, meaning a i ≥ 2*(cc i - c i) + 10 (the subtraction doesn't truncate).
  have ha : a i = (a i - 2 * (cc i - c i) - 4) + 2 * (cc i - c i) + 4 := by
    omega
  rw [ha]
  refine MultistepPlus.append
    (D_lt (a i - 2 * (cc i - c i) - 4) (cc i - c i) r) ?_
  tm_finish

/-- `c` is monotone in its index. -/
theorem c_monotone (i j : ℕ) : c i ≤ c (j + i) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have heq : j + 1 + i = (j + i) + 1 := by ring
      rw [heq]
      have hdef : c ((j + i) + 1) = c (j + i) + a (j + i) / 2 + 1 := rfl
      rw [hdef]
      omega

/-- One `D_gt` step: increment `i` while preserving the dominance gap. -/
theorem D_step_a (i j : ℕ) (r : Side) :
    D (a i) (cc (j + i + 1) - c i) r -[machine]->*
      D (a (i + 1)) (cc (j + i + 1) - c (i + 1)) r := by
  -- We need a i/2 + 1 ≤ cc (j+i+1) - c i to apply D_gt.
  have hcm := c_monotone (i + 1) j
  have hjsi : j + (i + 1) = j + i + 1 := by ring
  rw [hjsi] at hcm
  obtain ⟨h2, _⟩ := cc_bounds (j + i + 1)
  have hci1 : c (i + 1) = c i + a i / 2 + 1 := rfl
  have heq : cc (j + i + 1) - c i =
      (cc (j + i + 1) - c i - a i / 2 - 1) + a i / 2 + 1 := by omega
  rw [heq]
  refine Multistep.trans (D_gt (a i)
    (cc (j + i + 1) - c i - a i / 2 - 1) r) ?_
  have hai1 : a (i + 1) = 3 * a i + a i / 2 + 3 := rfl
  have hci1' : cc (j + i + 1) - c (i + 1) =
      cc (j + i + 1) - c i - a i / 2 - 1 := by omega
  rw [hai1, hci1']
  tm_finish

/-- `D_step_a` valid when `i < j`. -/
theorem D_step_a_lt (i j : ℕ) (r : Side) (hij : i < j) :
    D (a i) (cc j - c i) r -[machine]->*
      D (a (i + 1)) (cc j - c (i + 1)) r := by
  have hj : j = (j - i - 1) + i + 1 := by omega
  conv_lhs => rw [hj]
  conv_rhs => rw [hj]
  exact D_step_a i (j - i - 1) r

/-- Stage of the climb: from index `i - (n+1)` to `i - n`. -/
theorem D_step_a_minus (i n : ℕ) (r : Side) :
    D (a (i - (n + 1))) (cc i - c (i - (n + 1))) r -[machine]->*
      D (a (i - n)) (cc i - c (i - n)) r := by
  by_cases h : i ≤ n
  · have h1 : i - (n + 1) = 0 := by omega
    have h2 : i - n = 0 := by omega
    rw [h1, h2]
    tm_finish
  · push_neg at h
    have h1 : i - (n + 1) + 1 = i - n := by omega
    have hlt : i - (n + 1) < i := by omega
    have := D_step_a_lt (i - (n + 1)) i r hlt
    rw [h1] at this
    exact this

/-- Climb from `D (a 0)` to `D (a i)`, preserving `cc i`. -/
theorem D_step_a_finish (i : ℕ) (r : Side) :
    D (a 0) (cc i - c 0) r -[machine]->* D (a i) (cc i - c i) r := by
  -- Generalize: prove that climbing any prefix works.
  suffices h : ∀ n, D (a (i - n)) (cc i - c (i - n)) r -[machine]->*
      D (a i) (cc i - c i) r by
    have h0 : i - (i + 1) = 0 := by omega
    have := h (i + 1)
    rw [h0] at this
    exact this
  intro n
  induction n with
  | zero =>
      have : i - 0 = i := by omega
      rw [this]
      tm_finish
  | succ n ih =>
      exact Multistep.trans (D_step_a_minus i n r) ih

/-- Step of the outer cycle: from `D(a 0, cc i - c 0)`, reach
`D(a 0, cc (i+1) - c 0)`. Combines `D_step_a_finish` and `D_step_cc`.
Mirrors busycoq's `D_next`. -/
theorem D_next (i : ℕ) (r : Side) : ∃ r',
    D (a 0) (cc i - c 0) r -[machine]->+ D (a 0) (cc (i + 1) - c 0) r' := by
  obtain ⟨r', H⟩ := D_step_cc i r
  refine ⟨r', ?_⟩
  exact MultistepPlus.trans_right (D_step_a_finish i r) H

set_option maxHeartbeats 4000000 in
/-- Bootstrap: from `Cfg2.blank`, machine 494 reaches `C 1 5 1 Side.blank`
in 105 concrete steps. Mirrors busycoq's `do 105 step` in `nonhalt`. -/
theorem bootstrap : Cfg2.blank -[machine]->* C 1 5 1 Side.blank := by
  unfold C
  iterate 105 tm_step
  tm_finish

/-- **Headline theorem**: machine 494 does not halt from the blank tape.
Composes:
* `bootstrap` — `Cfg2.blank ->* C 1 5 1 blank` (105 concrete steps),
* `C_1b1 5 0 Side.blank` — `C 1 5 1 blank ->* C 10 1 0 blank = D 10 0 blank`,
* `progress_nonhalt_simple` with family `(i, r) ↦ D (a 0) (cc i - c 0) r`
  and step witness `D_next`. -/
theorem no_halt : ¬ halts machine Cfg2.blank := by
  refine multistep_nonhalt (c := D (a 0) (cc 0 - c 0) Side.blank) ?reach ?nonhalt
  · -- Cfg2.blank -[machine]->* D 10 0 Side.blank
    refine Multistep.trans bootstrap ?_
    refine Multistep.trans (C_1b1 5 0 Side.blank) ?_
    tm_finish
  · -- ¬ halts machine (D (a 0) (cc 0 - c 0) Side.blank)
    apply progress_nonhalt_simple
      (C := fun (p : ℕ × Side) => D (a 0) (cc p.1 - c 0) p.2)
      (i₀ := (0, Side.blank))
    rintro ⟨i, r⟩
    obtain ⟨r', H⟩ := D_next i r
    exact ⟨(i + 1, r'), H⟩

end BB33_494
