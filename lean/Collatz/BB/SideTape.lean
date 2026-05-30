import Collatz.BB

/-!
# Side-stream tape model — canonical (Coq/mathlib-style)

Mirrors busycoq's `tape := side * Sym * side` (`verify/TM.v:66`) and
mathlib's `Tape` struct (`Mathlib/Computability/TuringMachine/Tape.lean:408`):
the head cell is stored *explicitly* as a field, with `left` and `right`
being the streams to either side of the head.

This is the canonical representation. An earlier directed encoding
(`(state, dir, left, right)`) was tried — it makes step2 slightly
simpler but breaks identifications like `l <{{q}} r ↔ l {{q}}> r`'s
collapse to the same physical state, which is critical for porting
busycoq's `r20_l12` and similar lemmas where LHS/RHS use opposite
directions over the same tape.

The isomorphism `BB.Cfg ≃ Cfg2` is in `Collatz/BB/Iso.lean`.
-/

namespace BB

/-- A half-tape, indexed inward to outward from the head boundary.
`r 0` is the cell adjacent to the head; `r 1` is the next cell, etc. -/
def Side : Type := ℕ → Sym

namespace Side

/-- The all-blank half-tape. -/
def blank : Side := fun _ => Sym.s0

/-- Prepend a symbol to a half-tape: the new symbol becomes the
closest cell to the head, and the rest shifts outward. -/
def cons (s : Sym) (r : Side) : Side :=
  fun n => match n with
    | 0 => s
    | n + 1 => r n

/-- Drop the closest-to-head cell. -/
def tail (r : Side) : Side := fun n => r (n + 1)

/-- The closest-to-head cell. -/
def head (r : Side) : Sym := r 0

@[simp] theorem head_cons (s : Sym) (r : Side) : head (cons s r) = s := rfl

@[simp] theorem tail_cons (s : Sym) (r : Side) : tail (cons s r) = r := by
  funext n; rfl

@[simp] theorem cons_head_tail (r : Side) : cons (head r) (tail r) = r := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

@[simp] theorem head_blank : head blank = Sym.s0 := rfl

@[simp] theorem tail_blank : tail blank = blank := by funext n; rfl

/-- Prepending the blank symbol to the blank stream is the blank stream.
Not defeq in the `ℕ → Sym` model (would be in a coinductive `Stream`), so
proven by funext + case on `n`. Critical for proofs that end at state A
with one stray `Sym.s0` written into the left side (e.g., `C_0b1`). -/
@[simp] theorem cons_s0_blank : Side.cons Sym.s0 blank = blank := by
  funext n; cases n <;> rfl

end Side

/-- `s >> r` prepends `s` to a side, busycoq-style. -/
infixr:67 " >> " => Side.cons

/-- Prepend `n` copies of a finite list `xs` to a side, with the last copy
(reading the list left-to-right) ending up nearest the head. Models
busycoq's `[s1; s2; ...]^^n *> r`. -/
def repeatList (xs : List Sym) : ℕ → Side → Side
  | 0,     r => r
  | n + 1, r => xs.foldr Side.cons (repeatList xs n r)

namespace Side

@[simp] theorem repeatList_zero (xs : List Sym) (r : Side) :
    repeatList xs 0 r = r := rfl

theorem repeatList_succ (xs : List Sym) (n : ℕ) (r : Side) :
    repeatList xs (n + 1) r = xs.foldr cons (repeatList xs n r) := rfl

@[simp] theorem repeatList_nil (n : ℕ) (r : Side) :
    repeatList [] n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatList_succ]; simp [ih]

/-- `merge_1` (busycoq): `[s]^^n *> s >> r = [s]^^(n+1) *> r`. -/
theorem merge_1 (s : Sym) (n : ℕ) (r : Side) :
    repeatList [s] n (Side.cons s r) = repeatList [s] (n + 1) r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repeatList_succ, repeatList_succ]
      simp only [List.foldr_cons, List.foldr_nil, ih]

/-- `merge_2` (busycoq): `[s1; s2]^^n *> s1 >> s2 >> r = [s1; s2]^^(n+1) *> r`. -/
theorem merge_2 (s1 s2 : Sym) (n : ℕ) (r : Side) :
    repeatList [s1, s2] n (Side.cons s1 (Side.cons s2 r)) =
      repeatList [s1, s2] (n + 1) r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repeatList_succ, repeatList_succ]
      simp only [List.foldr_cons, List.foldr_nil, ih]

/-- `merge_3` (busycoq): same for length-3 blocks. -/
theorem merge_3 (s1 s2 s3 : Sym) (n : ℕ) (r : Side) :
    repeatList [s1, s2, s3] n (Side.cons s1 (Side.cons s2 (Side.cons s3 r))) =
      repeatList [s1, s2, s3] (n + 1) r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repeatList_succ, repeatList_succ]
      simp only [List.foldr_cons, List.foldr_nil, ih]

end Side

/-- A side-stream configuration with explicit head cell.

This matches busycoq's `tape := side * Sym * side` and mathlib's
`Tape Γ := { head : Γ, left : ListBlank Γ, right : ListBlank Γ }`.

`headSym` is the symbol currently being read; `left` and `right` are the
streams to the left and right of the head (NOT including the head cell). -/
@[ext]
structure Cfg2 where
  state : State
  left : Side
  headSym : Sym
  right : Side

namespace Cfg2

/-- Blank start: state A, both sides blank, head reading blank symbol. -/
def blank : Cfg2 := ⟨State.A, Side.blank, Sym.s0, Side.blank⟩

/-- `dirL q l r`: canonical Cfg2 where the head is reading the first cell
of `l` (with `l.tail` as the "rest" of the left side). Mirrors busycoq's
`l <{{q}} r` notation (`l` includes the head cell). -/
def dirL (q : State) (l r : Side) : Cfg2 :=
  ⟨q, l.tail, l.head, r⟩

/-- `dirR q l r`: canonical Cfg2 where the head is reading the first cell
of `r` (with `r.tail` as the "rest" of the right side). Mirrors busycoq's
`l {{q}}> r` notation (`r` includes the head cell). -/
def dirR (q : State) (l r : Side) : Cfg2 :=
  ⟨q, l, r.head, r.tail⟩

@[simp] theorem dirL_cons (q : State) (s : Sym) (l r : Side) :
    dirL q (s >> l) r = ⟨q, l, s, r⟩ := by
  simp [dirL]

@[simp] theorem dirR_cons (q : State) (l : Side) (s : Sym) (r : Side) :
    dirR q l (s >> r) = ⟨q, l, s, r⟩ := by
  simp [dirR]

@[simp] theorem dirL_blank (q : State) (r : Side) :
    dirL q Side.blank r = ⟨q, Side.blank, Sym.s0, r⟩ := by
  simp [dirL]

@[simp] theorem dirR_blank (q : State) (l : Side) :
    dirR q l Side.blank = ⟨q, l, Sym.s0, Side.blank⟩ := by
  simp [dirR]

end Cfg2

/-- One TM step on the canonical side-stream model.

* `t.dir = L`: head moves left. New head cell = old `left.head`; new left
  stream = old `left.tail`; the written symbol joins the right stream.
* `t.dir = R`: head moves right. New head cell = old `right.head`; new
  right stream = old `right.tail`; the written symbol joins the left stream.

Returns `none` exactly when the machine halts at `(c.state, c.headSym)`. -/
def step2 (M : Machine) (c : Cfg2) : Option Cfg2 :=
  (M c.state c.headSym).map fun t =>
    match t.dir with
    | Dir.L => ⟨t.state, c.left.tail, c.left.head, t.write >> c.right⟩
    | Dir.R => ⟨t.state, t.write >> c.left, c.right.head, c.right.tail⟩

/-- `n` steps from `c`, or `none` if the machine halts first. -/
def stepN2 (M : Machine) : ℕ → Cfg2 → Option Cfg2
  | 0,     c => some c
  | n + 1, c => (step2 M c).bind (stepN2 M n)

@[simp] theorem stepN2_zero (M : Machine) (c : Cfg2) : stepN2 M 0 c = some c := rfl

theorem stepN2_succ (M : Machine) (n : ℕ) (c : Cfg2) :
    stepN2 M (n + 1) c = (step2 M c).bind (stepN2 M n) := rfl

end BB
