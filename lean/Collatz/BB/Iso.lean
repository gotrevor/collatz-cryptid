import Collatz.BB
import Collatz.BB.SideTape
import Collatz.BB.Multistep

/-!
# Isomorphism between `BB.Cfg` (ℤ→Sym tape) and `Cfg2` (side-stream tape)

Conversion functions in both directions, plus the blank-config lemma.

The step-preservation lemma `step_toSide` is **deferred**: it's not on the
critical path to Phase 1 (porting BB33_494), which starts from a fresh
blank tape. It will be needed in Phase 2 / 3, when we want to reuse the
existing `Encoding.bootstrap_full` (proved on `ℤ → Sym`) as the
prefix of a `Cfg2`-side proof.
-/

namespace BB

/-- Convert a `BB.Cfg` (`ℤ → Sym` tape) to a `Cfg2` (canonical
side-stream tape with explicit head cell).

* `headSym = c.tape c.pos` — the cell currently under the head.
* `left n = c.tape (c.pos - (n + 1))` — left[0] is immediately left of head.
* `right n = c.tape (c.pos + (n + 1))` — right[0] is immediately right of head.
-/
def Cfg.toSide (c : Cfg) : Cfg2 where
  state := c.state
  left := fun n => c.tape (c.pos - (n + 1 : ℕ))
  headSym := c.tape c.pos
  right := fun n => c.tape (c.pos + (n + 1 : ℕ))

/-- Convert a `Cfg2` back to a `BB.Cfg`, placing the head at position 0. -/
def Cfg2.toCfg (c : Cfg2) : Cfg where
  state := c.state
  tape := fun i =>
    if i = 0 then c.headSym
    else if i > 0 then c.right (i - 1).toNat
    else c.left (-i - 1).toNat
  pos := 0

/-- Convert with the head at an explicit position. -/
def Cfg2.toCfgAt (c : Cfg2) (pos : ℤ) : Cfg where
  state := c.state
  tape := fun i =>
    if i = pos then c.headSym
    else if i > pos then c.right (i - pos - 1).toNat
    else c.left (pos - i - 1).toNat
  pos := pos

/-- The side-stream step agrees with the `ℤ→Sym` step under `Cfg.toSide`.
Case split on the transition, then on direction; equality of `Cfg2` is
established componentwise. The left/right sides match because
`Tape.write` only changes position `c.pos`, and the new head's view of
its neighborhood is a one-cell shift of the old view. -/
theorem step_toSide (M : Machine) (c : Cfg) :
    step2 M (Cfg.toSide c) = (step M c).map Cfg.toSide := by
  unfold step step2 Cfg.toSide
  show (M c.state (c.tape c.pos)).map _ =
    ((M c.state (c.tape.read c.pos)).map _).map _
  rw [Tape.read]
  cases hM : M c.state (c.tape c.pos) with
  | none => simp
  | some t =>
    simp only [Option.map_some]
    congr 1
    unfold Side.tail Side.head Side.cons Tape.write
    cases hd : t.dir with
    | L =>
      simp only [hd, shift]
      refine Cfg2.ext rfl ?_ ?_ ?_
      · -- left
        funext n; dsimp only; push_cast
        have hne : c.pos - 1 - ((n : ℤ) + 1) ≠ c.pos := by omega
        have heq : c.pos - 1 - ((n : ℤ) + 1) = c.pos - (((n : ℤ) + 1) + 1) := by ring
        rw [if_neg hne]; exact (congrArg c.tape heq).symm
      · -- headSym
        dsimp only
        have hne : c.pos - 1 ≠ c.pos := by omega
        push_cast
        -- `push_cast` rewrites the ite's proposition but leaves the stale Decidable
        -- instance, so `rw [if_neg hne]` can't match; term-mode unification can.
        exact (if_neg hne).symm
      · -- right
        funext n; dsimp only
        cases n with
        | zero =>
          push_cast
          simp
        | succ k =>
          push_cast
          have heq : c.pos - 1 + (((k : ℤ) + 1) + 1) = c.pos + ((k : ℤ) + 1) := by ring
          have hne : c.pos + ((k : ℤ) + 1) ≠ c.pos := by omega
          rw [heq, if_neg hne]
    | R =>
      simp only [hd, shift]
      refine Cfg2.ext rfl ?_ ?_ ?_
      · -- left
        funext n; dsimp only
        cases n with
        | zero =>
          push_cast
          simp
        | succ k =>
          push_cast
          have heq : c.pos + 1 - (((k : ℤ) + 1) + 1) = c.pos - ((k : ℤ) + 1) := by ring
          have hne : c.pos - ((k : ℤ) + 1) ≠ c.pos := by omega
          rw [heq, if_neg hne]
      · -- headSym
        dsimp only
        have hne : c.pos + 1 ≠ c.pos := by omega
        push_cast
        exact (if_neg hne).symm
      · -- right
        funext n; dsimp only; push_cast
        have hne : c.pos + 1 + ((n : ℤ) + 1) ≠ c.pos := by omega
        have heq : c.pos + (((n : ℤ) + 1) + 1) = c.pos + 1 + ((n : ℤ) + 1) := by ring
        rw [if_neg hne, heq]

/-- The blank `BB.Cfg` corresponds to the blank `Cfg2`. -/
@[simp] theorem Cfg.toSide_blank : Cfg.toSide Cfg.blank = Cfg2.blank := by
  apply Cfg2.ext <;> rfl

/-- "Step first" form of `stepN`. Mirrors `stepN2_succ`'s shape. -/
theorem stepN_step_first (M : Machine) (n : ℕ) (c : Cfg) :
    stepN M (n + 1) c = (step M c).bind (stepN M n) := by
  induction n generalizing c with
  | zero =>
      change (stepN M 0 c).bind (step M) = (step M c).bind (stepN M 0)
      change (some c).bind (step M) = (step M c).bind (fun c' => some c')
      simp
  | succ n ih =>
      change (stepN M (n + 1) c).bind (step M) =
        (step M c).bind (stepN M (n + 1))
      rw [ih c]
      cases hs : step M c with
      | none => simp
      | some c' =>
          simp only [Option.bind_some]
          rfl

/-- The `n`-step generalisation of `step_toSide`. Useful for lifting any
already-proved `BB.stepN M n c = some c'` (e.g. Bigfoot's 69-step
bootstrap) into the `Cfg2` world. -/
theorem stepN_toSide (M : Machine) (n : ℕ) (c : Cfg) :
    stepN2 M n (Cfg.toSide c) = (stepN M n c).map Cfg.toSide := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [stepN2_succ, step_toSide, stepN_step_first]
      cases hs : step M c with
      | none => simp
      | some c' =>
          simp only [Option.map_some, Option.bind_some]
          exact ih c'

/-- Packaged: if the ℤ-tape machine reaches `c'` in `n` steps, the
side-tape machine reaches `Cfg.toSide c'` in `n` steps. Direct
substitution into `stepN_toSide`. -/
theorem stepN2_of_stepN_toSide {M : Machine} {n : ℕ} {c c' : Cfg}
    (h : stepN M n c = some c') :
    stepN2 M n (Cfg.toSide c) = some (Cfg.toSide c') := by
  rw [stepN_toSide, h]; rfl

/-- Promoted to `Multistep`: if `BB.stepN M n c = some c'`, then `Cfg.toSide c`
reaches `Cfg.toSide c'` in the relational view used by the busycoq-style
tactics. -/
theorem multistep_toSide {M : Machine} {n : ℕ} {c c' : Cfg}
    (h : stepN M n c = some c') :
    Multistep M (Cfg.toSide c) (Cfg.toSide c') :=
  stepN_to_multistep (stepN2_of_stepN_toSide h)

end BB
