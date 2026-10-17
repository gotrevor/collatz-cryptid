/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.GoodsteinTM.HydraTree

/-!
# Tape encodings for the Goodstein machine simulation

The simulation is anchored at `CHOP_START`, with the head scanning the final cell of the encoded
tree and an arbitrary finite tail of explicit blanks to its right.  The empty tree is a genuine
edge case of the frozen headline theorem: it reaches `CHOP_START` on the right bracket and halts
immediately because that table entry is undefined.
-/

namespace GoodsteinTM

/-- Step composition: first run `m` steps, then run another `n` steps from the result. -/
theorem stepN_add (M : St → Sy → Option (Sy × Dir × St)) (m n : ℕ) (c : Cfg St Sy) :
    stepN M (m + n) c = (stepN M m c).bind (stepN M n) := by
  induction m generalizing c with
  | zero => simp [stepN]
  | succ m ih =>
      rw [Nat.succ_add]
      change (step M c).bind (stepN M (m + n)) =
        ((step M c).bind (stepN M m)).bind (stepN M n)
      cases h : step M c with
      | none => rfl
      | some c' => simpa using ih c'

/-- Existential finite reachability for composing machine segments without tracking their costs. -/
def Reaches (M : St → Sy → Option (Sy × Dir × St))
    (c c' : Cfg St Sy) : Prop :=
  ∃ n, stepN M n c = some c'

theorem reaches_refl (M : St → Sy → Option (Sy × Dir × St)) (c : Cfg St Sy) :
    Reaches M c c :=
  ⟨0, rfl⟩

theorem reaches_trans {M : St → Sy → Option (Sy × Dir × St)} {c₁ c₂ c₃ : Cfg St Sy}
    (h₁₂ : Reaches M c₁ c₂) (h₂₃ : Reaches M c₂ c₃) : Reaches M c₁ c₃ := by
  obtain ⟨m, hm⟩ := h₁₂
  obtain ⟨n, hn⟩ := h₂₃
  refine ⟨m + n, ?_⟩
  rw [stepN_add, hm]
  exact hn

theorem reaches_of_stepN {M : St → Sy → Option (Sy × Dir × St)} {n : ℕ}
    {c c' : Cfg St Sy} (h : stepN M n c = some c') : Reaches M c c' :=
  ⟨n, h⟩

/-- A left-moving scan over a nonempty run, written as its current symbol followed by the
remaining symbols, stops on the first cell to the run's left. -/
theorem stepN_scanLeft (M : St → Sy → Option (Sy × Dir × St)) (q : St)
    (x : Sy) (xs l r : List Sy)
    (hscan : ∀ a ∈ x :: xs, M q a = some (a, .L, q)) :
    stepN M (xs.length + 1) ⟨q, xs ++ l, x, r⟩ =
      some ⟨q, l.tail, l.headD default, (x :: xs).reverse ++ r⟩ := by
  induction xs generalizing x r with
  | nil =>
      simp [stepN, step, Cfg.move, hscan]
  | cons a as ih =>
      change (step M ⟨q, a :: (as ++ l), x, r⟩).bind (stepN M (as.length + 1)) = _
      rw [show step M ⟨q, a :: (as ++ l), x, r⟩ =
          some ⟨q, as ++ l, a, x :: r⟩ by simp [step, Cfg.move, hscan]]
      simp only [Option.bind_some]
      rw [ih a (x :: r) (by
        intro w hw
        exact hscan w (by simp only [List.mem_cons] at hw ⊢; tauto))]
      simp

/-- Right-moving counterpart of `stepN_scanLeft`. -/
theorem stepN_scanRight (M : St → Sy → Option (Sy × Dir × St)) (q : St)
    (x : Sy) (xs l r : List Sy)
    (hscan : ∀ a ∈ x :: xs, M q a = some (a, .R, q)) :
    stepN M (xs.length + 1) ⟨q, l, x, xs ++ r⟩ =
      some ⟨q, (x :: xs).reverse ++ l, r.headD default, r.tail⟩ := by
  induction xs generalizing x l with
  | nil =>
      simp [stepN, step, Cfg.move, hscan]
  | cons a as ih =>
      change (step M ⟨q, l, x, a :: (as ++ r)⟩).bind (stepN M (as.length + 1)) = _
      rw [show step M ⟨q, l, x, a :: (as ++ r)⟩ =
          some ⟨q, x :: l, a, as ++ r⟩ by simp [step, Cfg.move, hscan]]
      simp only [Option.bind_some]
      rw [ih a (x :: l) (by
        intro w hw
        exact hscan w (by simp only [List.mem_cons] at hw ⊢; tauto))]
      simp

/-- A `CHOP_FINDL` configuration with `m` depth marks still between the head and the final
node marker.  The separate definition makes the zero-mark boundary exact rather than padding the
tape with a fictitious cell. -/
def chopFindConfig (m : ℕ) (l r : List Sy) : Cfg St Sy :=
  match m with
  | 0 => ⟨.core .CHOP_FINDL, l, .P, r⟩
  | m + 1 => ⟨.core .CHOP_FINDL, List.replicate m .d ++ .P :: l, .d, r⟩

/-- `CHOP_FINDL` crosses the rest of the final node's depth, marks its `P` as `T`, and leaves the
head one cell to its left for `CAND_FIND`. -/
theorem chopFind_reaches_candidate (cells : List Sy) (m : ℕ) (l r : List Sy) :
    stepN (machine cells) (m + 1) (chopFindConfig m l r) =
      some ⟨.core .CAND_FIND, l.tail, l.headD .blank, .T :: List.replicate m .d ++ r⟩ := by
  induction m generalizing r with
  | zero =>
      rfl
  | succ m ih =>
      change (step (machine cells) (chopFindConfig (m + 1) l r)).bind
        (stepN (machine cells) (m + 1)) = _
      rw [show step (machine cells) (chopFindConfig (m + 1) l r) =
          some (chopFindConfig m l (.d :: r)) by cases m <;> rfl]
      simp only [Option.bind_some]
      rw [ih (.d :: r)]
      rw [List.replicate_succ']
      simp [List.append_assoc]

/-- `CAND_FIND` crosses one positive-depth candidate node, marks its `P` as `C`, and begins the
depth comparison at the candidate's first `d`. -/
theorem candidateFind_reaches_compare (cells : List Sy) (m : ℕ) (l r : List Sy) :
    stepN (machine cells) (m + 2)
        ⟨.core .CAND_FIND, List.replicate m .d ++ .P :: l, .d, r⟩ =
      some ⟨.core .CMP_C, .C :: l, .d, List.replicate m .d ++ r⟩ := by
  have hscan :
      stepN (machine cells) (m + 1)
          ⟨.core .CAND_FIND, List.replicate m .d ++ .P :: l, .d, r⟩ =
        some ⟨.core .CAND_FIND, l, .P, List.replicate (m + 1) .d ++ r⟩ := by
    simpa [List.replicate_succ'] using
      (stepN_scanLeft (machine cells) (.core .CAND_FIND) .d
        (List.replicate m .d) (.P :: l) r (by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · rfl
          · have had : a = .d := (List.mem_replicate.mp ha).2
            subst a
            rfl))
  rw [show m + 2 = (m + 1) + 1 by omega, stepN_add, hscan]
  rfl

/-- For a final node of depth `m + 2`, the `CHOP_START`, `CHOP_D1`, and `CHOP_FINDL`
segments together mark that node and enter `CAND_FIND`. -/
theorem chopStart_reaches_candidate (cells : List Sy) (m : ℕ) (l r : List Sy) :
    stepN (machine cells) (m + 3)
        ⟨.core .CHOP_START, List.replicate (m + 1) .d ++ .P :: l, .d, r⟩ =
      some ⟨.core .CAND_FIND, l.tail, l.headD .blank,
        .T :: List.replicate (m + 2) .d ++ r⟩ := by
  have hstart :
      stepN (machine cells) 2
          ⟨.core .CHOP_START, List.replicate (m + 1) .d ++ .P :: l, .d, r⟩ =
        some (chopFindConfig m l (.d :: .d :: r)) := by
    cases m <;> rfl
  rw [show m + 3 = 2 + (m + 1) by omega, stepN_add, hstart,
    Option.bind_some, chopFind_reaches_candidate]
  simp only [List.replicate_succ']
  simp [List.append_assoc]

/-- The first two search segments put any positive-depth candidate and a final node of depth at
least two into the canonical `CMP_C` layout. -/
theorem chopStart_reaches_compare (cells : List Sy) (m a : ℕ) (l r : List Sy) :
    Reaches (machine cells)
        ⟨.core .CHOP_START,
          List.replicate (m + 1) .d ++ .P :: List.replicate (a + 1) .d ++ .P :: l,
          .d, r⟩
        ⟨.core .CMP_C, .C :: l, .d,
          List.replicate a .d ++ .T :: List.replicate (m + 2) .d ++ r⟩ := by
  have hfirst := reaches_of_stepN (chopStart_reaches_candidate cells m
    (List.replicate (a + 1) Sy.d ++ Sy.P :: l) r)
  have htail : (List.replicate (a + 1) Sy.d ++ Sy.P :: l).tail =
      List.replicate a Sy.d ++ Sy.P :: l := by
    rw [List.replicate_succ]
    rfl
  have hhead : (List.replicate (a + 1) Sy.d ++ Sy.P :: l).headD Sy.blank = Sy.d := by
    rw [List.replicate_succ]
    rfl
  rw [htail, hhead] at hfirst
  simpa [List.append_assoc] using
    (reaches_trans hfirst (reaches_of_stepN (candidateFind_reaches_compare cells a l
      (Sy.T :: List.replicate (m + 2) Sy.d ++ r))))

/-- The `P d^k` work-region encoding of a level sequence. -/
def treeCells (t : List ℕ) : List Sy :=
  t.flatMap fun k => .P :: List.replicate k .d

/-- The complete finite nonblank tape segment at the start of a chop. -/
def tapeCells (b : ℕ) (t : List ℕ) : List Sy :=
  List.replicate b .b ++ [.lb, .rb] ++ treeCells t

/-- Configuration entering `CHOP_START`.  `j` explicit blanks represent an arbitrary finite
portion of the infinite blank tail. -/
def chopConfig (b : ℕ) (t : List ℕ) (j : ℕ) : Cfg St Sy :=
  let tape := tapeCells b t
  ⟨.core .CHOP_START, tape.dropLast.reverse, tape.getLastD .blank,
    List.replicate j .blank⟩

theorem cellsOf_eq_tapeCells_two (t : List ℕ) : cellsOf t = tapeCells 2 t := by
  simp [cellsOf, tapeCells, treeCells]

/-- The empty well-formed seed reaches the undefined `CHOP_START`/`]` entry after 13 steps. -/
theorem empty_halts : Halts (machine (cellsOf [])) start := by
  refine ⟨13, chopConfig 3 [] 1, ?_, ?_⟩ <;> decide +kernel

end GoodsteinTM
