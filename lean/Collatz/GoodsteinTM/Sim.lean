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

/-- Configuration whose head is the first symbol of `xs`, or the following stop symbol when the
run is empty. -/
def scanRightStart (q : St) (xs : List Sy) (y : Sy) (l r : List Sy) : Cfg St Sy :=
  match xs with
  | [] => ⟨q, l, y, r⟩
  | x :: xs => ⟨q, l, x, xs ++ y :: r⟩

theorem replicate_append_cons_self (n : ℕ) (x : Sy) (r : List Sy) :
    List.replicate n x ++ x :: r = x :: List.replicate n x ++ r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem headD_replicate_self (n : ℕ) (x : Sy) :
    (List.replicate n x).headD x = x := by
  cases n <;> rfl

theorem tail_append_of_ne_nil (xs ys : List Sy) (h : xs ≠ []) :
    (xs ++ ys).tail = xs.tail ++ ys := by
  cases xs with
  | nil => contradiction
  | cons x xs => rfl

theorem headD_append_of_ne_nil (xs ys : List Sy) (h : xs ≠ []) :
    (xs ++ ys).headD default = xs.headD default := by
  cases xs with
  | nil => contradiction
  | cons x xs => rfl

/-- Scan a possibly empty run to the right, then consume a distinguished stop symbol whose
transition also moves right.  Unlike `stepN_scanRight`, this includes the state-changing stop
transition, which is the recurring shape of the comparison loops below. -/
theorem stepN_scanRightUntilRight (M : St → Sy → Option (Sy × Dir × St)) (q q' : St)
    (xs zs : List Sy) (y y' z : Sy) (l r : List Sy)
    (hscan : ∀ a ∈ xs, M q a = some (a, .R, q))
    (hstop : M q y = some (y', .R, q')) :
    stepN M (xs.length + 1)
        (scanRightStart q xs y l (zs ++ z :: r)) =
      some (scanRightStart q' zs z (y' :: xs.reverse ++ l) r) := by
  induction xs generalizing l with
  | nil =>
      change (step M ⟨q, l, y, zs ++ z :: r⟩).bind (stepN M 0) = _
      rw [show step M ⟨q, l, y, zs ++ z :: r⟩ =
          some (scanRightStart q' zs z (y' :: l) r) by
        cases zs <;> simp [scanRightStart, step, Cfg.move, hstop]]
      rfl
  | cons x xs ih =>
      change (step M ⟨q, l, x, xs ++ y :: (zs ++ z :: r)⟩).bind
        (stepN M (xs.length + 1)) = _
      rw [show step M ⟨q, l, x, xs ++ y :: (zs ++ z :: r)⟩ =
          some (scanRightStart q xs y (x :: l) (zs ++ z :: r)) by
        have hx := hscan x (by simp)
        cases xs <;> simp [scanRightStart, step, Cfg.move, hx]]
      simp only [Option.bind_some]
      rw [ih (l := x :: l) (by
        intro a ha
        exact hscan a (by simp [ha]))]
      simp

/-- Right scan through a possibly empty run followed by a stop transition moving left. -/
theorem stepN_scanRightUntilLeft (M : St → Sy → Option (Sy × Dir × St)) (q q' : St)
    (xs : List Sy) (y y' x : Sy) (l r : List Sy)
    (hscan : ∀ a ∈ xs, M q a = some (a, .R, q))
    (hstop : M q y = some (y', .L, q')) :
    stepN M (xs.length + 1)
        (scanRightStart q xs y (x :: l) r) =
      some ⟨q', (xs.reverse ++ x :: l).tail,
        (xs.reverse ++ x :: l).headD default, y' :: r⟩ := by
  induction xs generalizing l x with
  | nil =>
      change (step M ⟨q, x :: l, y, r⟩).bind (stepN M 0) = _
      rw [show step M ⟨q, x :: l, y, r⟩ = some ⟨q', l, x, y' :: r⟩ by
        simp [step, Cfg.move, hstop]]
      rfl
  | cons z zs ih =>
      change (step M ⟨q, x :: l, z, zs ++ y :: r⟩).bind
        (stepN M (zs.length + 1)) = _
      rw [show step M ⟨q, x :: l, z, zs ++ y :: r⟩ =
          some (scanRightStart q zs y (z :: x :: l) r) by
        have hz := hscan z (by simp)
        cases zs <;> simp [scanRightStart, step, Cfg.move, hz]]
      simp only [Option.bind_some]
      rw [ih (x := z) (l := x :: l) (by
        intro a ha
        exact hscan a (by simp [ha]))]
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

/-- One depth-pairing iteration of the candidate/last-node comparison.  The first `i` marks of
each depth have already been changed to `D`; this iteration marks one more on each side and
returns to the first still-unmarked candidate mark (or to `T` when the candidate is exhausted). -/
theorem comparePair_reaches (cells : List Sy) (i a : ℕ) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
        List.replicate a .d ++ .T :: List.replicate i .D ++ .d :: r⟩
      (scanRightStart (.core .CMP_C) (List.replicate a .d) .T
        (List.replicate (i + 1) .D ++ .C :: l) (List.replicate (i + 1) .D ++ r)) := by
  let candLeft := Sy.D :: (List.replicate i Sy.D ++ Sy.C :: l)
  let backRun := List.replicate i Sy.D ++
    (Sy.T :: (List.replicate a Sy.d ++ Sy.D :: List.replicate i Sy.D))
  have hmark :
      Reaches (machine cells)
        ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
          List.replicate a .d ++ .T :: List.replicate i .D ++ .d :: r⟩
        (scanRightStart (.core .CMP_TOL) (List.replicate a .d) .T candLeft
          (List.replicate i .D ++ .d :: r)) := by
    refine ⟨1, ?_⟩
    change (step (machine cells)
      ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
        List.replicate a .d ++ .T :: List.replicate i .D ++ .d :: r⟩).bind
      (stepN (machine cells) 0) = _
    rw [show step (machine cells)
        ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
          List.replicate a .d ++ .T :: List.replicate i .D ++ .d :: r⟩ =
        some ⟨.core .CMP_TOL, .D :: List.replicate i .D ++ .C :: l,
          (List.replicate a Sy.d ++ Sy.T :: List.replicate i Sy.D ++ Sy.d :: r).headD .blank,
          (List.replicate a Sy.d ++ Sy.T :: List.replicate i Sy.D ++ Sy.d :: r).tail⟩ by
      simp only [step]
      rw [show machine cells (.core .CMP_C) .d = some (.D, .R, .core .CMP_TOL) by rfl]
      rfl]
    simp only [Option.bind_some, stepN]
    cases a <;> simp [scanRightStart, candLeft, List.replicate_succ,
      List.append_assoc]
  have htoLeaf :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_TOL) (List.replicate a .d) .T candLeft
          (List.replicate i .D ++ .d :: r))
        (scanRightStart (.core .CMP_L) (List.replicate i .D) .d
          (.T :: List.replicate a .d ++ candLeft) r) := by
    refine reaches_of_stepN (n := a + 1) ?_
    simpa [candLeft, List.reverse_replicate, List.append_assoc] using
      (stepN_scanRightUntilRight (machine cells) (.core .CMP_TOL) (.core .CMP_L)
        (List.replicate a .d) (List.replicate i .D) .T .T .d candLeft r
        (by
          intro x hx
          have : x = Sy.d := (List.mem_replicate.mp hx).2
          subst x
          rfl)
        (by rfl))
  have hmarkLeaf :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_L) (List.replicate i .D) .d
          (.T :: List.replicate a .d ++ candLeft) r)
        ⟨.core .CMP_TOC, backRun.tail ++ .C :: l, backRun.headD .blank, .D :: r⟩ := by
    refine reaches_of_stepN (n := i + 1) ?_
    have hne : backRun ≠ [] := by simp [backRun]
    have htail := tail_append_of_ne_nil backRun (Sy.C :: l) hne
    have hhead := headD_append_of_ne_nil backRun (Sy.C :: l) hne
    have hwhole :
        List.replicate i Sy.D ++ Sy.T :: (List.replicate a Sy.d ++ candLeft) =
          backRun ++ Sy.C :: l := by
      simp [backRun, candLeft, List.append_assoc]
    have h :=
      stepN_scanRightUntilLeft (machine cells) (.core .CMP_L) (.core .CMP_TOC)
        (List.replicate i .D) .d .D .T
        (List.replicate a .d ++ candLeft) r
        (by
          intro x hx
          have : x = Sy.D := (List.mem_replicate.mp hx).2
          subst x
          rfl)
        (by rfl)
    simp only [List.reverse_replicate] at h
    rw [hwhole, htail, hhead] at h
    simpa only [List.length_replicate, List.cons_append,
      show (default : Sy) = Sy.blank by rfl] using h
  have hback :
      Reaches (machine cells)
        ⟨.core .CMP_TOC, backRun.tail ++ .C :: l, backRun.headD .blank, .D :: r⟩
        ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩ := by
    refine reaches_of_stepN (n := backRun.tail.length + 1) ?_
    have hne : backRun ≠ [] := by simp [backRun]
    have hcons : backRun.headD Sy.blank :: backRun.tail = backRun := by
      cases h : backRun with
      | nil => exact (hne h).elim
      | cons x xs => rfl
    have hscan := stepN_scanLeft (machine cells) (.core .CMP_TOC)
      (backRun.headD Sy.blank) backRun.tail (.C :: l) (.D :: r) (by
        intro x hx
        have hx' : x ∈ backRun := by
          rw [← hcons]
          exact hx
        have hxCases : x = Sy.D ∨ x = Sy.T ∨ x = Sy.d := by
          dsimp [backRun] at hx'
          rw [List.mem_append] at hx'
          rcases hx' with hi | hx'
          · exact .inl (List.mem_replicate.mp hi).2
          · rcases List.mem_cons.mp hx' with rfl | hx'
            · exact .inr (.inl rfl)
            · rw [List.mem_append] at hx'
              rcases hx' with ha | hx'
              · exact .inr (.inr (List.mem_replicate.mp ha).2)
              · rcases List.mem_cons.mp hx' with rfl | hi
                · exact .inl rfl
                · exact .inl (List.mem_replicate.mp hi).2
        rcases hxCases with rfl | rfl | rfl <;> rfl)
    simpa only [List.tail_cons, List.headD_cons, hcons] using hscan
  have hreturn :
      Reaches (machine cells)
        ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩
        (scanRightStart (.core .CMP_C) (List.replicate a .d) .T
          candLeft (.D :: List.replicate i .D ++ r)) := by
    refine reaches_of_stepN (n := i + 2) ?_
    have hscan := stepN_scanRight (machine cells) (.core .CMP_C) Sy.D
      (List.replicate i .D) (.C :: l)
      (List.replicate a .d ++ .T :: .D :: List.replicate i .D ++ r) (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · have : x = Sy.D := (List.mem_replicate.mp hx).2
          subst x
          rfl)
    rw [show i + 2 = 1 + (i + 1) by omega, stepN_add]
    rw [show stepN (machine cells) 1
        ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩ =
          some ⟨.core .CMP_C, .C :: l, .D,
            List.replicate i .D ++ List.replicate a .d ++ .T ::
              .D :: List.replicate i .D ++ r⟩ by
      change (step (machine cells)
        ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩).bind
          (stepN (machine cells) 0) = _
      rw [show step (machine cells)
          ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩ =
          some ⟨.core .CMP_C, .C :: l, .D,
            List.replicate i .D ++ List.replicate a .d ++ .T ::
              .D :: List.replicate i .D ++ r⟩ by
        simp only [step]
        rw [show machine cells (.core .CMP_TOC) .C = some (.C, .R, .core .CMP_C) by rfl]
        simp [Cfg.move, backRun, List.reverse_append, List.reverse_replicate,
          replicate_append_cons_self, headD_replicate_self, List.append_assoc]]
      rfl]
    simp only [Option.bind_some]
    rw [show stepN (machine cells) (i + 1)
        ⟨.core .CMP_C, .C :: l, .D,
          List.replicate i .D ++ List.replicate a .d ++ .T ::
            .D :: List.replicate i .D ++ r⟩ =
        some ⟨.core .CMP_C, (Sy.D :: List.replicate i .D).reverse ++ .C :: l,
          (List.replicate a Sy.d ++ Sy.T :: Sy.D :: List.replicate i Sy.D ++ r).headD default,
          (List.replicate a Sy.d ++ Sy.T :: Sy.D :: List.replicate i Sy.D ++ r).tail⟩ by
      simpa [replicate_append_cons_self, headD_replicate_self,
        List.append_assoc] using hscan]
    cases a <;> simp [scanRightStart, candLeft, List.replicate_succ,
      replicate_append_cons_self, headD_replicate_self, List.append_assoc]
  simpa [candLeft, List.replicate_succ] using
    (reaches_trans hmark (reaches_trans htoLeaf
      (reaches_trans hmarkLeaf (reaches_trans hback hreturn))))

/-- Iterating `comparePair_reaches` consumes the candidate's whole positive depth and the same
number of marks on the last node. -/
theorem comparePairs_reaches_exhausted (cells : List Sy) (i a : ℕ) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
        List.replicate a .d ++ .T :: List.replicate i .D ++
          List.replicate (a + 1) .d ++ r⟩
      ⟨.core .CMP_C, List.replicate (i + a + 1) .D ++ .C :: l, .T,
        List.replicate (i + a + 1) .D ++ r⟩ := by
  induction a generalizing i with
  | zero =>
      simpa [scanRightStart, List.replicate_succ, List.append_assoc] using
        (comparePair_reaches cells i 0 l r)
  | succ a ih =>
      have hpair := comparePair_reaches cells i (a + 1) l
        (List.replicate (a + 1) Sy.d ++ r)
      have hrest := ih (i + 1)
      have hpair' :
          Reaches (machine cells)
            ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
              List.replicate (a + 1) .d ++ .T :: List.replicate i .D ++
                List.replicate (a + 2) .d ++ r⟩
            ⟨.core .CMP_C, List.replicate (i + 1) .D ++ .C :: l, .d,
              List.replicate a .d ++ .T :: List.replicate (i + 1) .D ++
                List.replicate (a + 1) .d ++ r⟩ := by
        simpa [scanRightStart, List.replicate_succ, replicate_append_cons_self,
          List.append_assoc] using hpair
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (reaches_trans hpair' hrest)

/-- Once all candidate depth marks are paired, `CMP_CEXH/CMP_LCHK` recognizes one remaining
last-node mark and enters the parent-found state. -/
theorem compareExhausted_reaches_parent (cells : List Sy) (a : ℕ) (x : Sy)
    (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, List.replicate (a + 1) .D ++ .C :: l, .T,
        List.replicate (a + 1) .D ++ .d :: x :: r⟩
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T ::
          List.replicate (a + 1) .D ++ .C :: l,
        x, r⟩ := by
  have henter :
      stepN (machine cells) 3
        ⟨.core .CMP_C, List.replicate (a + 1) .D ++ .C :: l, .T,
          List.replicate (a + 1) .D ++ .d :: x :: r⟩ =
        some ⟨.core .CMP_LCHK,
          .T :: List.replicate (a + 1) .D ++ .C :: l, .D,
          List.replicate a .D ++ .d :: x :: r⟩ := by
    cases a <;> rfl
  have hcheck := stepN_scanRightUntilRight (machine cells)
    (.core .CMP_LCHK) (.core .PAR_END) (List.replicate (a + 1) .D) []
    .d .d x (.T :: List.replicate (a + 1) .D ++ .C :: l) r
    (by
      intro y hy
      have : y = Sy.D := (List.mem_replicate.mp hy).2
      subst y
      rfl)
    (by rfl)
  have hcheck' :
      Reaches (machine cells)
        ⟨.core .CMP_LCHK,
          .T :: List.replicate (a + 1) .D ++ .C :: l, .D,
          List.replicate a .D ++ .d :: x :: r⟩
        ⟨.core .PAR_END,
          .d :: List.replicate (a + 1) .D ++ .T ::
            List.replicate (a + 1) .D ++ .C :: l,
          x, r⟩ := by
    refine reaches_of_stepN (n := (a + 1) + 1) ?_
    simpa [scanRightStart, List.reverse_replicate, List.replicate_succ,
      replicate_append_cons_self, List.append_assoc] using hcheck
  exact reaches_trans (reaches_of_stepN henter) hcheck'

/-- A candidate whose depth is exactly one below the last node is recognized as its parent. -/
theorem compareParent_reaches (cells : List Sy) (a : ℕ) (x : Sy) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, .C :: l, .d,
        List.replicate a .d ++ .T :: List.replicate (a + 2) .d ++ x :: r⟩
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T ::
          List.replicate (a + 1) .D ++ .C :: l,
        x, r⟩ := by
  have hpairs := comparePairs_reaches_exhausted cells 0 a l (.d :: x :: r)
  have hfound := compareExhausted_reaches_parent cells a x l r
  have hfound' :
      Reaches (machine cells)
        ⟨.core .CMP_C, List.replicate (0 + a + 1) .D ++ .C :: l, .T,
          List.replicate (0 + a + 1) .D ++ .d :: x :: r⟩
        ⟨.core .PAR_END,
          .d :: List.replicate (a + 1) .D ++ .T ::
            List.replicate (a + 1) .D ++ .C :: l,
          x, r⟩ := by
    simpa using hfound
  simpa [List.replicate_succ, replicate_append_cons_self,
    List.append_assoc] using reaches_trans hpairs hfound'

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
