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

/-- A generated stay move is represented by a right move followed by a left move.  When the
right-hand cell is explicit, those two physical moves restore the tape representation exactly. -/
theorem stepN_rightLeft (M : St → Sy → Option (Sy × Dir × St))
    (q qBack q' : St) (x y : Sy) (l r : List Sy)
    (hgo : M q x = some (x, .R, qBack))
    (hback : M qBack y = some (y, .L, q')) :
    stepN M 2 ⟨q, l, x, y :: r⟩ = some ⟨q', l, x, y :: r⟩ := by
  simp [stepN, step, Cfg.move, hgo, hback]

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

/-- A left-moving scan that rewrites each crossed symbol with `f`. -/
theorem stepN_scanLeftMap (M : St → Sy → Option (Sy × Dir × St)) (q : St)
    (f : Sy → Sy) (x : Sy) (xs l r : List Sy)
    (hscan : ∀ a ∈ x :: xs, M q a = some (f a, .L, q)) :
    stepN M (xs.length + 1) ⟨q, xs ++ l, x, r⟩ =
      some ⟨q, l.tail, l.headD default, ((x :: xs).map f).reverse ++ r⟩ := by
  induction xs generalizing x r with
  | nil =>
      simp [stepN, step, Cfg.move, hscan]
  | cons a as ih =>
      change (step M ⟨q, a :: (as ++ l), x, r⟩).bind (stepN M (as.length + 1)) = _
      rw [show step M ⟨q, a :: (as ++ l), x, r⟩ =
          some ⟨q, as ++ l, a, f x :: r⟩ by simp [step, Cfg.move, hscan]]
      simp only [Option.bind_some]
      rw [ih a (f x :: r) (by
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

theorem scanRightStart_eq (q : St) (xs : List Sy) (y : Sy) (l r : List Sy) :
    scanRightStart q xs y l r =
      ⟨q, l, (xs ++ y :: r).headD default, (xs ++ y :: r).tail⟩ := by
  cases xs <;> rfl

theorem replicate_append_cons_self (n : ℕ) (x : Sy) (r : List Sy) :
    List.replicate n x ++ x :: r = x :: List.replicate n x ++ r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem two_cons_replicate_append (n : ℕ) (x : Sy) (r : List Sy) :
    x :: x :: (List.replicate n x ++ r) = List.replicate (n + 2) x ++ r := by
  rw [show n + 2 = 2 + n by omega, List.replicate_add]
  rfl

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

/-- The `P d^k` work-region encoding of a level sequence. -/
def treeCells (t : List ℕ) : List Sy :=
  t.flatMap fun k => .P :: List.replicate k .d

@[simp] theorem treeCells_nil : treeCells [] = [] := rfl

@[simp] theorem treeCells_cons (k : ℕ) (t : List ℕ) :
    treeCells (k :: t) = .P :: List.replicate k .d ++ treeCells t := rfl

/-- Unmarked encoded tree cells contain only node markers and depth marks. -/
theorem mem_treeCells {t : List ℕ} {x : Sy} (hx : x ∈ treeCells t) :
    x = .P ∨ x = .d := by
  induction t with
  | nil => simp at hx
  | cons k t ih =>
      simp only [treeCells_cons, List.mem_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · rcases hx with rfl | hx
        · exact .inl rfl
        · exact .inr (List.mem_replicate.mp hx).2
      · exact ih hx

/-- Restore a comparison mark; all other symbols are unchanged. -/
def restoreD : Sy → Sy
  | .D => .d
  | x => x

@[simp] theorem map_restoreD_treeCells (t : List ℕ) :
    (treeCells t).map restoreD = treeCells t := by
  induction t with
  | nil => rfl
  | cons k t ih => simp [treeCells_cons, restoreD, ih]

/-- `NOTPARENT` crosses the marked comparison region, restores every `D`, changes the candidate
marker `C` back to `P`, and resumes the leftward candidate search. -/
theorem notParent_reaches_candidate (cells : List Sy) (x : Sy) (xs l r : List Sy)
    (hsafe : ∀ y ∈ x :: xs, y = .D ∨ y = .T ∨ y = .P ∨ y = .d) :
    Reaches (machine cells)
      ⟨.core .NOTPARENT, xs ++ .C :: l, x, r⟩
      ⟨.core .CAND_FIND, l.tail, l.headD .blank,
        .P :: ((x :: xs).map restoreD).reverse ++ r⟩ := by
  have hscan := stepN_scanLeftMap (machine cells) (.core .NOTPARENT) restoreD
    x xs (.C :: l) r (by
      intro y hy
      rcases hsafe y hy with rfl | rfl | rfl | rfl <;> rfl)
  have hscan' :
      stepN (machine cells) (xs.length + 1)
          ⟨.core .NOTPARENT, xs ++ .C :: l, x, r⟩ =
        some ⟨.core .NOTPARENT, l, .C, ((x :: xs).map restoreD).reverse ++ r⟩ := by
    simpa using hscan
  refine ⟨xs.length + 2, ?_⟩
  rw [show xs.length + 2 = (xs.length + 1) + 1 by omega, stepN_add, hscan']
  rfl

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

/-- One comparison pairing with an already-rejected encoded node segment between the candidate
and the marked last node.  This is the form needed after `NOTPARENT` retries farther left: the
comparison scans through `middle` in both directions without changing it. -/
theorem comparePairThrough_reaches (cells : List Sy) (i a : ℕ)
    (middle l r : List Sy)
    (hmiddle : ∀ x ∈ middle, x = .P ∨ x = .d) :
    Reaches (machine cells)
      ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
        List.replicate a .d ++ middle ++ .T :: List.replicate i .D ++ .d :: r⟩
      (scanRightStart (.core .CMP_C) (List.replicate a .d ++ middle) .T
        (List.replicate (i + 1) .D ++ .C :: l) (List.replicate (i + 1) .D ++ r)) := by
  let frontRun := List.replicate a Sy.d ++ middle
  let candLeft := Sy.D :: (List.replicate i Sy.D ++ Sy.C :: l)
  let backRun := List.replicate i Sy.D ++
    (Sy.T :: (frontRun.reverse ++ Sy.D :: List.replicate i Sy.D))
  have hfront : ∀ x ∈ frontRun, x = Sy.P ∨ x = Sy.d := by
    intro x hx
    rw [show frontRun = List.replicate a Sy.d ++ middle by rfl,
      List.mem_append] at hx
    rcases hx with hx | hx
    · exact .inr (List.mem_replicate.mp hx).2
    · exact hmiddle x hx
  have hmark :
      Reaches (machine cells)
        ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
          frontRun ++ .T :: List.replicate i .D ++ .d :: r⟩
        (scanRightStart (.core .CMP_TOL) frontRun .T candLeft
          (List.replicate i .D ++ .d :: r)) := by
    refine ⟨1, ?_⟩
    change (step (machine cells)
      ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
        frontRun ++ .T :: List.replicate i .D ++ .d :: r⟩).bind
      (stepN (machine cells) 0) = _
    rw [show step (machine cells)
        ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
          frontRun ++ .T :: List.replicate i .D ++ .d :: r⟩ =
        some (scanRightStart (.core .CMP_TOL) frontRun .T candLeft
          (List.replicate i .D ++ .d :: r)) by
      simp only [step]
      rw [show machine cells (.core .CMP_C) .d = some (.D, .R, .core .CMP_TOL) by rfl]
      simp [Cfg.move, scanRightStart_eq, candLeft, List.append_assoc]]
    rfl
  have htoLeaf :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_TOL) frontRun .T candLeft
          (List.replicate i .D ++ .d :: r))
        (scanRightStart (.core .CMP_L) (List.replicate i .D) .d
          (.T :: frontRun.reverse ++ candLeft) r) := by
    apply reaches_of_stepN
    exact stepN_scanRightUntilRight (machine cells) (.core .CMP_TOL) (.core .CMP_L)
      frontRun (List.replicate i .D) .T .T .d candLeft r
      (by
        intro x hx
        rcases hfront x hx with rfl | rfl <;> rfl)
      (by rfl)
  have hmarkLeaf :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_L) (List.replicate i .D) .d
          (.T :: frontRun.reverse ++ candLeft) r)
        ⟨.core .CMP_TOC, backRun.tail ++ .C :: l, backRun.headD .blank, .D :: r⟩ := by
    refine reaches_of_stepN (n := i + 1) ?_
    have hne : backRun ≠ [] := by simp [backRun]
    have htail := tail_append_of_ne_nil backRun (Sy.C :: l) hne
    have hhead := headD_append_of_ne_nil backRun (Sy.C :: l) hne
    have hwhole :
        List.replicate i Sy.D ++ Sy.T :: (frontRun.reverse ++ candLeft) =
          backRun ++ Sy.C :: l := by
      simp [backRun, candLeft, List.append_assoc]
    have h :=
      stepN_scanRightUntilLeft (machine cells) (.core .CMP_L) (.core .CMP_TOC)
        (List.replicate i .D) .d .D .T
        (frontRun.reverse ++ candLeft) r
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
    have hbackSymbols : ∀ x ∈ backRun,
        x = Sy.D ∨ x = Sy.T ∨ x = Sy.P ∨ x = Sy.d := by
      intro x hx
      dsimp [backRun] at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact .inl (List.mem_replicate.mp hx).2
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inr (.inl rfl)
        · rw [List.mem_append] at hx
          rcases hx with hx | hx
          · have hx' : x ∈ frontRun := by simpa using hx
            rcases hfront x hx' with rfl | rfl
            · exact .inr (.inr (.inl rfl))
            · exact .inr (.inr (.inr rfl))
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact .inl rfl
            · exact .inl (List.mem_replicate.mp hx).2
    have hscan := stepN_scanLeft (machine cells) (.core .CMP_TOC)
      (backRun.headD Sy.blank) backRun.tail (.C :: l) (.D :: r) (by
        intro x hx
        have hx' : x ∈ backRun := by
          rw [← hcons]
          exact hx
        rcases hbackSymbols x hx' with rfl | rfl | rfl | rfl <;> rfl)
    simpa only [List.tail_cons, List.headD_cons, hcons] using hscan
  have hreturn :
      Reaches (machine cells)
        ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩
        (scanRightStart (.core .CMP_C) frontRun .T
          candLeft (.D :: List.replicate i .D ++ r)) := by
    have htoC :
        Reaches (machine cells)
          ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩
          ⟨.core .CMP_C, .C :: l, .D,
            List.replicate i .D ++ frontRun ++ .T ::
              .D :: List.replicate i .D ++ r⟩ := by
      refine ⟨1, ?_⟩
      change (step (machine cells)
        ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩).bind
          (stepN (machine cells) 0) = _
      rw [show step (machine cells)
          ⟨.core .CMP_TOC, l, .C, backRun.reverse ++ .D :: r⟩ =
          some ⟨.core .CMP_C, .C :: l, .D,
            List.replicate i .D ++ frontRun ++ .T ::
              .D :: List.replicate i .D ++ r⟩ by
        simp only [step]
        rw [show machine cells (.core .CMP_TOC) .C = some (.C, .R, .core .CMP_C) by rfl]
        simp [Cfg.move, backRun, List.reverse_append, List.reverse_replicate,
          replicate_append_cons_self, headD_replicate_self, List.append_assoc]]
      rfl
    have hscan := stepN_scanRight (machine cells) (.core .CMP_C) Sy.D
      (List.replicate i .D) (.C :: l)
      (frontRun ++ .T :: .D :: List.replicate i .D ++ r) (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · have : x = Sy.D := (List.mem_replicate.mp hx).2
          subst x
          rfl)
    have hscan' :
        Reaches (machine cells)
          ⟨.core .CMP_C, .C :: l, .D,
            List.replicate i .D ++ frontRun ++ .T ::
              .D :: List.replicate i .D ++ r⟩
          (scanRightStart (.core .CMP_C) frontRun .T
            candLeft (.D :: List.replicate i .D ++ r)) := by
      refine reaches_of_stepN (n := i + 1) ?_
      simpa [scanRightStart_eq, candLeft, List.reverse_replicate,
        List.replicate_succ, replicate_append_cons_self, headD_replicate_self,
        List.append_assoc] using hscan
    exact reaches_trans htoC hscan'
  simpa [frontRun, candLeft, List.replicate_succ, List.append_assoc] using
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

/-- Iterating the generalized pairing circuit consumes the candidate depth while preserving an
encoded segment of previously rejected nodes between the candidate and the last node. -/
theorem comparePairsThrough_reaches_exhausted (cells : List Sy) (i a : ℕ)
    (middle l r : List Sy) (hmiddle : ∀ x ∈ middle, x = .P ∨ x = .d) :
    Reaches (machine cells)
      ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
        List.replicate a .d ++ middle ++ .T :: List.replicate i .D ++
          List.replicate (a + 1) .d ++ r⟩
      (scanRightStart (.core .CMP_C) middle .T
        (List.replicate (i + a + 1) .D ++ .C :: l)
        (List.replicate (i + a + 1) .D ++ r)) := by
  induction a generalizing i with
  | zero =>
      simpa [scanRightStart, List.replicate_succ, List.append_assoc] using
        (comparePairThrough_reaches cells i 0 middle l r hmiddle)
  | succ a ih =>
      have hpair := comparePairThrough_reaches cells i (a + 1) middle l
        (List.replicate (a + 1) Sy.d ++ r) hmiddle
      have hrest := ih (i + 1)
      have hpair' :
          Reaches (machine cells)
            ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
              List.replicate (a + 1) .d ++ middle ++ .T :: List.replicate i .D ++
                List.replicate (a + 2) .d ++ r⟩
            ⟨.core .CMP_C, List.replicate (i + 1) .D ++ .C :: l, .d,
              List.replicate a .d ++ middle ++ .T :: List.replicate (i + 1) .D ++
                List.replicate (a + 1) .d ++ r⟩ := by
        simpa [scanRightStart, List.replicate_succ, replicate_append_cons_self,
          List.append_assoc] using hpair
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (reaches_trans hpair' hrest)

/-- Pair exactly `k` remaining last-node marks while the candidate has `k + e + 1` marks left.
The candidate therefore still has a current mark and `e` following marks when the last-node depth
is exhausted. -/
theorem comparePairsThrough_reaches_leafExhausted (cells : List Sy) (i k e : ℕ)
    (middle l r : List Sy) (hmiddle : ∀ x ∈ middle, x = .P ∨ x = .d) :
    Reaches (machine cells)
      ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
        List.replicate (k + e) .d ++ middle ++ .T :: List.replicate i .D ++
          List.replicate k .d ++ .blank :: r⟩
      ⟨.core .CMP_C, List.replicate (i + k) .D ++ .C :: l, .d,
        List.replicate e .d ++ middle ++ .T ::
          List.replicate (i + k) .D ++ .blank :: r⟩ := by
  induction k generalizing i with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero,
        List.append_nil]
      exact reaches_refl _ _
  | succ k ih =>
      have hpair := comparePairThrough_reaches cells i (k + e + 1) middle l
        (List.replicate k Sy.d ++ .blank :: r) hmiddle
      have hpair' :
          Reaches (machine cells)
            ⟨.core .CMP_C, List.replicate i .D ++ .C :: l, .d,
              List.replicate (k + 1 + e) .d ++ middle ++ .T ::
                List.replicate i .D ++ List.replicate (k + 1) .d ++ .blank :: r⟩
            ⟨.core .CMP_C, List.replicate (i + 1) .D ++ .C :: l, .d,
              List.replicate (k + e) .d ++ middle ++ .T ::
                List.replicate (i + 1) .D ++ List.replicate k .d ++ .blank :: r⟩ := by
        rw [show k + 1 + e = k + e + 1 by omega]
        simpa [scanRightStart, List.replicate_succ, replicate_append_cons_self,
          List.append_assoc] using hpair
      have hrest := ih (i + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (reaches_trans hpair' hrest)

/-- `CMP_C` detects the `P` starting a preserved middle segment (or the final `T` when that
segment is empty) and enters the forward exhausted-candidate scan. -/
theorem compareBoundary_reaches_exhausted (cells : List Sy) (middle : List ℕ)
    (y : Sy) (l r : List Sy) :
    Reaches (machine cells)
      (scanRightStart (.core .CMP_C) (treeCells middle) .T l (y :: r))
      (scanRightStart (.core .CMP_CEXH) (treeCells middle) .T l (y :: r)) := by
  refine ⟨2, ?_⟩
  cases middle with
  | nil =>
      simpa [scanRightStart] using
        (stepN_rightLeft (machine cells) (.core .CMP_C) (.core .BACK_CMP_CEXH)
          (.core .CMP_CEXH) .T y l r (by rfl) (by cases y <;> rfl))
  | cons k middle =>
      let rest := List.replicate k Sy.d ++ treeCells middle ++ Sy.T :: y :: r
      have hrest : rest ≠ [] := by simp [rest]
      cases hrestEq : rest with
      | nil => exact (hrest hrestEq).elim
      | cons z zs =>
          have h := stepN_rightLeft (machine cells) (.core .CMP_C)
            (.core .BACK_CMP_CEXH) (.core .CMP_CEXH) .P z l zs
            (by rfl) (by cases z <;> rfl)
          rw [scanRightStart_eq, scanRightStart_eq]
          simp only [treeCells_cons, List.cons_append, List.headD_cons, List.tail_cons]
          have hright :
              List.replicate k Sy.d ++ treeCells middle ++ Sy.T :: y :: r = z :: zs := by
            simpa [rest, List.append_assoc] using hrestEq
          rw [hright]
          exact h

/-- After the candidate is exhausted, `CMP_CEXH` crosses the preserved encoded middle segment;
`CMP_LCHK` then recognizes the one remaining last-node depth mark. -/
theorem compareExhaustedThrough_reaches_parent (cells : List Sy) (a : ℕ)
    (middle : List ℕ) (x : Sy) (l r : List Sy) :
    Reaches (machine cells)
      (scanRightStart (.core .CMP_C) (treeCells middle) .T
        (List.replicate (a + 1) .D ++ .C :: l)
        (List.replicate (a + 1) .D ++ .d :: x :: r))
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T ::
          (treeCells middle).reverse ++ List.replicate (a + 1) .D ++ .C :: l,
        x, r⟩ := by
  let candLeft := List.replicate (a + 1) Sy.D ++ Sy.C :: l
  have henter :
    Reaches (machine cells)
        (scanRightStart (.core .CMP_C) (treeCells middle) .T candLeft
          (List.replicate (a + 1) .D ++ .d :: x :: r))
        (scanRightStart (.core .CMP_CEXH) (treeCells middle) .T candLeft
          (List.replicate (a + 1) .D ++ .d :: x :: r)) := by
    refine ⟨2, ?_⟩
    cases middle with
    | nil =>
        simpa [scanRightStart, List.replicate_succ] using
          (stepN_rightLeft (machine cells) (.core .CMP_C) (.core .BACK_CMP_CEXH)
            (.core .CMP_CEXH) .T .D candLeft
            (List.replicate a .D ++ .d :: x :: r) (by rfl) (by rfl))
    | cons k middle =>
        let rest := List.replicate k Sy.d ++ treeCells middle ++ Sy.T ::
          List.replicate (a + 1) Sy.D ++ Sy.d :: x :: r
        have hrest : rest ≠ [] := by simp [rest]
        cases hrestEq : rest with
        | nil => exact (hrest hrestEq).elim
        | cons y ys =>
            have h := stepN_rightLeft (machine cells) (.core .CMP_C)
              (.core .BACK_CMP_CEXH) (.core .CMP_CEXH) .P y candLeft ys
              (by rfl) (by cases y <;> rfl)
            rw [scanRightStart_eq, scanRightStart_eq]
            simp only [treeCells_cons, List.cons_append, List.headD_cons, List.tail_cons]
            have hright :
                List.replicate k Sy.d ++ treeCells middle ++ Sy.T ::
                    (List.replicate (a + 1) Sy.D ++ Sy.d :: x :: r) =
                  y :: ys := by
              simpa [rest, List.append_assoc] using hrestEq
            rw [hright]
            exact h
  have htoLast :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_CEXH) (treeCells middle) .T candLeft
          (List.replicate (a + 1) .D ++ .d :: x :: r))
        (scanRightStart (.core .CMP_LCHK) (List.replicate (a + 1) .D) .d
          (.T :: (treeCells middle).reverse ++ candLeft) (x :: r)) := by
    apply reaches_of_stepN
    exact stepN_scanRightUntilRight (machine cells) (.core .CMP_CEXH) (.core .CMP_LCHK)
      (treeCells middle) (List.replicate (a + 1) .D) .T .T .d candLeft (x :: r)
      (by
        intro y hy
        rcases mem_treeCells hy with rfl | rfl <;> rfl)
      (by rfl)
  have hfound :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_LCHK) (List.replicate (a + 1) .D) .d
          (.T :: (treeCells middle).reverse ++ candLeft) (x :: r))
        ⟨.core .PAR_END,
          .d :: List.replicate (a + 1) .D ++ .T ::
            (treeCells middle).reverse ++ candLeft,
          x, r⟩ := by
    apply reaches_of_stepN
    simpa [scanRightStart, List.reverse_replicate, List.replicate_succ,
      replicate_append_cons_self, List.append_assoc] using
      (stepN_scanRightUntilRight (machine cells) (.core .CMP_LCHK) (.core .PAR_END)
        (List.replicate (a + 1) .D) [] .d .d x
        (.T :: (treeCells middle).reverse ++ candLeft) r
        (by
          intro y hy
          have : y = Sy.D := (List.mem_replicate.mp hy).2
          subst y
          rfl)
        (by rfl))
  simpa [candLeft, List.append_assoc] using reaches_trans henter (reaches_trans htoLast hfound)

/-- A candidate one level above the last node is recognized even after arbitrary already-rejected
encoded nodes.  This is the actual parent-search shape on a nontrivial rightmost subtree. -/
theorem compareParentThrough_reaches (cells : List Sy) (a : ℕ)
    (middle : List ℕ) (x : Sy) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, .C :: l, .d,
        List.replicate a .d ++ treeCells middle ++ .T ::
          List.replicate (a + 2) .d ++ x :: r⟩
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T ::
          (treeCells middle).reverse ++ List.replicate (a + 1) .D ++ .C :: l,
        x, r⟩ := by
  have hpairs := comparePairsThrough_reaches_exhausted cells 0 a
    (treeCells middle) l (.d :: x :: r) (fun _ hx ↦ mem_treeCells hx)
  have hfound := compareExhaustedThrough_reaches_parent cells a middle x l r
  have hpairs' :
      Reaches (machine cells)
        ⟨.core .CMP_C, .C :: l, .d,
          List.replicate a .d ++ treeCells middle ++ .T ::
            List.replicate (a + 2) .d ++ x :: r⟩
        (scanRightStart (.core .CMP_C) (treeCells middle) .T
          (List.replicate (a + 1) .D ++ .C :: l)
          (List.replicate (a + 1) .D ++ .d :: x :: r)) := by
    simpa [List.replicate_succ, replicate_append_cons_self,
      List.append_assoc] using hpairs
  exact reaches_trans hpairs' hfound

/-- If the candidate and the last node have equal depth, the exhausted scan reaches the trailing
blank and enters `NOTPARENT`, preserving every intervening encoded node. -/
theorem compareExhaustedThrough_reaches_notParent (cells : List Sy) (a : ℕ)
    (middle : List ℕ) (l r : List Sy) :
    Reaches (machine cells)
      (scanRightStart (.core .CMP_C) (treeCells middle) .T
        (List.replicate (a + 1) .D ++ .C :: l)
        (List.replicate (a + 1) .D ++ .blank :: r))
      ⟨.core .NOTPARENT,
        List.replicate a .D ++ .T :: (treeCells middle).reverse ++
          List.replicate (a + 1) .D ++ .C :: l,
        .D, .blank :: r⟩ := by
  let candLeft := List.replicate (a + 1) Sy.D ++ Sy.C :: l
  have henter :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_C) (treeCells middle) .T candLeft
          (List.replicate (a + 1) .D ++ .blank :: r))
        (scanRightStart (.core .CMP_CEXH) (treeCells middle) .T candLeft
          (List.replicate (a + 1) .D ++ .blank :: r)) := by
    simpa [List.replicate_succ] using
      (compareBoundary_reaches_exhausted cells middle Sy.D candLeft
        (List.replicate a .D ++ .blank :: r))
  have htoLast :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_CEXH) (treeCells middle) .T candLeft
          (List.replicate (a + 1) .D ++ .blank :: r))
        (scanRightStart (.core .CMP_LCHK) (List.replicate (a + 1) .D) .blank
          (.T :: (treeCells middle).reverse ++ candLeft) r) := by
    apply reaches_of_stepN
    exact stepN_scanRightUntilRight (machine cells) (.core .CMP_CEXH) (.core .CMP_LCHK)
      (treeCells middle) (List.replicate (a + 1) .D) .T .T .blank candLeft r
      (by
        intro y hy
        rcases mem_treeCells hy with rfl | rfl <;> rfl)
      (by rfl)
  have hreject :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_LCHK) (List.replicate (a + 1) .D) .blank
          (.T :: (treeCells middle).reverse ++ candLeft) r)
        ⟨.core .NOTPARENT,
          List.replicate a .D ++ .T :: (treeCells middle).reverse ++ candLeft,
          .D, .blank :: r⟩ := by
    apply reaches_of_stepN
    simpa [scanRightStart, List.reverse_replicate, List.replicate_succ,
      replicate_append_cons_self, List.append_assoc] using
      (stepN_scanRightUntilLeft (machine cells) (.core .CMP_LCHK) (.core .NOTPARENT)
        (List.replicate (a + 1) .D) .blank .blank .T
        ((treeCells middle).reverse ++ candLeft) r
        (by
          intro y hy
          have : y = Sy.D := (List.mem_replicate.mp hy).2
          subst y
          rfl)
        (by rfl))
  simpa [candLeft, List.append_assoc] using reaches_trans henter (reaches_trans htoLast hreject)

/-- Equal-depth candidates are rejected, fully unmarked, and left behind in the preserved middle
segment before `CAND_FIND` retries the preceding node. -/
theorem compareEqualThrough_reaches_retry (cells : List Sy) (a : ℕ)
    (middle : List ℕ) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, .C :: l, .d,
        List.replicate a .d ++ treeCells middle ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩
      ⟨.core .CAND_FIND, l.tail, l.headD .blank,
        .P :: List.replicate (a + 1) .d ++ treeCells middle ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩ := by
  have hpairs := comparePairsThrough_reaches_exhausted cells 0 a
    (treeCells middle) l (.blank :: r) (fun _ hx ↦ mem_treeCells hx)
  have hreject := compareExhaustedThrough_reaches_notParent cells a middle l r
  have hpairs' :
      Reaches (machine cells)
        ⟨.core .CMP_C, .C :: l, .d,
          List.replicate a .d ++ treeCells middle ++ .T ::
            List.replicate (a + 1) .d ++ .blank :: r⟩
        (scanRightStart (.core .CMP_C) (treeCells middle) .T
          (List.replicate (a + 1) .D ++ .C :: l)
          (List.replicate (a + 1) .D ++ .blank :: r)) := by
    simpa [List.append_assoc] using hpairs
  have hreject' := reaches_trans hpairs' hreject
  let scanTail := List.replicate a Sy.D ++ Sy.T :: (treeCells middle).reverse ++
    List.replicate (a + 1) Sy.D
  have hrestore := notParent_reaches_candidate cells Sy.D scanTail l (.blank :: r) (by
    intro y hy
    simp only [List.mem_cons, scanTail, List.mem_append] at hy
    rcases hy with rfl | hy
    · exact .inl rfl
    · rcases hy with (hy | rfl | hy) | hy
      · exact .inl (List.mem_replicate.mp hy).2
      · exact .inr (.inl rfl)
      · have hy' : y ∈ treeCells middle := by simpa using hy
        rcases mem_treeCells hy' with rfl | rfl
        · exact .inr (.inr (.inl rfl))
        · exact .inr (.inr (.inr rfl))
      · exact .inl (List.mem_replicate.mp hy).2)
  have hrestore' :
      Reaches (machine cells)
        ⟨.core .NOTPARENT,
          List.replicate a .D ++ .T :: (treeCells middle).reverse ++
            List.replicate (a + 1) .D ++ .C :: l,
          .D, .blank :: r⟩
        ⟨.core .CAND_FIND, l.tail, l.headD .blank,
          .P :: List.replicate (a + 1) .d ++ treeCells middle ++ .T ::
            List.replicate (a + 1) .d ++ .blank :: r⟩ := by
    simpa [scanTail, restoreD, List.map_append, List.reverse_append,
      List.reverse_replicate, List.replicate_succ, replicate_append_cons_self,
      List.append_assoc] using hrestore
  exact reaches_trans hreject' hrestore'

/-- When the last-node depth is exhausted while the candidate still has a mark, `CMP_L` reaches
the trailing blank and rejects the candidate. -/
theorem compareLeafExhaustedThrough_reaches_notParent (cells : List Sy) (a e : ℕ)
    (middle : List ℕ) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, List.replicate (a + 1) .D ++ .C :: l, .d,
        List.replicate e .d ++ treeCells middle ++ .T ::
          List.replicate (a + 1) .D ++ .blank :: r⟩
      ⟨.core .NOTPARENT,
        List.replicate a .D ++ .T :: (treeCells middle).reverse ++
          List.replicate e .d ++ .D :: List.replicate (a + 1) .D ++ .C :: l,
        .D, .blank :: r⟩ := by
  let frontRun := List.replicate e Sy.d ++ treeCells middle
  let candLeft := Sy.D :: List.replicate (a + 1) Sy.D ++ Sy.C :: l
  have hfront : ∀ x ∈ frontRun, x = Sy.P ∨ x = Sy.d := by
    intro x hx
    rw [show frontRun = List.replicate e Sy.d ++ treeCells middle by rfl,
      List.mem_append] at hx
    rcases hx with hx | hx
    · exact .inr (List.mem_replicate.mp hx).2
    · exact mem_treeCells hx
  have hmark :
      Reaches (machine cells)
        ⟨.core .CMP_C, List.replicate (a + 1) .D ++ .C :: l, .d,
          frontRun ++ .T :: List.replicate (a + 1) .D ++ .blank :: r⟩
        (scanRightStart (.core .CMP_TOL) frontRun .T candLeft
          (List.replicate (a + 1) .D ++ .blank :: r)) := by
    refine ⟨1, ?_⟩
    change (step (machine cells)
      ⟨.core .CMP_C, List.replicate (a + 1) .D ++ .C :: l, .d,
        frontRun ++ .T :: List.replicate (a + 1) .D ++ .blank :: r⟩).bind
      (stepN (machine cells) 0) = _
    rw [show step (machine cells)
        ⟨.core .CMP_C, List.replicate (a + 1) .D ++ .C :: l, .d,
          frontRun ++ .T :: List.replicate (a + 1) .D ++ .blank :: r⟩ =
        some (scanRightStart (.core .CMP_TOL) frontRun .T candLeft
          (List.replicate (a + 1) .D ++ .blank :: r)) by
      simp only [step]
      rw [show machine cells (.core .CMP_C) .d = some (.D, .R, .core .CMP_TOL) by rfl]
      simp [Cfg.move, scanRightStart_eq, candLeft, List.append_assoc]]
    rfl
  have htoLast :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_TOL) frontRun .T candLeft
          (List.replicate (a + 1) .D ++ .blank :: r))
        (scanRightStart (.core .CMP_L) (List.replicate (a + 1) .D) .blank
          (.T :: frontRun.reverse ++ candLeft) r) := by
    apply reaches_of_stepN
    exact stepN_scanRightUntilRight (machine cells) (.core .CMP_TOL) (.core .CMP_L)
      frontRun (List.replicate (a + 1) .D) .T .T .blank candLeft r
      (by
        intro x hx
        rcases hfront x hx with rfl | rfl <;> rfl)
      (by rfl)
  have hreject :
      Reaches (machine cells)
        (scanRightStart (.core .CMP_L) (List.replicate (a + 1) .D) .blank
          (.T :: frontRun.reverse ++ candLeft) r)
        ⟨.core .NOTPARENT,
          List.replicate a .D ++ .T :: frontRun.reverse ++ candLeft,
          .D, .blank :: r⟩ := by
    apply reaches_of_stepN
    simpa [scanRightStart, List.reverse_replicate, List.replicate_succ,
      replicate_append_cons_self, List.append_assoc] using
      (stepN_scanRightUntilLeft (machine cells) (.core .CMP_L) (.core .NOTPARENT)
        (List.replicate (a + 1) .D) .blank .blank .T
        (frontRun.reverse ++ candLeft) r
        (by
          intro y hy
          have : y = Sy.D := (List.mem_replicate.mp hy).2
          subst y
          rfl)
        (by rfl))
  simpa [frontRun, candLeft, List.reverse_append, List.reverse_replicate,
    List.append_assoc] using reaches_trans hmark (reaches_trans htoLast hreject)

/-- A candidate deeper than the last node is rejected, fully unmarked, and added to the preserved
middle segment before `CAND_FIND` retries farther left. -/
theorem compareDeeperThrough_reaches_retry (cells : List Sy) (a e : ℕ)
    (middle : List ℕ) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, .C :: l, .d,
        List.replicate (a + 1 + e) .d ++ treeCells middle ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩
      ⟨.core .CAND_FIND, l.tail, l.headD .blank,
        .P :: List.replicate (a + e + 2) .d ++ treeCells middle ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩ := by
  have hpairs := comparePairsThrough_reaches_leafExhausted cells 0 (a + 1) e
    (treeCells middle) l r (fun _ hx ↦ mem_treeCells hx)
  have hpairs' :
      Reaches (machine cells)
        ⟨.core .CMP_C, .C :: l, .d,
          List.replicate (a + 1 + e) .d ++ treeCells middle ++ .T ::
            List.replicate (a + 1) .d ++ .blank :: r⟩
        ⟨.core .CMP_C, List.replicate (a + 1) .D ++ .C :: l, .d,
          List.replicate e .d ++ treeCells middle ++ .T ::
            List.replicate (a + 1) .D ++ .blank :: r⟩ := by
    simpa [List.append_assoc] using hpairs
  have hreject := compareLeafExhaustedThrough_reaches_notParent cells a e middle l r
  have hreject' := reaches_trans hpairs' hreject
  let scanTail := List.replicate a Sy.D ++
    (Sy.T :: ((treeCells middle).reverse ++
      (List.replicate e Sy.d ++ (Sy.D :: List.replicate (a + 1) Sy.D))))
  have hrestore := notParent_reaches_candidate cells Sy.D scanTail l (.blank :: r) (by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl rfl
    · dsimp [scanTail] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact .inl (List.mem_replicate.mp hy).2
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact .inr (.inl rfl)
        · rcases List.mem_append.mp hy with hy | hy
          · have hy' : y ∈ treeCells middle := by simpa using hy
            rcases mem_treeCells hy' with rfl | rfl
            · exact .inr (.inr (.inl rfl))
            · exact .inr (.inr (.inr rfl))
          · rcases List.mem_append.mp hy with hy | hy
            · exact .inr (.inr (.inr (List.mem_replicate.mp hy).2))
            · rcases List.mem_cons.mp hy with rfl | hy
              · exact .inl rfl
              · exact .inl (List.mem_replicate.mp hy).2)
  have hrestore' :
      Reaches (machine cells)
        ⟨.core .NOTPARENT,
          List.replicate a .D ++ .T :: (treeCells middle).reverse ++
            List.replicate e .d ++ .D :: List.replicate (a + 1) .D ++ .C :: l,
          .D, .blank :: r⟩
        ⟨.core .CAND_FIND, l.tail, l.headD .blank,
          .P :: List.replicate (a + e + 2) .d ++ treeCells middle ++ .T ::
            List.replicate (a + 1) .d ++ .blank :: r⟩ := by
    have hraw := hrestore
    simp [scanTail, restoreD, List.map_append, List.reverse_append,
      List.reverse_replicate, List.replicate_succ, replicate_append_cons_self,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hraw
    simp only [two_cons_replicate_append] at hraw
    simpa [List.replicate_succ, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hraw
  exact reaches_trans hreject' hrestore'

/-- Every candidate at least as deep as the last node is rejected and restored.  `q = 0` is the
equal-depth `CMP_LCHK` exit; `q > 0` is the deeper-candidate `CMP_L` exit. -/
theorem compareRejectedThrough_reaches_retry (cells : List Sy) (a q : ℕ)
    (middle : List ℕ) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CMP_C, .C :: l, .d,
        List.replicate (a + q) .d ++ treeCells middle ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩
      ⟨.core .CAND_FIND, l.tail, l.headD .blank,
        .P :: List.replicate (a + q + 1) .d ++ treeCells middle ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩ := by
  cases q with
  | zero => simpa using compareEqualThrough_reaches_retry cells a middle l r
  | succ e =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        compareDeeperThrough_reaches_retry cells a e middle l r

/-- One complete rejected-candidate iteration, starting before its rightmost depth mark.  The
restored candidate is prepended to `middle`, exposing the preceding tape cell to `CAND_FIND`. -/
theorem candidateRejectedThrough_reaches_retry (cells : List Sy) (a q : ℕ)
    (middle : List ℕ) (l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .CAND_FIND, List.replicate (a + q) .d ++ .P :: l, .d,
        treeCells middle ++ .T :: List.replicate (a + 1) .d ++ .blank :: r⟩
      ⟨.core .CAND_FIND, l.tail, l.headD .blank,
        treeCells ((a + q + 1) :: middle) ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩ := by
  have hfind := reaches_of_stepN (candidateFind_reaches_compare cells (a + q) l
    (treeCells middle ++ .T :: List.replicate (a + 1) .d ++ .blank :: r))
  have hreject := compareRejectedThrough_reaches_retry cells a q middle l r
  have hfind' :
      Reaches (machine cells)
        ⟨.core .CAND_FIND, List.replicate (a + q) .d ++ .P :: l, .d,
          treeCells middle ++ .T :: List.replicate (a + 1) .d ++ .blank :: r⟩
        ⟨.core .CMP_C, .C :: l, .d,
          List.replicate (a + q) .d ++ treeCells middle ++ .T ::
            List.replicate (a + 1) .d ++ .blank :: r⟩ := by
    simpa [List.append_assoc] using hfind
  simpa [treeCells_cons, List.append_assoc] using reaches_trans hfind' hreject

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
