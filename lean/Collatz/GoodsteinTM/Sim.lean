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

/-- A right scan through a nonempty finite right half reaches the implicit blank just beyond it. -/
theorem stepN_scanRightToImplicit (M : St → Sy → Option (Sy × Dir × St)) (q : St)
    (xs : List Sy) (l : List Sy) (hne : xs ≠ [])
    (hscan : ∀ a ∈ xs, M q a = some (a, .R, q)) :
    stepN M xs.length ⟨q, l, xs.headD default, xs.tail⟩ =
      some ⟨q, xs.reverse ++ l, default, []⟩ := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simpa using stepN_scanRight M q x xs l [] hscan

/-- Scan left across a nonempty block presented in reverse on the left half. -/
theorem stepN_scanLeftReverse (M : St → Sy → Option (Sy × Dir × St)) (q : St)
    (xs l r : List Sy) (hne : xs ≠ [])
    (hscan : ∀ a ∈ xs, M q a = some (a, .L, q)) :
    stepN M xs.length
        ⟨q, xs.reverse.tail ++ l, xs.reverse.headD default, r⟩ =
      some ⟨q, l.tail, l.headD default, xs ++ r⟩ := by
  induction xs using List.reverseRecOn with
  | nil => contradiction
  | append_singleton pre last =>
      have h := stepN_scanLeft M q last pre.reverse l r (by
        intro a ha
        apply hscan a
        simpa [List.reverse_append, or_comm] using ha)
      simpa [List.reverse_append, List.append_assoc] using h

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

/-- Right-moving counterpart of `stepN_scanLeftMap`, including a distinguished stop transition.
This is used by `REP_DONE`, whose scan restores every used base counter from `B` to `b`. -/
theorem stepN_scanRightMapUntilRight (M : St → Sy → Option (Sy × Dir × St))
    (q q' : St) (f : Sy → Sy) (xs zs : List Sy) (y y' z : Sy) (l r : List Sy)
    (hscan : ∀ a ∈ xs, M q a = some (f a, .R, q))
    (hstop : M q y = some (y', .R, q')) :
    stepN M (xs.length + 1)
        (scanRightStart q xs y l (zs ++ z :: r)) =
      some (scanRightStart q' zs z
        (y' :: (xs.map f).reverse ++ l) r) := by
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
          some (scanRightStart q xs y (f x :: l) (zs ++ z :: r)) by
        have hx := hscan x (by simp)
        cases xs <;> simp [scanRightStart, step, Cfg.move, hx]]
      simp only [Option.bind_some]
      rw [ih (l := f x :: l) (by
        intro a ha
        exact hscan a (by simp [ha]))]
      simp [List.reverse_cons, List.append_assoc]

/-- Scan a possibly empty run to the right, consume a right-moving stop symbol, and expose an
arbitrary finite right half.  In particular, an empty right half exposes the implicit blank. -/
theorem stepN_scanRightUntilRightTail (M : St → Sy → Option (Sy × Dir × St))
    (q q' : St) (xs : List Sy) (y y' : Sy) (l r : List Sy)
    (hscan : ∀ a ∈ xs, M q a = some (a, .R, q))
    (hstop : M q y = some (y', .R, q')) :
    stepN M (xs.length + 1) (scanRightStart q xs y l r) =
      some ⟨q', y' :: xs.reverse ++ l, r.headD default, r.tail⟩ := by
  induction xs generalizing l with
  | nil =>
      simp [scanRightStart, stepN, step, Cfg.move, hstop]
  | cons x xs ih =>
      change (step M ⟨q, l, x, xs ++ y :: r⟩).bind
        (stepN M (xs.length + 1)) = _
      rw [show step M ⟨q, l, x, xs ++ y :: r⟩ =
          some (scanRightStart q xs y (x :: l) r) by
        have hx := hscan x (by simp)
        cases xs <;> simp [scanRightStart, step, Cfg.move, hx]]
      simp only [Option.bind_some]
      rw [ih (l := x :: l) (by
        intro a ha
        exact hscan a (by simp [ha]))]
      simp [List.reverse_cons, List.append_assoc]

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

@[simp] theorem treeCells_append (s t : List ℕ) :
    treeCells (s ++ t) = treeCells s ++ treeCells t := by
  simp [treeCells]

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

/-- A nonempty positive-depth tree encoding ends in a depth symbol. -/
theorem exists_treeCells_append_d {t : List ℕ} (hne : t ≠ [])
    (hpositive : ∀ k ∈ t, 1 ≤ k) : ∃ pre, treeCells t = pre ++ [.d] := by
  induction t using List.reverseRecOn with
  | nil => contradiction
  | append_singleton pre k _ =>
      have hk : 1 ≤ k := hpositive k (by simp)
      obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
      refine ⟨treeCells pre ++ .P :: List.replicate q .d, ?_⟩
      simp [treeCells_append, treeCells_cons, List.replicate_succ',
        replicate_append_cons_self, List.append_assoc]

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

/-- Starting at the right edge of a suffix whose nodes are all at least as deep as the marked
last node, repeated rejected-candidate iterations cross the whole suffix.  Restored nodes are
accumulated in their original left-to-right order in front of `middle`. -/
theorem candidateSuffix_reaches_retry (cells : List Sy) (a : ℕ)
    (suffix middle : List ℕ) (l r : List Sy)
    (hdeep : ∀ k ∈ suffix, a + 1 ≤ k) :
    Reaches (machine cells)
      ⟨.core .CAND_FIND, ((treeCells suffix).reverse ++ l).tail,
        ((treeCells suffix).reverse ++ l).headD .blank,
        treeCells middle ++ .T :: List.replicate (a + 1) .d ++ .blank :: r⟩
      ⟨.core .CAND_FIND, l.tail, l.headD .blank,
        treeCells (suffix ++ middle) ++ .T ::
          List.replicate (a + 1) .d ++ .blank :: r⟩ := by
  induction suffix using List.reverseRecOn generalizing middle with
  | nil =>
      change Reaches (machine cells)
        ⟨.core .CAND_FIND, l.tail, l.headD .blank,
          treeCells middle ++ .T :: List.replicate (a + 1) .d ++ .blank :: r⟩
        ⟨.core .CAND_FIND, l.tail, l.headD .blank,
          treeCells middle ++ .T :: List.replicate (a + 1) .d ++ .blank :: r⟩
      exact reaches_refl _ _
  | append_singleton pre k ih =>
      have hk : a + 1 ≤ k := hdeep k (by simp)
      obtain ⟨q, hk_eq⟩ : ∃ q, k = a + q + 1 := by
        exact ⟨k - (a + 1), by omega⟩
      subst k
      have hone := candidateRejectedThrough_reaches_retry cells a q middle
        ((treeCells pre).reverse ++ l) r
      have hone' :
          Reaches (machine cells)
            ⟨.core .CAND_FIND,
              ((treeCells (pre ++ [a + q + 1])).reverse ++ l).tail,
              ((treeCells (pre ++ [a + q + 1])).reverse ++ l).headD .blank,
              treeCells middle ++ .T ::
                List.replicate (a + 1) .d ++ .blank :: r⟩
            ⟨.core .CAND_FIND,
              ((treeCells pre).reverse ++ l).tail,
              ((treeCells pre).reverse ++ l).headD .blank,
              treeCells ((a + q + 1) :: middle) ++ .T ::
                List.replicate (a + 1) .d ++ .blank :: r⟩ := by
        simpa [List.reverse_append, List.reverse_replicate, List.replicate_succ,
          replicate_append_cons_self, List.append_assoc] using hone
      have hprefix : ∀ k ∈ pre, a + 1 ≤ k := by
        intro k hk
        exact hdeep k (by simp [hk])
      have hrest := ih ((a + q + 1) :: middle) hprefix
      simpa [List.append_assoc] using reaches_trans hone' hrest

/-- The complete right-to-left search through a deep suffix finds the actual rightmost parent of
a final node of depth `a + 2`.  The result is the canonical `PAR_END` configuration used by the
erase-and-copy phase. -/
theorem chopStartThrough_reaches_parent (cells : List Sy) (a : ℕ)
    (suffix : List ℕ) (l r : List Sy)
    (hdeep : ∀ k ∈ suffix, a + 2 ≤ k) :
    Reaches (machine cells)
      ⟨.core .CHOP_START,
        List.replicate (a + 1) .d ++ .P :: (treeCells suffix).reverse ++
          List.replicate (a + 1) .d ++ .P :: l,
        .d, .blank :: r⟩
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T ::
          (treeCells suffix).reverse ++ List.replicate (a + 1) .D ++ .C :: l,
        .blank, r⟩ := by
  let parentTape := List.replicate (a + 1) Sy.d ++ Sy.P :: l
  have hstart := reaches_of_stepN
    (chopStart_reaches_candidate cells a ((treeCells suffix).reverse ++ parentTape)
      (.blank :: r))
  have hsuffix := candidateSuffix_reaches_retry cells (a + 1) suffix [] parentTape r (by
    simpa [Nat.add_assoc] using hdeep)
  have hfind := reaches_of_stepN
    (candidateFind_reaches_compare cells a l
      (treeCells suffix ++ .T :: List.replicate (a + 2) .d ++ .blank :: r))
  have hparent := compareParentThrough_reaches cells a suffix .blank l r
  have hstart' :
      Reaches (machine cells)
        ⟨.core .CHOP_START,
          List.replicate (a + 1) .d ++ .P :: (treeCells suffix).reverse ++ parentTape,
          .d, .blank :: r⟩
        ⟨.core .CAND_FIND,
          ((treeCells suffix).reverse ++ parentTape).tail,
          ((treeCells suffix).reverse ++ parentTape).headD .blank,
          .T :: List.replicate (a + 2) .d ++ .blank :: r⟩ := by
    simpa [List.append_assoc] using hstart
  have hsuffix' :
      Reaches (machine cells)
        ⟨.core .CAND_FIND,
          ((treeCells suffix).reverse ++ parentTape).tail,
          ((treeCells suffix).reverse ++ parentTape).headD .blank,
          .T :: List.replicate (a + 2) .d ++ .blank :: r⟩
        ⟨.core .CAND_FIND, List.replicate a .d ++ .P :: l, .d,
          treeCells suffix ++ .T :: List.replicate (a + 2) .d ++ .blank :: r⟩ := by
    simpa [parentTape, List.replicate_succ, List.append_assoc] using hsuffix
  have hfind' :
      Reaches (machine cells)
        ⟨.core .CAND_FIND, List.replicate a .d ++ .P :: l, .d,
          treeCells suffix ++ .T :: List.replicate (a + 2) .d ++ .blank :: r⟩
        ⟨.core .CMP_C, .C :: l, .d,
          List.replicate a .d ++ treeCells suffix ++ .T ::
            List.replicate (a + 2) .d ++ .blank :: r⟩ := by
    simpa [List.append_assoc] using hfind
  simpa [parentTape, List.append_assoc] using
    reaches_trans hstart' (reaches_trans hsuffix'
      (reaches_trans hfind' hparent))

/-- For an actual well-formed level sequence, the machine's search finds the rightmost node one
level above the final leaf.  The witnesses expose exactly the prefix/suffix decomposition used by
`parentBlock`. -/
theorem chopStart_reaches_parent_of_wf (cells : List Sy) (a : ℕ)
    (s : List ℕ) (l r : List Sy) (ht : WF (s ++ [a + 2])) :
    ∃ p u, s = p ++ (a + 1) :: u ∧
      Reaches (machine cells)
        ⟨.core .CHOP_START,
          List.replicate (a + 1) .d ++ .P :: (treeCells s).reverse ++ l,
          .d, .blank :: r⟩
        ⟨.core .PAR_END,
          .d :: List.replicate (a + 1) .D ++ .T ::
            (treeCells u).reverse ++ List.replicate (a + 1) .D ++
              .C :: (treeCells p).reverse ++ l,
          .blank, r⟩ := by
  obtain ⟨p, u, hsplit, hdeep⟩ :=
    exists_parent_split_of_wf ht (by omega)
  have hsplit' : s = p ++ (a + 1) :: u := by
    simpa using hsplit
  refine ⟨p, u, hsplit', ?_⟩
  have hsearch := chopStartThrough_reaches_parent cells a u
    ((treeCells p).reverse ++ l) r (by
      intro k hk
      have := hdeep k hk
      omega)
  rw [hsplit']
  simpa [List.reverse_append, List.reverse_replicate, List.replicate_succ,
    replicate_append_cons_self, List.append_assoc] using hsearch

/-- After `MARK_END` has marked the right edge of the copy block, `UNMARK_S` restores all
comparison marks on the block, changes its initial `C` to `S`, and executes the generated stay
move into `REP_START`.  `front` is in forward tape order; the source configuration scans it in
reverse order. -/
theorem unmarkStart_reaches_repStart (cells : List Sy) (front l r : List Sy) (y : Sy)
    (hfront : ∀ x ∈ front, x = .P ∨ x = .d ∨ x = .D) :
    Reaches (machine cells)
      ⟨.core .UNMARK_S, (front.reverse ++ .C :: l).tail,
        (front.reverse ++ .C :: l).headD .blank, y :: r⟩
      ⟨.core .REP_START, l, .S, front.map restoreD ++ y :: r⟩ := by
  induction front using List.reverseRecOn generalizing y r with
  | nil =>
      refine ⟨2, ?_⟩
      cases y <;> rfl
  | append_singleton pre x ih =>
      have hx : x = Sy.P ∨ x = Sy.d ∨ x = Sy.D := hfront x (by simp)
      have hpre : ∀ y ∈ pre, y = Sy.P ∨ y = Sy.d ∨ y = Sy.D := by
        intro y hy
        exact hfront y (by simp [hy])
      have hone :
          Reaches (machine cells)
            ⟨.core .UNMARK_S,
              ((pre ++ [x]).reverse ++ .C :: l).tail,
              ((pre ++ [x]).reverse ++ .C :: l).headD .blank, y :: r⟩
            ⟨.core .UNMARK_S, (pre.reverse ++ .C :: l).tail,
              (pre.reverse ++ .C :: l).headD .blank, restoreD x :: y :: r⟩ := by
        rcases hx with rfl | rfl | rfl <;>
          simpa [List.reverse_append] using
            (show Reaches (machine cells)
              ⟨.core .UNMARK_S, pre.reverse ++ .C :: l, _, y :: r⟩
              ⟨.core .UNMARK_S, (pre.reverse ++ .C :: l).tail,
                (pre.reverse ++ .C :: l).headD .blank, _ :: y :: r⟩ from ⟨1, rfl⟩)
      have hrest := ih (y :: r) (restoreD x) hpre
      simpa [List.map_append, List.append_assoc] using reaches_trans hone hrest

/-- `PAR_END` crosses the blank tail, erases the marked last node, and stops on the final symbol
of the copy block in `MARK_END`. -/
theorem parEnd_reaches_markEnd (cells : List Sy) (a : ℕ)
    (last : Sy) (front l r : List Sy) :
    Reaches (machine cells)
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T :: last :: front.reverse ++ .C :: l,
        .blank, r⟩
      ⟨.core .MARK_END, front.reverse ++ .C :: l, last,
        List.replicate (a + 4) .blank ++ r⟩ := by
  have henter :
      stepN (machine cells) 1
        ⟨.core .PAR_END,
          .d :: List.replicate (a + 1) .D ++ .T :: last :: front.reverse ++ .C :: l,
          .blank, r⟩ =
        some ⟨.core .ERASE_L,
          List.replicate (a + 1) .D ++ .T :: last :: front.reverse ++ .C :: l,
          .d, .blank :: r⟩ := by
    rfl
  have herase := stepN_scanLeftMap (machine cells) (.core .ERASE_L)
    (fun _ : Sy => Sy.blank) .d (List.replicate (a + 1) .D)
    (.T :: last :: front.reverse ++ .C :: l) (.blank :: r) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · have : x = Sy.D := (List.mem_replicate.mp hx).2
        subst x
        rfl)
  have herase' :
      stepN (machine cells) (a + 2)
        ⟨.core .ERASE_L,
          List.replicate (a + 1) .D ++ .T :: last :: front.reverse ++ .C :: l,
          .d, .blank :: r⟩ =
        some ⟨.core .ERASE_L, last :: front.reverse ++ .C :: l, .T,
          List.replicate (a + 3) .blank ++ r⟩ := by
    simpa [List.map_replicate, List.reverse_replicate, List.replicate_succ,
      replicate_append_cons_self, List.append_assoc] using herase
  have hmark :
      stepN (machine cells) 1
        ⟨.core .ERASE_L, last :: front.reverse ++ .C :: l, .T,
          List.replicate (a + 3) .blank ++ r⟩ =
        some ⟨.core .MARK_END, front.reverse ++ .C :: l, last,
          List.replicate (a + 4) .blank ++ r⟩ := by
    simpa [List.replicate_succ, replicate_append_cons_self, List.append_assoc] using
      (show stepN (machine cells) 1
        ⟨.core .ERASE_L, last :: front.reverse ++ .C :: l, .T,
          List.replicate (a + 3) .blank ++ r⟩ =
        some ⟨.core .MARK_END, front.reverse ++ .C :: l, last,
          .blank :: List.replicate (a + 3) .blank ++ r⟩ by rfl)
  exact reaches_trans (reaches_of_stepN henter)
    (reaches_trans (reaches_of_stepN herase') (reaches_of_stepN hmark))

/-- Complete erase/mark/restore phase.  `front ++ [last]` is the copy block after its initial
node marker, in forward tape order. -/
theorem eraseLeaf_reaches_repStart (cells : List Sy) (a : ℕ)
    (last : Sy) (front l r : List Sy)
    (hlast : last = .d ∨ last = .D)
    (hfront : ∀ x ∈ front, x = .P ∨ x = .d ∨ x = .D) :
    Reaches (machine cells)
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T :: last :: front.reverse ++ .C :: l,
        .blank, r⟩
      ⟨.core .REP_START, l, .S,
        front.map restoreD ++ .z :: List.replicate (a + 4) .blank ++ r⟩ := by
  have htoMark := parEnd_reaches_markEnd cells a last front l r
  have hmark :
      Reaches (machine cells)
        ⟨.core .MARK_END, front.reverse ++ .C :: l, last,
          List.replicate (a + 4) .blank ++ r⟩
        ⟨.core .UNMARK_S, (front.reverse ++ .C :: l).tail,
          (front.reverse ++ .C :: l).headD .blank,
          .z :: List.replicate (a + 4) .blank ++ r⟩ := by
    rcases hlast with rfl | rfl <;> exact ⟨1, rfl⟩
  have hunmark := unmarkStart_reaches_repStart cells front l
    (List.replicate (a + 4) Sy.blank ++ r) .z hfront
  simpa [List.append_assoc] using
    reaches_trans htoMark (reaches_trans hmark hunmark)

/-- The copy block after `MARK_END`: the parent marker is scanned as `S`, and the final depth
mark of the parent's pruned subtree is `z`. -/
def markedCopyTail (a : ℕ) (u : List ℕ) : List Sy :=
  (List.replicate (a + 1) Sy.d ++ treeCells u).dropLast ++ [Sy.z]

/-- One nonfinal pass of the copy loop.  The source cell is marked, its copy is appended at the
first blank, and `CP_RET` returns to the first cell of `future`.  Keeping the table entries as
hypotheses lets the same tape argument serve the `S`, `P`, and `d` cases. -/
theorem copyCell_reaches (cells : List Sy) (carry : Core) (x mark copied : Sy)
    (future l r : List Sy) (hfuture : future ≠ [])
    (hstart : machine cells (.core .CP_SCAN) x =
      some (mark, .R, .core carry))
    (hcarry : ∀ y ∈ future,
      machine cells (.core carry) y = some (y, .R, .core carry))
    (hblank : machine cells (.core carry) .blank =
      some (copied, .L, .core .CP_RET))
    (hreturn : ∀ y ∈ future,
      machine cells (.core .CP_RET) y = some (y, .L, .core .CP_RET))
    (hmark : machine cells (.core .CP_RET) mark =
      some (mark, .R, .core .CP_SCAN)) :
    Reaches (machine cells)
      ⟨.core .CP_SCAN, l, x, future ++ .blank :: r⟩
      (scanRightStart (.core .CP_SCAN) future copied (mark :: l) r) := by
  induction future using List.reverseRecOn with
  | nil => contradiction
  | append_singleton pre last =>
      have henter :
          Reaches (machine cells)
            ⟨.core .CP_SCAN, l, x, (pre ++ [last]) ++ .blank :: r⟩
            (scanRightStart (.core carry) (pre ++ [last]) .blank (mark :: l) r) := by
        refine ⟨1, ?_⟩
        cases pre <;> simp [stepN, step, Cfg.move, scanRightStart, hstart]
      have htoBlank := stepN_scanRightUntilLeft (machine cells)
        (.core carry) (.core .CP_RET) (pre ++ [last]) .blank copied mark l r
        (by
          intro y hy
          exact hcarry y (by simpa using hy)) hblank
      have htoBlank' :
          Reaches (machine cells)
            (scanRightStart (.core carry) (pre ++ [last]) .blank (mark :: l) r)
            ⟨.core .CP_RET, pre.reverse ++ mark :: l, last, copied :: r⟩ := by
        refine ⟨(pre ++ [last]).length + 1, ?_⟩
        simpa [List.reverse_append, List.append_assoc] using htoBlank
      have hback := stepN_scanLeft (machine cells) (.core .CP_RET) last pre.reverse
        (mark :: l) (copied :: r) (by
          intro y hy
          apply hreturn y
          simpa [List.reverse_append, or_comm] using hy)
      have hback' :
          Reaches (machine cells)
            ⟨.core .CP_RET, pre.reverse ++ mark :: l, last, copied :: r⟩
            ⟨.core .CP_RET, l, mark, (pre ++ [last]) ++ copied :: r⟩ := by
        refine ⟨pre.reverse.length + 1, ?_⟩
        simpa [List.reverse_append, List.append_assoc] using hback
      have hnext :
          Reaches (machine cells)
            ⟨.core .CP_RET, l, mark, (pre ++ [last]) ++ copied :: r⟩
            (scanRightStart (.core .CP_SCAN) (pre ++ [last]) copied (mark :: l) r) := by
        refine ⟨1, ?_⟩
        cases pre <;> simp [stepN, step, Cfg.move, scanRightStart, hmark]
      exact reaches_trans henter (reaches_trans htoBlank' (reaches_trans hback' hnext))

/-- The same copy pass when the first blank is implicit, just beyond the represented right half. -/
theorem copyCellImplicit_reaches (cells : List Sy) (carry : Core) (x mark copied : Sy)
    (future l : List Sy) (hfuture : future ≠ [])
    (hstart : machine cells (.core .CP_SCAN) x =
      some (mark, .R, .core carry))
    (hcarry : ∀ y ∈ future,
      machine cells (.core carry) y = some (y, .R, .core carry))
    (hblank : machine cells (.core carry) .blank =
      some (copied, .L, .core .CP_RET))
    (hreturn : ∀ y ∈ future,
      machine cells (.core .CP_RET) y = some (y, .L, .core .CP_RET))
    (hmark : machine cells (.core .CP_RET) mark =
      some (mark, .R, .core .CP_SCAN)) :
    Reaches (machine cells)
      ⟨.core .CP_SCAN, l, x, future⟩
      (scanRightStart (.core .CP_SCAN) future copied (mark :: l) []) := by
  induction future using List.reverseRecOn with
  | nil => contradiction
  | append_singleton pre last =>
      have henter :
          Reaches (machine cells)
            ⟨.core .CP_SCAN, l, x, pre ++ [last]⟩
            ⟨.core carry, mark :: l, (pre ++ [last]).headD .blank,
              (pre ++ [last]).tail⟩ := by
        refine ⟨1, ?_⟩
        cases pre <;> simp [stepN, step, Cfg.move, hstart]
      have htoEnd := stepN_scanRightToImplicit (machine cells) (.core carry)
        (pre ++ [last]) (mark :: l) (by simp) (by
          intro y hy
          exact hcarry y (by simpa using hy))
      have htoEnd' :
          Reaches (machine cells)
            ⟨.core carry, mark :: l, (pre ++ [last]).headD .blank,
              (pre ++ [last]).tail⟩
            ⟨.core carry, (pre ++ [last]).reverse ++ mark :: l, .blank, []⟩ :=
        reaches_of_stepN htoEnd
      have hwrite :
          Reaches (machine cells)
            ⟨.core carry, (pre ++ [last]).reverse ++ mark :: l, .blank, []⟩
            ⟨.core .CP_RET, pre.reverse ++ mark :: l, last, [copied]⟩ := by
        refine ⟨1, ?_⟩
        simp [stepN, step, Cfg.move, hblank, List.reverse_append, List.append_assoc]
      have hback := stepN_scanLeft (machine cells) (.core .CP_RET) last pre.reverse
        (mark :: l) [copied] (by
          intro y hy
          apply hreturn y
          simpa [List.reverse_append, or_comm] using hy)
      have hback' :
          Reaches (machine cells)
            ⟨.core .CP_RET, pre.reverse ++ mark :: l, last, [copied]⟩
            ⟨.core .CP_RET, l, mark, (pre ++ [last]) ++ [copied]⟩ := by
        refine ⟨pre.reverse.length + 1, ?_⟩
        simpa [List.reverse_append, List.append_assoc] using hback
      have hnext :
          Reaches (machine cells)
            ⟨.core .CP_RET, l, mark, (pre ++ [last]) ++ [copied]⟩
            (scanRightStart (.core .CP_SCAN) (pre ++ [last]) copied (mark :: l) []) := by
        refine ⟨1, ?_⟩
        cases pre <;> simp [stepN, step, Cfg.move, scanRightStart, hmark]
      exact reaches_trans henter
        (reaches_trans htoEnd' (reaches_trans hwrite (reaches_trans hback' hnext)))

/-- A copy pass with any finite number of represented trailing blanks.  Writing consumes one
represented blank when available; once the list is exhausted, later writes use implicit blanks. -/
theorem copyCellBlanks_reaches (cells : List Sy) (carry : Core) (x mark copied : Sy)
    (future l : List Sy) (j : ℕ) (hfuture : future ≠ [])
    (hstart : machine cells (.core .CP_SCAN) x =
      some (mark, .R, .core carry))
    (hcarry : ∀ y ∈ future,
      machine cells (.core carry) y = some (y, .R, .core carry))
    (hblank : machine cells (.core carry) .blank =
      some (copied, .L, .core .CP_RET))
    (hreturn : ∀ y ∈ future,
      machine cells (.core .CP_RET) y = some (y, .L, .core .CP_RET))
    (hmark : machine cells (.core .CP_RET) mark =
      some (mark, .R, .core .CP_SCAN)) :
    Reaches (machine cells)
      ⟨.core .CP_SCAN, l, x, future ++ List.replicate j .blank⟩
      (scanRightStart (.core .CP_SCAN) future copied (mark :: l)
        (List.replicate (j - 1) .blank)) := by
  cases j with
  | zero =>
      simpa using copyCellImplicit_reaches cells carry x mark copied future l hfuture
        hstart hcarry hblank hreturn hmark
  | succ j =>
      have h := copyCell_reaches cells carry x mark copied future l
        (List.replicate j Sy.blank) hfuture hstart hcarry hblank hreturn hmark
      simpa [List.replicate_succ, List.append_assoc] using h

/-- Marks used on source cells while `CP_SCAN` copies the body of a block. -/
def copyMark : Sy → Sy
  | .P => .p
  | .d => .e
  | x => x

/-- `CP_SCAN` copies a whole `P`/`d` body up to (but not including) its final `z` marker. -/
theorem copyBody_reaches (cells : List Sy) (body out l : List Sy) (j : ℕ)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d)
    (hout : ∀ x ∈ out, x = .P ∨ x = .d) :
    Reaches (machine cells)
      (scanRightStart (.core .CP_SCAN) body .z l
        (out ++ List.replicate j .blank))
      ⟨.core .CP_SCAN, (body.map copyMark).reverse ++ l, .z,
        out ++ body ++ List.replicate (j - body.length) .blank⟩ := by
  induction body generalizing out l j with
  | nil =>
      simp [scanRightStart, reaches_refl]
  | cons x xs ih =>
      have hx : x = Sy.P ∨ x = Sy.d := hbody x (by simp)
      have hxs : ∀ y ∈ xs, y = Sy.P ∨ y = Sy.d := by
        intro y hy
        exact hbody y (by simp [hy])
      let future := xs ++ .z :: out
      have hfuture : future ≠ [] := by simp [future]
      have hfuture_symbols : ∀ y ∈ future, y = Sy.P ∨ y = Sy.d ∨ y = Sy.z := by
        intro y hy
        simp only [future, List.mem_append, List.mem_cons] at hy
        rcases hy with hy | rfl | hy
        · rcases hxs y hy with rfl | rfl
          · exact .inl rfl
          · exact .inr (.inl rfl)
        · exact .inr (.inr rfl)
        · rcases hout y hy with rfl | rfl
          · exact .inl rfl
          · exact .inr (.inl rfl)
      have hone :
          Reaches (machine cells)
            (scanRightStart (.core .CP_SCAN) (x :: xs) .z l
              (out ++ List.replicate j .blank))
            (scanRightStart (.core .CP_SCAN) xs .z (copyMark x :: l)
              ((out ++ [x]) ++ List.replicate (j - 1) .blank)) := by
        rcases hx with rfl | rfl
        · have h := copyCellBlanks_reaches cells .CARRY_P .P .p .P future l j hfuture
            rfl (by
              intro y hy
              rcases hfuture_symbols y hy with rfl | rfl | rfl <;> rfl)
            rfl (by
              intro y hy
              rcases hfuture_symbols y hy with rfl | rfl | rfl <;> rfl) rfl
          simpa [future, copyMark, scanRightStart_eq, List.append_assoc] using h
        · have h := copyCellBlanks_reaches cells .CARRY_D .d .e .d future l j hfuture
            rfl (by
              intro y hy
              rcases hfuture_symbols y hy with rfl | rfl | rfl <;> rfl)
            rfl (by
              intro y hy
              rcases hfuture_symbols y hy with rfl | rfl | rfl <;> rfl) rfl
          simpa [future, copyMark, scanRightStart_eq, List.append_assoc] using h
      have hout' : ∀ y ∈ out ++ [x], y = Sy.P ∨ y = Sy.d := by
        intro y hy
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hout y hy
        · exact hx
      have hrest := ih (out ++ [x]) (copyMark x :: l) (j - 1) hxs hout'
      have hlength : j - (xs.length + 1) = j - 1 - xs.length := by omega
      simpa [copyMark, List.append_assoc, hlength] using reaches_trans hone hrest

/-- The final `z` pass appends the copied final depth mark and returns to the source marker in
`CP_UNM`.  This includes both represented and implicit first-blank cases. -/
theorem copyFinal_reaches_cpUnm (cells : List Sy) (out left : List Sy) (j : ℕ)
    (hne : out ≠ []) (hout : ∀ x ∈ out, x = .P ∨ x = .d) :
    Reaches (machine cells)
      ⟨.core .CP_SCAN, left, .z, out ++ List.replicate j .blank⟩
      ⟨.core .CP_UNM, left.tail, left.headD .blank,
        .z :: out ++ .d :: List.replicate (j - 1) .blank⟩ := by
  have hcarry : ∀ x ∈ out,
      machine cells (.core .CARRY_DL) x = some (x, .R, .core .CARRY_DL) := by
    intro x hx
    rcases hout x hx with rfl | rfl <;> rfl
  have hend : ∀ x ∈ out,
      machine cells (.core .CP_END) x = some (x, .L, .core .CP_END) := by
    intro x hx
    rcases hout x hx with rfl | rfl <;> rfl
  have htoEnd :
      Reaches (machine cells)
        ⟨.core .CP_SCAN, left, .z, out ++ List.replicate j .blank⟩
        ⟨.core .CP_END, (out.reverse ++ .y :: left).tail,
          (out.reverse ++ .y :: left).headD .blank,
          .d :: List.replicate (j - 1) .blank⟩ := by
    cases j with
    | zero =>
        have henter :
            Reaches (machine cells)
              ⟨.core .CP_SCAN, left, .z, out⟩
              ⟨.core .CARRY_DL, .y :: left, out.headD .blank, out.tail⟩ := ⟨1, rfl⟩
        have hscan := stepN_scanRightToImplicit (machine cells) (.core .CARRY_DL)
          out (.y :: left) hne hcarry
        have hscan' :
            Reaches (machine cells)
              ⟨.core .CARRY_DL, .y :: left, out.headD .blank, out.tail⟩
              ⟨.core .CARRY_DL, out.reverse ++ .y :: left, .blank, []⟩ :=
          reaches_of_stepN hscan
        have hwrite :
            Reaches (machine cells)
              ⟨.core .CARRY_DL, out.reverse ++ .y :: left, .blank, []⟩
              ⟨.core .CP_END, (out.reverse ++ .y :: left).tail,
                (out.reverse ++ .y :: left).headD .blank, [.d]⟩ := ⟨1, rfl⟩
        simpa using reaches_trans henter (reaches_trans hscan' hwrite)
    | succ j =>
        have henter :
            Reaches (machine cells)
              ⟨.core .CP_SCAN, left, .z,
                out ++ List.replicate (j + 1) .blank⟩
              (scanRightStart (.core .CARRY_DL) out .blank (.y :: left)
                (List.replicate j .blank)) := by
          refine ⟨1, ?_⟩
          cases out with
          | nil => contradiction
          | cons x xs =>
              rw [List.replicate_succ]
              rfl
        have hscan := stepN_scanRightUntilLeft (machine cells)
          (.core .CARRY_DL) (.core .CP_END) out .blank .d .y left
          (List.replicate j Sy.blank) hcarry rfl
        have hscan' :
            Reaches (machine cells)
              (scanRightStart (.core .CARRY_DL) out .blank (.y :: left)
                (List.replicate j .blank))
              ⟨.core .CP_END, (out.reverse ++ .y :: left).tail,
                (out.reverse ++ .y :: left).headD .blank,
                .d :: List.replicate j .blank⟩ := reaches_of_stepN hscan
        simpa using reaches_trans henter hscan'
  have hback := stepN_scanLeftReverse (machine cells) (.core .CP_END) out
    (.y :: left) (.d :: List.replicate (j - 1) Sy.blank) hne hend
  have hback' :
      Reaches (machine cells)
        ⟨.core .CP_END, (out.reverse ++ .y :: left).tail,
          (out.reverse ++ .y :: left).headD .blank,
          .d :: List.replicate (j - 1) .blank⟩
        ⟨.core .CP_END, left, .y,
          out ++ .d :: List.replicate (j - 1) .blank⟩ := by
    have hrev : out.reverse ≠ [] := by simpa using hne
    refine ⟨out.length, ?_⟩
    rw [tail_append_of_ne_nil out.reverse (.y :: left) hrev]
    have hhead : (out.reverse ++ .y :: left).headD Sy.blank =
        out.reverse.headD Sy.blank := by
      cases hr : out.reverse with
      | nil => contradiction
      | cons x xs => rfl
    rw [hhead]
    have hdefault : (default : Sy) = Sy.blank := rfl
    have hheadDefault : out.reverse.headD Sy.blank =
        out.reverse.headD (default : Sy) := by rw [hdefault]
    rw [hheadDefault]
    simpa using hback
  have hstop :
      Reaches (machine cells)
        ⟨.core .CP_END, left, .y, out ++ .d :: List.replicate (j - 1) .blank⟩
        ⟨.core .CP_UNM, left.tail, left.headD .blank,
          .z :: out ++ .d :: List.replicate (j - 1) .blank⟩ := ⟨1, rfl⟩
  exact reaches_trans htoEnd (reaches_trans hback' hstop)

/-- Restore a marked `P`/`d` source body and enter `REP_RET` just left of its initial `S`. -/
theorem copyUnmark_reaches_repRet (cells : List Sy) (body l r : List Sy)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d) :
    Reaches (machine cells)
      ⟨.core .CP_UNM, ((body.map copyMark).reverse ++ .s :: l).tail,
        ((body.map copyMark).reverse ++ .s :: l).headD .blank, r⟩
      ⟨.core .REP_RET, l.tail, l.headD .blank, .S :: body ++ r⟩ := by
  induction body using List.reverseRecOn generalizing r with
  | nil =>
      exact ⟨1, rfl⟩
  | append_singleton pre x ih =>
      have hx : x = Sy.P ∨ x = Sy.d := hbody x (by simp)
      have hpre : ∀ y ∈ pre, y = Sy.P ∨ y = Sy.d := by
        intro y hy
        exact hbody y (by simp [hy])
      have hone :
          Reaches (machine cells)
            ⟨.core .CP_UNM,
              (((pre ++ [x]).map copyMark).reverse ++ .s :: l).tail,
              (((pre ++ [x]).map copyMark).reverse ++ .s :: l).headD .blank, r⟩
            ⟨.core .CP_UNM, ((pre.map copyMark).reverse ++ .s :: l).tail,
              ((pre.map copyMark).reverse ++ .s :: l).headD .blank, x :: r⟩ := by
        rcases hx with rfl | rfl <;>
          simpa [copyMark, List.reverse_append] using
            (show Reaches (machine cells)
              ⟨.core .CP_UNM, (pre.map copyMark).reverse ++ .s :: l, _, r⟩
              ⟨.core .CP_UNM, ((pre.map copyMark).reverse ++ .s :: l).tail,
                ((pre.map copyMark).reverse ++ .s :: l).headD .blank, _ :: r⟩ from ⟨1, rfl⟩)
      have hrest := ih (x :: r) hpre
      simpa [List.append_assoc] using reaches_trans hone hrest

/-- One complete `CP_SCAN/CARRY_*/CP_RET/CP_END/CP_UNM` loop copies `[S] ++ body ++ [z]`
as `[P] ++ body ++ [d]`, after any already appended `P`/`d` cells, and returns left in
`REP_RET`. -/
theorem copyBlockThrough_reaches_repRet (cells : List Sy) (body out l : List Sy) (j : ℕ)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d)
    (hout : ∀ x ∈ out, x = .P ∨ x = .d) :
    Reaches (machine cells)
      ⟨.core .CP_SCAN, l, .S, body ++ .z :: out ++ List.replicate j .blank⟩
      ⟨.core .REP_RET, l.tail, l.headD .blank,
        .S :: body ++ .z :: out ++ .P :: body ++ .d ::
          List.replicate (j - (body.length + 2)) .blank⟩ := by
  let future := body ++ .z :: out
  have hfuture : future ≠ [] := by simp [future]
  have hsymbols : ∀ x ∈ future, x = Sy.P ∨ x = Sy.d ∨ x = Sy.z := by
    intro x hx
    simp only [future, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · rcases hbody x hx with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
    · rcases hout x hx with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
  have hstart := copyCellBlanks_reaches cells .CARRY_P .S .s .P future l j hfuture
    rfl (by
      intro x hx
      rcases hsymbols x hx with rfl | rfl | rfl <;> rfl)
    rfl (by
      intro x hx
      rcases hsymbols x hx with rfl | rfl | rfl <;> rfl) rfl
  have hstart' :
      Reaches (machine cells)
        ⟨.core .CP_SCAN, l, .S, body ++ .z :: out ++ List.replicate j .blank⟩
        (scanRightStart (.core .CP_SCAN) body .z (.s :: l)
          ((out ++ [.P]) ++ List.replicate (j - 1) .blank)) := by
    simpa [future, scanRightStart_eq, List.append_assoc] using hstart
  have houtP : ∀ x ∈ out ++ [Sy.P], x = Sy.P ∨ x = Sy.d := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hout x hx
    · exact .inl rfl
  have hbodyCopy := copyBody_reaches cells body (out ++ [.P]) (.s :: l) (j - 1) hbody houtP
  have hbodyCopy' :
      Reaches (machine cells)
        (scanRightStart (.core .CP_SCAN) body .z (.s :: l)
          ((out ++ [.P]) ++ List.replicate (j - 1) .blank))
        ⟨.core .CP_SCAN, (body.map copyMark).reverse ++ .s :: l, .z,
          out ++ .P :: body ++ List.replicate (j - (body.length + 1)) .blank⟩ := by
    have hsub : j - 1 - body.length = j - (body.length + 1) := by omega
    simpa [hsub, List.append_assoc] using hbodyCopy
  have houtBody : ∀ x ∈ out ++ Sy.P :: body, x = Sy.P ∨ x = Sy.d := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hout x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inl rfl
      · exact hbody x hx
  have hfinal := copyFinal_reaches_cpUnm cells (out ++ .P :: body)
    ((body.map copyMark).reverse ++ .s :: l) (j - (body.length + 1)) (by simp) houtBody
  have hfinal' :
      Reaches (machine cells)
        ⟨.core .CP_SCAN, (body.map copyMark).reverse ++ .s :: l, .z,
          out ++ .P :: body ++ List.replicate (j - (body.length + 1)) .blank⟩
        ⟨.core .CP_UNM,
          ((body.map copyMark).reverse ++ .s :: l).tail,
          ((body.map copyMark).reverse ++ .s :: l).headD .blank,
          .z :: out ++ .P :: body ++ .d ::
            List.replicate (j - (body.length + 2)) .blank⟩ := by
    have hsub : j - (body.length + 1) - 1 = j - (body.length + 2) := by omega
    simpa [hsub, List.append_assoc] using hfinal
  have hunmark := copyUnmark_reaches_repRet cells body l
    (.z :: out ++ .P :: body ++ .d ::
      List.replicate (j - (body.length + 2)) Sy.blank) hbody
  simpa [List.append_assoc] using reaches_trans hstart'
    (reaches_trans hbodyCopy' (reaches_trans hfinal' hunmark))

/-- The empty-output specialization of `copyBlockThrough_reaches_repRet`. -/
theorem copyBlock_reaches_repRet (cells : List Sy) (body l : List Sy) (j : ℕ)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d) :
    Reaches (machine cells)
      ⟨.core .CP_SCAN, l, .S, body ++ .z :: List.replicate j .blank⟩
      ⟨.core .REP_RET, l.tail, l.headD .blank,
        .S :: body ++ .z :: .P :: body ++ .d ::
          List.replicate (j - (body.length + 2)) .blank⟩ := by
  simpa using copyBlockThrough_reaches_repRet cells body [] l j hbody (by simp)

/-- The unmarked `P`/`d` body between the initial `S` and final `z` of a marked copy block. -/
def markedCopyBody (a : ℕ) (u : List ℕ) : List Sy :=
  (List.replicate (a + 1) Sy.d ++ treeCells u).dropLast

/-- For a positive-depth suffix, restoring the final `z` to `d` reconstructs the exact encoded
parent block. -/
theorem markedCopyBody_append_d (a : ℕ) (u : List ℕ)
    (hpositive : ∀ k ∈ u, 1 ≤ k) :
    markedCopyBody a u ++ [.d] = List.replicate (a + 1) .d ++ treeCells u := by
  have hshape : ∃ pre,
      List.replicate (a + 1) Sy.d ++ treeCells u = pre ++ [.d] := by
    induction u using List.reverseRecOn with
    | nil =>
        refine ⟨List.replicate a .d, ?_⟩
        simp [List.replicate_succ', replicate_append_cons_self]
    | append_singleton pre k _ =>
        have hk : 1 ≤ k := hpositive k (by simp)
        obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
        refine ⟨List.replicate (a + 1) .d ++ treeCells pre ++
          .P :: List.replicate q .d, ?_⟩
        simp [treeCells_append, treeCells_cons, List.replicate_succ',
          replicate_append_cons_self, List.append_assoc]
  obtain ⟨pre, hpre⟩ := hshape
  unfold markedCopyBody
  rw [hpre, List.dropLast_concat]

theorem markedCopyTail_eq (a : ℕ) (u : List ℕ) :
    markedCopyTail a u = markedCopyBody a u ++ [.z] := rfl

theorem mem_markedCopyBody {a : ℕ} {u : List ℕ} {x : Sy}
    (hx : x ∈ markedCopyBody a u) : x = .P ∨ x = .d := by
  have hx' : x ∈ List.replicate (a + 1) Sy.d ++ treeCells u := by
    exact List.mem_of_mem_dropLast hx
  rw [List.mem_append] at hx'
  rcases hx' with hx' | hx'
  · exact .inr (List.mem_replicate.mp hx').2
  · exact mem_treeCells hx'

/-- The complete copy-loop theorem specialized to the block produced by the parent/erase phase. -/
theorem markedCopyTail_reaches_repRet (cells : List Sy) (a : ℕ)
    (u : List ℕ) (left : List Sy) (j : ℕ) :
    Reaches (machine cells)
      ⟨.core .CP_SCAN, left, .S,
        markedCopyTail a u ++ List.replicate j .blank⟩
      ⟨.core .REP_RET, left.tail, left.headD .blank,
        .S :: markedCopyTail a u ++ .P :: markedCopyBody a u ++ .d ::
          List.replicate (j - (markedCopyBody a u).length - 2) .blank⟩ := by
  have hbody : ∀ x ∈ markedCopyBody a u, x = Sy.P ∨ x = Sy.d := by
    intro x hx
    exact mem_markedCopyBody hx
  have h := copyBlock_reaches_repRet cells (markedCopyBody a u) left j hbody
  simpa [markedCopyTail_eq, Nat.sub_sub, List.append_assoc] using h

/-- Canonical configuration of the base-counter replication loop.  `remaining` counters are
still `b`; `used` counters have been changed to `B`; `out` is the already appended output. -/
def repScanConfig (remaining used : ℕ) (front body out : List Sy) (j : ℕ) : Cfg St Sy :=
  let right := List.replicate used Sy.B ++ .lb :: front ++ .S :: body ++ .z :: out ++
    List.replicate j .blank
  match remaining with
  | 0 => ⟨.core .REP_SCAN, [], .blank, right⟩
  | n + 1 => ⟨.core .REP_SCAN, List.replicate n .b, .b, right⟩

/-- `REP_START` crosses the work region, then `REP_FIRST` reserves the rightmost base counter.
There must be at least one base counter; the machine's reachable chop configurations have at
least the original two. -/
theorem repStart_reaches_repScan (cells : List Sy) (remaining : ℕ)
    (front body out : List Sy) (j : ℕ) (hfront : ∀ x ∈ front, x ≠ .lb) :
    Reaches (machine cells)
      ⟨.core .REP_START,
        front.reverse ++ .lb :: List.replicate (remaining + 1) .b,
        .S, body ++ .z :: out ++ List.replicate j .blank⟩
      (repScanConfig remaining 1 front body out j) := by
  have hscan := stepN_scanLeft (machine cells) (.core .REP_START) .S front.reverse
    (.lb :: List.replicate (remaining + 1) Sy.b)
    (body ++ .z :: out ++ List.replicate j .blank) (by
      intro x hx
      have hx' : x = Sy.S ∨ x ∈ front.reverse := by simpa using hx
      rcases hx' with rfl | hx'
      · rfl
      · have hne : x ≠ Sy.lb := hfront x (by simpa using hx')
        cases x <;> try rfl
        exact (hne rfl).elim)
  have hscan' :
      Reaches (machine cells)
        ⟨.core .REP_START,
          front.reverse ++ .lb :: List.replicate (remaining + 1) .b,
          .S, body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .REP_START, List.replicate (remaining + 1) .b, .lb,
          front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩ := by
    refine ⟨front.reverse.length + 1, ?_⟩
    simpa [List.append_assoc] using hscan
  have hfirst :
      Reaches (machine cells)
        ⟨.core .REP_START, List.replicate (remaining + 1) .b, .lb,
          front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩
        (repScanConfig remaining 1 front body out j) := by
    refine ⟨2, ?_⟩
    cases remaining <;> rfl
  exact reaches_trans hscan' hfirst

/-- After marking one more base counter, `GO_S` crosses the used counters and the work prefix,
then executes the generated stay move into `CP_SCAN` on the source marker. -/
theorem goS_reaches_cpScan (cells : List Sy) (remaining used : ℕ)
    (front body out : List Sy) (j : ℕ) (hfront : ∀ x ∈ front, x ≠ .S) :
    Reaches (machine cells)
      (scanRightStart (.core .GO_S)
        (List.replicate used .B ++ .lb :: front) .S
        (.B :: List.replicate remaining .b)
        (body ++ .z :: out ++ List.replicate j .blank))
      ⟨.core .CP_SCAN,
        front.reverse ++ .lb :: List.replicate (used + 1) .B ++
          List.replicate remaining .b,
        .S, body ++ .z :: out ++ List.replicate j .blank⟩ := by
  let path := List.replicate used Sy.B ++ .lb :: front
  have hpath : path ≠ [] := by simp [path]
  have htoS' :
      Reaches (machine cells)
        (scanRightStart (.core .GO_S) path .S
          (.B :: List.replicate remaining .b)
          (body ++ .z :: out ++ List.replicate j .blank))
        ⟨.core .GO_S, path.reverse ++ .B :: List.replicate remaining .b,
          .S, body ++ .z :: out ++ List.replicate j .blank⟩ := by
    cases hp : path with
    | nil => contradiction
    | cons first rest =>
      have htoS := stepN_scanRight (machine cells) (.core .GO_S)
        first rest (.B :: List.replicate remaining Sy.b)
        (.S :: body ++ .z :: out ++ List.replicate j .blank) (by
          intro x hx
          have hxPath : x ∈ path := by simpa [hp] using hx
          dsimp [path] at hxPath
          rw [List.mem_append] at hxPath
          rcases hxPath with hxPath | hxPath
          · have : x = Sy.B := (List.mem_replicate.mp hxPath).2
            subst x
            rfl
          · rcases List.mem_cons.mp hxPath with rfl | hxPath
            · rfl
            · have hne : x ≠ Sy.S := hfront x hxPath
              cases x <;> try rfl
              exact (hne rfl).elim)
      exact reaches_of_stepN (by simpa [hp, scanRightStart] using htoS)
  have hstay :
      Reaches (machine cells)
        ⟨.core .GO_S, path.reverse ++ .B :: List.replicate remaining .b,
          .S, body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .CP_SCAN, path.reverse ++ .B :: List.replicate remaining .b,
          .S, body ++ .z :: out ++ List.replicate j .blank⟩ := by
    refine ⟨2, ?_⟩
    cases body with
    | nil => rfl
    | cons x xs => cases x <;> rfl
  have hboth := reaches_trans htoS' hstay
  simpa [path, List.reverse_append, List.reverse_replicate,
    List.replicate_succ', List.append_assoc] using hboth

/-- `REP_RET` crosses the work prefix back to `lb`, whose transition resumes `REP_SCAN`. -/
theorem repRet_reaches_repScan (cells : List Sy) (base : List Sy)
    (front right : List Sy) (hfrontSafe : ∀ x ∈ front, x ≠ .lb) :
    Reaches (machine cells)
      ⟨.core .REP_RET, (front.reverse ++ .lb :: base).tail,
        (front.reverse ++ .lb :: base).headD .blank, .S :: right⟩
      ⟨.core .REP_SCAN, base.tail, base.headD .blank, .lb :: front ++ .S :: right⟩ := by
  by_cases hfront : front = []
  · subst front
    exact ⟨1, rfl⟩
  · have hscan := stepN_scanLeftReverse (machine cells) (.core .REP_RET)
      front (.lb :: base) (.S :: right) hfront (by
        intro x hx
        have hne : x ≠ Sy.lb := hfrontSafe x hx
        cases x <;> try rfl
        exact (hne rfl).elim)
    have hscan' :
        Reaches (machine cells)
          ⟨.core .REP_RET, (front.reverse ++ .lb :: base).tail,
            (front.reverse ++ .lb :: base).headD .blank, .S :: right⟩
          ⟨.core .REP_RET, base, .lb, front ++ .S :: right⟩ := by
      have hrev : front.reverse ≠ [] := by simpa using hfront
      refine ⟨front.length, ?_⟩
      rw [tail_append_of_ne_nil front.reverse (.lb :: base) hrev]
      have hhead : (front.reverse ++ .lb :: base).headD Sy.blank =
          front.reverse.headD (default : Sy) := by
        simpa using headD_append_of_ne_nil front.reverse (.lb :: base) hrev
      rw [hhead]
      simpa using hscan
    exact reaches_trans hscan' ⟨1, rfl⟩

/-- The return pass followed by the `REP_SCAN` pass across all counters already marked `B`. -/
theorem repRet_reaches_repScanConfig (cells : List Sy) (remaining used : ℕ)
    (front body out : List Sy) (j : ℕ) (hfront : ∀ x ∈ front, x ≠ .lb) :
    Reaches (machine cells)
      ⟨.core .REP_RET,
        (front.reverse ++ Sy.lb :: List.replicate (used + 1) Sy.B ++
          List.replicate remaining Sy.b).tail,
        (front.reverse ++ Sy.lb :: List.replicate (used + 1) Sy.B ++
          List.replicate remaining Sy.b).headD .blank,
        .S :: body ++ .z :: out ++ List.replicate j .blank⟩
      (repScanConfig remaining (used + 1) front body out j) := by
  let base := List.replicate (used + 1) Sy.B ++ List.replicate remaining .b
  have hret := repRet_reaches_repScan cells base front
    (body ++ .z :: out ++ List.replicate j Sy.blank) hfront
  have hret' :
      Reaches (machine cells)
        ⟨.core .REP_RET, (front.reverse ++ .lb :: base).tail,
          (front.reverse ++ .lb :: base).headD .blank,
          .S :: body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .REP_SCAN, base.tail, base.headD .blank,
          .lb :: front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩ := by
    simpa [List.append_assoc] using hret
  have hscan := stepN_scanLeft (machine cells) (.core .REP_SCAN) .B
    (List.replicate used .B) (List.replicate remaining .b)
    (.lb :: front ++ .S :: body ++ .z :: out ++ List.replicate j .blank) (by
      intro x hx
      have : x = Sy.B := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact (List.mem_replicate.mp hx).2
      subst x
      rfl)
  have hscan' :
      Reaches (machine cells)
        ⟨.core .REP_SCAN, base.tail, base.headD .blank,
          .lb :: front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩
        (repScanConfig remaining (used + 1) front body out j) := by
    refine ⟨used + 1, ?_⟩
    cases remaining <;>
      simpa [show (default : Sy) = Sy.blank from rfl, base, repScanConfig,
        List.replicate_succ, replicate_append_cons_self, List.append_assoc] using hscan
  simpa [base, List.append_assoc] using reaches_trans hret' hscan'

/-- One nonfinal base-counter iteration: mark a counter, copy the source block after the existing
output, return to the base, and resume `REP_SCAN` with one fewer unmarked counter. -/
theorem repScanSucc_reaches (cells : List Sy) (remaining used : ℕ)
    (front body out : List Sy) (j : ℕ)
    (hfrontLb : ∀ x ∈ front, x ≠ .lb)
    (hfrontS : ∀ x ∈ front, x ≠ .S)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d)
    (hout : ∀ x ∈ out, x = .P ∨ x = .d) :
    Reaches (machine cells)
      (repScanConfig (remaining + 1) used front body out j)
      (repScanConfig remaining (used + 1) front body
        (out ++ .P :: body ++ [.d]) (j - (body.length + 2))) := by
  let path := List.replicate used Sy.B ++ .lb :: front
  have hmark :
      Reaches (machine cells)
        (repScanConfig (remaining + 1) used front body out j)
        (scanRightStart (.core .GO_S) path .S
          (.B :: List.replicate remaining .b)
          (body ++ .z :: out ++ List.replicate j .blank)) := by
    refine ⟨1, ?_⟩
    cases used <;>
      simp [repScanConfig, path, scanRightStart, List.replicate_succ,
        List.append_assoc] <;> rfl
  have hgo := goS_reaches_cpScan cells remaining used front body out j hfrontS
  have hout' : ∀ x ∈ out, x = Sy.P ∨ x = Sy.d := hout
  let left := front.reverse ++ .lb :: List.replicate (used + 1) Sy.B ++
    List.replicate remaining .b
  have hcopy := copyBlockThrough_reaches_repRet cells body out left j hbody hout'
  have hcopy' :
      Reaches (machine cells)
        ⟨.core .CP_SCAN, left, .S,
          body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .REP_RET, left.tail, left.headD .blank,
          .S :: body ++ .z :: out ++ .P :: body ++ .d ::
            List.replicate (j - (body.length + 2)) .blank⟩ := by
    simpa [List.append_assoc] using hcopy
  have hreturn := repRet_reaches_repScanConfig cells remaining used front body
    (out ++ .P :: body ++ [.d]) (j - (body.length + 2)) hfrontLb
  have hreturn' :
      Reaches (machine cells)
        ⟨.core .REP_RET, left.tail, left.headD .blank,
          .S :: body ++ .z :: out ++ .P :: body ++ .d ::
            List.replicate (j - (body.length + 2)) .blank⟩
        (repScanConfig remaining (used + 1) front body
          (out ++ .P :: body ++ [.d]) (j - (body.length + 2))) := by
    simpa [left, List.append_assoc] using hreturn
  have hall := reaches_trans hmark (reaches_trans hgo (reaches_trans hcopy' hreturn'))
  simpa [path, left, List.append_assoc] using hall

/-- The unmarked block appended by one pass of the copy loop. -/
def copiedBlock (body : List Sy) : List Sy :=
  .P :: body ++ [.d]

/-- The unmarked source block copied by the machine is precisely the tree encoding of the
rightmost parent and its surviving suffix. -/
theorem copiedBlock_markedCopyBody (a : ℕ) (u : List ℕ)
    (hpositive : ∀ k ∈ u, 1 ≤ k) :
    copiedBlock (markedCopyBody a u) = treeCells ((a + 1) :: u) := by
  simp only [copiedBlock, treeCells_cons]
  rw [List.cons_append, markedCopyBody_append_d a u hpositive]
  simp [List.cons_append]

theorem treeCells_flatten_replicate (n : ℕ) (block : List ℕ) :
    treeCells (List.replicate n block).flatten =
      (List.replicate n (treeCells block)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, treeCells_append, ih]

theorem mem_copiedBlock {body : List Sy} {x : Sy}
    (hbody : ∀ y ∈ body, y = .P ∨ y = .d) (hx : x ∈ copiedBlock body) :
    x = .P ∨ x = .d := by
  change x ∈ (Sy.P :: body) ++ [Sy.d] at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl rfl
    · exact hbody x hx
  · have : x = Sy.d := by simpa using hx
    exact .inr this

theorem mem_flatten_replicate_copiedBlock {body : List Sy} {n : ℕ} {x : Sy}
    (hbody : ∀ y ∈ body, y = .P ∨ y = .d)
    (hx : x ∈ (List.replicate n (copiedBlock body)).flatten) :
    x = .P ∨ x = .d := by
  rw [List.mem_flatten] at hx
  obtain ⟨block, hblock, hx⟩ := hx
  have : block = copiedBlock body := (List.mem_replicate.mp hblock).2
  subst block
  exact mem_copiedBlock hbody hx

/-- Induction over every still-unmarked base counter.  The existential blank count is deliberate:
the finite tape representation may exhaust its explicit blanks, after which writes use implicit
blanks, but the nonblank output is exact. -/
theorem repScanAll_reaches (cells : List Sy) (remaining used : ℕ)
    (front body out : List Sy) (j : ℕ)
    (hfrontLb : ∀ x ∈ front, x ≠ .lb)
    (hfrontS : ∀ x ∈ front, x ≠ .S)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d)
    (hout : ∀ x ∈ out, x = .P ∨ x = .d) :
    ∃ j', Reaches (machine cells)
      (repScanConfig remaining used front body out j)
      (repScanConfig 0 (used + remaining) front body
        (out ++ (List.replicate remaining (copiedBlock body)).flatten) j') := by
  induction remaining generalizing used out j with
  | zero =>
      exact ⟨j, by simpa using
        (reaches_refl (machine cells) (repScanConfig 0 used front body out j))⟩
  | succ n ih =>
      have hone := repScanSucc_reaches cells n used front body out j
        hfrontLb hfrontS hbody hout
      have hout' : ∀ x ∈ out ++ copiedBlock body, x = Sy.P ∨ x = Sy.d := by
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hout x hx
        · exact mem_copiedBlock hbody hx
      obtain ⟨j', hrest⟩ := ih (used + 1) (out ++ copiedBlock body)
        (j - (body.length + 2)) hout'
      refine ⟨j', ?_⟩
      have hone' :
          Reaches (machine cells)
            (repScanConfig (n + 1) used front body out j)
            (repScanConfig n (used + 1) front body
              (out ++ copiedBlock body) (j - (body.length + 2))) := by
        simpa [copiedBlock] using hone
      have hall := reaches_trans hone' hrest
      simpa [copiedBlock, List.replicate_succ, List.flatten_cons,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- Complete `REP_START/REP_FIRST/REP_SCAN/GO_S/.../REP_RET` replication phase.  A base of
`remaining + 1` produces exactly `remaining` copies, since `REP_FIRST` reserves one counter. -/
theorem repStart_reaches_repScanDone (cells : List Sy) (remaining : ℕ)
    (front body : List Sy) (j : ℕ)
    (hfrontLb : ∀ x ∈ front, x ≠ .lb)
    (hfrontS : ∀ x ∈ front, x ≠ .S)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d) :
    ∃ j', Reaches (machine cells)
      ⟨.core .REP_START,
        front.reverse ++ .lb :: List.replicate (remaining + 1) .b,
        .S, body ++ .z :: List.replicate j .blank⟩
      (repScanConfig 0 (remaining + 1) front body
        (List.replicate remaining (copiedBlock body)).flatten j') := by
  have hstart := repStart_reaches_repScan cells remaining front body [] j hfrontLb
  obtain ⟨j', hall⟩ := repScanAll_reaches cells remaining 1 front body [] j
    hfrontLb hfrontS hbody (by simp)
  refine ⟨j', ?_⟩
  simpa [Nat.add_comm] using reaches_trans hstart hall

/-! A deep chop leaves one represented blank immediately to the left of the unary base.  The
next deep chop reaches that blank rather than an implicit one.  The following wrappers retain
this one-bit padding invariant while reusing the copy-loop lemmas above. -/

def basePad (padded : Bool) : List Sy :=
  if padded then [.blank] else []

/-- Replication-loop configuration with either no represented blank or one represented blank to
the left of the base.  Once all counters are used, the two representations coincide at the
scanned blank. -/
def repScanConfigPadded (padded : Bool) (remaining used : ℕ)
    (front body out : List Sy) (j : ℕ) : Cfg St Sy :=
  let right := List.replicate used Sy.B ++ .lb :: front ++ .S :: body ++ .z :: out ++
    List.replicate j .blank
  match remaining with
  | 0 => ⟨.core .REP_SCAN, [], .blank, right⟩
  | n + 1 =>
      ⟨.core .REP_SCAN, List.replicate n .b ++ basePad padded, .b, right⟩

theorem repStart_reaches_repScanPadded (cells : List Sy) (padded : Bool) (remaining : ℕ)
    (front body out : List Sy) (j : ℕ) (hfront : ∀ x ∈ front, x ≠ .lb) :
    Reaches (machine cells)
      ⟨.core .REP_START,
        front.reverse ++ .lb ::
          (List.replicate (remaining + 1) .b ++ basePad padded),
        .S, body ++ .z :: out ++ List.replicate j .blank⟩
      (repScanConfigPadded padded remaining 1 front body out j) := by
  have hscan := stepN_scanLeft (machine cells) (.core .REP_START) .S front.reverse
    (.lb :: (List.replicate (remaining + 1) Sy.b ++ basePad padded))
    (body ++ .z :: out ++ List.replicate j .blank) (by
      intro x hx
      have hx' : x = Sy.S ∨ x ∈ front.reverse := by simpa using hx
      rcases hx' with rfl | hx'
      · rfl
      · have hne : x ≠ Sy.lb := hfront x (by simpa using hx')
        cases x <;> try rfl
        exact (hne rfl).elim)
  have hscan' :
      Reaches (machine cells)
        ⟨.core .REP_START,
          front.reverse ++ .lb ::
            (List.replicate (remaining + 1) .b ++ basePad padded),
          .S, body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .REP_START,
          List.replicate (remaining + 1) .b ++ basePad padded, .lb,
          front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩ := by
    refine ⟨front.reverse.length + 1, ?_⟩
    simpa [List.append_assoc] using hscan
  have hfirst :
      Reaches (machine cells)
        ⟨.core .REP_START,
          List.replicate (remaining + 1) .b ++ basePad padded, .lb,
          front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩
        (repScanConfigPadded padded remaining 1 front body out j) := by
    refine ⟨2, ?_⟩
    cases remaining <;> cases padded <;> rfl
  exact reaches_trans hscan' hfirst

theorem goS_reaches_cpScanPadded (cells : List Sy) (padded : Bool)
    (remaining used : ℕ) (front body out : List Sy) (j : ℕ)
    (hfront : ∀ x ∈ front, x ≠ .S) :
    Reaches (machine cells)
      (scanRightStart (.core .GO_S)
        (List.replicate used .B ++ .lb :: front) .S
        (.B :: List.replicate remaining .b ++ basePad padded)
        (body ++ .z :: out ++ List.replicate j .blank))
      ⟨.core .CP_SCAN,
        front.reverse ++ .lb :: List.replicate (used + 1) .B ++
          List.replicate remaining .b ++ basePad padded,
        .S, body ++ .z :: out ++ List.replicate j .blank⟩ := by
  let path := List.replicate used Sy.B ++ .lb :: front
  have hpath : path ≠ [] := by simp [path]
  have htoS' :
      Reaches (machine cells)
        (scanRightStart (.core .GO_S) path .S
          (.B :: List.replicate remaining .b ++ basePad padded)
          (body ++ .z :: out ++ List.replicate j .blank))
        ⟨.core .GO_S,
          path.reverse ++ .B :: List.replicate remaining .b ++ basePad padded,
          .S, body ++ .z :: out ++ List.replicate j .blank⟩ := by
    cases hp : path with
    | nil => contradiction
    | cons first rest =>
      have htoS := stepN_scanRight (machine cells) (.core .GO_S)
        first rest (.B :: List.replicate remaining Sy.b ++ basePad padded)
        (.S :: body ++ .z :: out ++ List.replicate j .blank) (by
          intro x hx
          have hxPath : x ∈ path := by simpa [hp] using hx
          dsimp [path] at hxPath
          rw [List.mem_append] at hxPath
          rcases hxPath with hxPath | hxPath
          · have : x = Sy.B := (List.mem_replicate.mp hxPath).2
            subst x
            rfl
          · rcases List.mem_cons.mp hxPath with rfl | hxPath
            · rfl
            · have hne : x ≠ Sy.S := hfront x hxPath
              cases x <;> try rfl
              exact (hne rfl).elim)
      exact reaches_of_stepN (by simpa [hp, scanRightStart] using htoS)
  have hstay :
      Reaches (machine cells)
        ⟨.core .GO_S,
          path.reverse ++ .B :: List.replicate remaining .b ++ basePad padded,
          .S, body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .CP_SCAN,
          path.reverse ++ .B :: List.replicate remaining .b ++ basePad padded,
          .S, body ++ .z :: out ++ List.replicate j .blank⟩ := by
    refine ⟨2, ?_⟩
    cases body with
    | nil => rfl
    | cons x xs => cases x <;> rfl
  have hboth := reaches_trans htoS' hstay
  simpa [path, List.reverse_append, List.reverse_replicate,
    List.replicate_succ', List.append_assoc] using hboth

theorem repRet_reaches_repScanConfigPadded (cells : List Sy) (padded : Bool)
    (remaining used : ℕ) (front body out : List Sy) (j : ℕ)
    (hfront : ∀ x ∈ front, x ≠ .lb) :
    Reaches (machine cells)
      ⟨.core .REP_RET,
        (front.reverse ++ Sy.lb :: List.replicate (used + 1) Sy.B ++
          List.replicate remaining Sy.b ++ basePad padded).tail,
        (front.reverse ++ Sy.lb :: List.replicate (used + 1) Sy.B ++
          List.replicate remaining Sy.b ++ basePad padded).headD .blank,
        .S :: body ++ .z :: out ++ List.replicate j .blank⟩
      (repScanConfigPadded padded remaining (used + 1) front body out j) := by
  let base := List.replicate (used + 1) Sy.B ++
    List.replicate remaining .b ++ basePad padded
  have hret := repRet_reaches_repScan cells base front
    (body ++ .z :: out ++ List.replicate j Sy.blank) hfront
  have hret' :
      Reaches (machine cells)
        ⟨.core .REP_RET, (front.reverse ++ .lb :: base).tail,
          (front.reverse ++ .lb :: base).headD .blank,
          .S :: body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .REP_SCAN, base.tail, base.headD .blank,
          .lb :: front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩ := by
    simpa [List.append_assoc] using hret
  have hscan := stepN_scanLeft (machine cells) (.core .REP_SCAN) .B
    (List.replicate used .B)
    (List.replicate remaining .b ++ basePad padded)
    (.lb :: front ++ .S :: body ++ .z :: out ++ List.replicate j .blank) (by
      intro x hx
      have : x = Sy.B := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact (List.mem_replicate.mp hx).2
      subst x
      rfl)
  have hscan' :
      Reaches (machine cells)
        ⟨.core .REP_SCAN, base.tail, base.headD .blank,
          .lb :: front ++ .S :: body ++ .z :: out ++ List.replicate j .blank⟩
        (repScanConfigPadded padded remaining (used + 1) front body out j) := by
    refine ⟨used + 1, ?_⟩
    cases remaining <;> cases padded <;>
      simpa [show (default : Sy) = Sy.blank from rfl, base, basePad,
        repScanConfigPadded, List.replicate_succ, replicate_append_cons_self,
        List.append_assoc] using hscan
  simpa [base, List.append_assoc] using reaches_trans hret' hscan'

theorem repScanSucc_reachesPadded (cells : List Sy) (padded : Bool)
    (remaining used : ℕ) (front body out : List Sy) (j : ℕ)
    (hfrontLb : ∀ x ∈ front, x ≠ .lb)
    (hfrontS : ∀ x ∈ front, x ≠ .S)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d)
    (hout : ∀ x ∈ out, x = .P ∨ x = .d) :
    Reaches (machine cells)
      (repScanConfigPadded padded (remaining + 1) used front body out j)
      (repScanConfigPadded padded remaining (used + 1) front body
        (out ++ .P :: body ++ [.d]) (j - (body.length + 2))) := by
  let path := List.replicate used Sy.B ++ .lb :: front
  have hmark :
      Reaches (machine cells)
        (repScanConfigPadded padded (remaining + 1) used front body out j)
        (scanRightStart (.core .GO_S) path .S
          (.B :: List.replicate remaining .b ++ basePad padded)
          (body ++ .z :: out ++ List.replicate j .blank)) := by
    refine ⟨1, ?_⟩
    cases used <;>
      simp [repScanConfigPadded, path, scanRightStart, List.replicate_succ,
        List.append_assoc] <;> rfl
  have hgo := goS_reaches_cpScanPadded cells padded remaining used
    front body out j hfrontS
  let left := front.reverse ++ .lb :: List.replicate (used + 1) Sy.B ++
    List.replicate remaining .b ++ basePad padded
  have hcopy := copyBlockThrough_reaches_repRet cells body out left j hbody hout
  have hcopy' :
      Reaches (machine cells)
        ⟨.core .CP_SCAN, left, .S,
          body ++ .z :: out ++ List.replicate j .blank⟩
        ⟨.core .REP_RET, left.tail, left.headD .blank,
          .S :: body ++ .z :: out ++ .P :: body ++ .d ::
            List.replicate (j - (body.length + 2)) .blank⟩ := by
    simpa [List.append_assoc] using hcopy
  have hreturn := repRet_reaches_repScanConfigPadded cells padded remaining used front body
    (out ++ .P :: body ++ [.d]) (j - (body.length + 2)) hfrontLb
  have hreturn' :
      Reaches (machine cells)
        ⟨.core .REP_RET, left.tail, left.headD .blank,
          .S :: body ++ .z :: out ++ .P :: body ++ .d ::
            List.replicate (j - (body.length + 2)) .blank⟩
        (repScanConfigPadded padded remaining (used + 1) front body
          (out ++ .P :: body ++ [.d]) (j - (body.length + 2))) := by
    simpa [left, List.append_assoc] using hreturn
  have hall := reaches_trans hmark (reaches_trans hgo (reaches_trans hcopy' hreturn'))
  simpa [path, left, List.append_assoc] using hall

theorem repScanAll_reachesPadded (cells : List Sy) (padded : Bool)
    (remaining used : ℕ) (front body out : List Sy) (j : ℕ)
    (hfrontLb : ∀ x ∈ front, x ≠ .lb)
    (hfrontS : ∀ x ∈ front, x ≠ .S)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d)
    (hout : ∀ x ∈ out, x = .P ∨ x = .d) :
    ∃ j', Reaches (machine cells)
      (repScanConfigPadded padded remaining used front body out j)
      (repScanConfigPadded padded 0 (used + remaining) front body
        (out ++ (List.replicate remaining (copiedBlock body)).flatten) j') := by
  induction remaining generalizing used out j with
  | zero =>
      exact ⟨j, by simpa using
        (reaches_refl (machine cells)
          (repScanConfigPadded padded 0 used front body out j))⟩
  | succ n ih =>
      have hone := repScanSucc_reachesPadded cells padded n used front body out j
        hfrontLb hfrontS hbody hout
      have hout' : ∀ x ∈ out ++ copiedBlock body, x = Sy.P ∨ x = Sy.d := by
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hout x hx
        · exact mem_copiedBlock hbody hx
      obtain ⟨j', hrest⟩ := ih (used + 1) (out ++ copiedBlock body)
        (j - (body.length + 2)) hout'
      refine ⟨j', ?_⟩
      have hone' :
          Reaches (machine cells)
            (repScanConfigPadded padded (n + 1) used front body out j)
            (repScanConfigPadded padded n (used + 1) front body
              (out ++ copiedBlock body) (j - (body.length + 2))) := by
        simpa [copiedBlock] using hone
      have hall := reaches_trans hone' hrest
      simpa [copiedBlock, List.replicate_succ, List.flatten_cons,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- Padded version of the complete base-counter replication phase. -/
theorem repStart_reaches_repScanDonePadded (cells : List Sy) (padded : Bool)
    (remaining : ℕ) (front body : List Sy) (j : ℕ)
    (hfrontLb : ∀ x ∈ front, x ≠ .lb)
    (hfrontS : ∀ x ∈ front, x ≠ .S)
    (hbody : ∀ x ∈ body, x = .P ∨ x = .d) :
    ∃ j', Reaches (machine cells)
      ⟨.core .REP_START,
        front.reverse ++ .lb ::
          (List.replicate (remaining + 1) .b ++ basePad padded),
        .S, body ++ .z :: List.replicate j .blank⟩
      (repScanConfig 0 (remaining + 1) front body
        (List.replicate remaining (copiedBlock body)).flatten j') := by
  have hstart := repStart_reaches_repScanPadded cells padded remaining
    front body [] j hfrontLb
  obtain ⟨j', hall⟩ := repScanAll_reachesPadded cells padded remaining 1
    front body [] j hfrontLb hfrontS hbody (by simp)
  refine ⟨j', ?_⟩
  have hboth := reaches_trans hstart hall
  simpa [repScanConfig, repScanConfigPadded, Nat.add_comm] using hboth

/-- The all-`B` exit of the replicate loop restores the unary base and the two endpoints of the
source block.  The resulting `GO_CHOP` configuration scans the first appended output cell, or the
first explicit/implicit blank when the output is empty. -/
theorem repScanDone_reaches_goChop (cells : List Sy) (used : ℕ)
    (front body out : List Sy) (j : ℕ)
    (hfront : ∀ x ∈ front, x ≠ .S)
    (hbody : ∀ x ∈ body, x ≠ .z) :
    Reaches (machine cells)
      (repScanConfig 0 used front body out j)
      ⟨.core .GO_CHOP,
        .d :: body.reverse ++ .P :: front.reverse ++ .lb ::
          List.replicate used .b ++ [.blank],
        (out ++ List.replicate j Sy.blank).headD Sy.blank,
        (out ++ List.replicate j Sy.blank).tail⟩ := by
  let tail := out ++ List.replicate j Sy.blank
  have henter :
      Reaches (machine cells)
        (repScanConfig 0 used front body out j)
        (scanRightStart (.core .REP_DONE) (List.replicate used .B) .lb [.blank]
          (front ++ .S :: body ++ .z :: tail)) := by
    have hstep : machine cells (.core .REP_SCAN) .blank =
        some (.blank, .R, .core .REP_DONE) := rfl
    refine ⟨1, ?_⟩
    cases used <;>
      simp [repScanConfig, scanRightStart, tail, stepN, step, Cfg.move,
        hstep, List.replicate_succ, List.append_assoc]
  have hbaseStep := stepN_scanRightMapUntilRight (machine cells)
    (.core .REP_DONE) (.core .RD_S) (fun _ : Sy => Sy.b)
    (List.replicate used .B) front .lb .lb .S [.blank]
    (body ++ .z :: tail) (by
      intro x hx
      have : x = Sy.B := (List.mem_replicate.mp hx).2
      subst x
      rfl) rfl
  have hbase :
      Reaches (machine cells)
        (scanRightStart (.core .REP_DONE) (List.replicate used .B) .lb [.blank]
          (front ++ .S :: body ++ .z :: tail))
        (scanRightStart (.core .RD_S) front .S
          (.lb :: List.replicate used .b ++ [.blank]) (body ++ .z :: tail)) := by
    apply reaches_of_stepN
    simpa [List.map_replicate, List.reverse_replicate, List.append_assoc] using hbaseStep
  have hsourceStep := stepN_scanRightUntilRight (machine cells)
    (.core .RD_S) (.core .RD_Z) front body .S .P .z
    (.lb :: List.replicate used .b ++ [.blank]) tail (by
      intro x hx
      have hne := hfront x hx
      cases x <;> try rfl
      exact (hne rfl).elim) rfl
  have hsource :
      Reaches (machine cells)
        (scanRightStart (.core .RD_S) front .S
          (.lb :: List.replicate used .b ++ [.blank]) (body ++ .z :: tail))
        (scanRightStart (.core .RD_Z) body .z
          (.P :: front.reverse ++ .lb :: List.replicate used .b ++ [.blank]) tail) := by
    exact reaches_of_stepN (by simpa [List.append_assoc] using hsourceStep)
  have hendStep := stepN_scanRightUntilRightTail (machine cells)
    (.core .RD_Z) (.core .GO_CHOP) body .z .d
    (.P :: front.reverse ++ .lb :: List.replicate used .b ++ [.blank]) tail (by
      intro x hx
      have hne := hbody x hx
      cases x <;> try rfl
      exact (hne rfl).elim) rfl
  have hend :
      Reaches (machine cells)
        (scanRightStart (.core .RD_Z) body .z
          (.P :: front.reverse ++ .lb :: List.replicate used .b ++ [.blank]) tail)
        ⟨.core .GO_CHOP,
          .d :: body.reverse ++ .P :: front.reverse ++ .lb ::
            List.replicate used .b ++ [.blank],
          tail.headD Sy.blank, tail.tail⟩ := by
    exact reaches_of_stepN (by
      simpa [show (default : Sy) = Sy.blank from rfl, List.append_assoc] using hendStep)
  simpa [tail] using reaches_trans henter (reaches_trans hbase (reaches_trans hsource hend))

/-- `GO_CHOP` crosses a nonempty nonblank output block and turns around on its first represented
or implicit blank.  At least one explicit blank is present in the resulting `CHOP_START`
configuration. -/
theorem goChop_reaches_chopStart (cells : List Sy) (left out : List Sy) (j : ℕ)
    (houtNe : out ≠ []) (hout : ∀ x ∈ out, x ≠ .blank) :
    ∃ j', 1 ≤ j' ∧ Reaches (machine cells)
      ⟨.core .GO_CHOP, left, out.headD .blank,
        out.tail ++ List.replicate j .blank⟩
      ⟨.core .CHOP_START, (out.reverse ++ left).tail,
        (out.reverse ++ left).headD .blank, List.replicate j' .blank⟩ := by
  cases j with
  | zero =>
      have hscan := stepN_scanRightToImplicit (machine cells) (.core .GO_CHOP)
        out left houtNe (by
          intro x hx
          have hne := hout x hx
          cases x <;> try rfl
          exact (hne rfl).elim)
      have hturn :
          Reaches (machine cells)
            ⟨.core .GO_CHOP, out.reverse ++ left, .blank, []⟩
            ⟨.core .CHOP_START, (out.reverse ++ left).tail,
              (out.reverse ++ left).headD .blank, [.blank]⟩ := ⟨1, rfl⟩
      refine ⟨1, by omega, ?_⟩
      simpa [show (default : Sy) = Sy.blank from rfl] using
        reaches_trans (reaches_of_stepN hscan) hturn
  | succ j =>
      obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil houtNe
      have hscan := stepN_scanRight (machine cells) (.core .GO_CHOP)
        first rest left (.blank :: List.replicate j .blank) (by
          intro x hx
          have hne := hout x (by simpa using hx)
          cases x <;> try rfl
          exact (hne rfl).elim)
      have hturn :
          Reaches (machine cells)
            ⟨.core .GO_CHOP, (first :: rest).reverse ++ left, .blank,
              List.replicate j .blank⟩
            ⟨.core .CHOP_START, ((first :: rest).reverse ++ left).tail,
              ((first :: rest).reverse ++ left).headD .blank,
              List.replicate (j + 1) .blank⟩ := by
        refine ⟨1, ?_⟩
        rfl
      refine ⟨j + 1, by omega, ?_⟩
      have hscan' :
          Reaches (machine cells)
            ⟨.core .GO_CHOP, left, first,
              rest ++ List.replicate (j + 1) .blank⟩
        ⟨.core .GO_CHOP, (first :: rest).reverse ++ left, .blank,
              List.replicate j .blank⟩ := by
        apply reaches_of_stepN
        simpa [List.replicate_succ, List.append_assoc] using hscan
      exact reaches_trans hscan' hturn

/-- Specialization of the erase phase to the canonical parent-search output.  The suffix depths
are positive, so the final symbol of a nonempty suffix encoding is a depth mark; for an empty
suffix the final parent-depth mark is used instead. -/
theorem parentFound_reaches_repStart (cells : List Sy) (a : ℕ)
    (u : List ℕ) (l r : List Sy) (hpositive : ∀ k ∈ u, 1 ≤ k) :
    Reaches (machine cells)
      ⟨.core .PAR_END,
        .d :: List.replicate (a + 1) .D ++ .T ::
          (treeCells u).reverse ++ List.replicate (a + 1) .D ++ .C :: l,
        .blank, r⟩
      ⟨.core .REP_START, l, .S,
        markedCopyTail a u ++ List.replicate (a + 4) .blank ++ r⟩ := by
  induction u using List.reverseRecOn with
  | nil =>
      have h := eraseLeaf_reaches_repStart cells a Sy.D
        (List.replicate a Sy.D) l r (.inr rfl) (by
          intro x hx
          exact .inr (.inr (List.mem_replicate.mp hx).2))
      simpa [markedCopyTail, restoreD, List.map_replicate,
        List.reverse_replicate, List.replicate_succ,
        replicate_append_cons_self, List.append_assoc] using h
  | append_singleton pre k _ =>
      have hk : 1 ≤ k := hpositive k (by simp)
      obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
      let front := List.replicate (a + 1) Sy.D ++ treeCells pre ++
        Sy.P :: List.replicate q Sy.d
      have htree : treeCells (pre ++ [q + 1]) =
          treeCells pre ++ Sy.P :: List.replicate q Sy.d ++ [Sy.d] := by
        rw [treeCells_append, treeCells_cons]
        simp [List.replicate_succ', List.append_assoc]
      have hmarked : markedCopyTail a (pre ++ [q + 1]) =
          List.replicate (a + 1) Sy.d ++ treeCells pre ++
            Sy.P :: List.replicate q Sy.d ++ [Sy.z] := by
        unfold markedCopyTail
        rw [htree]
        have hconcat : List.replicate (a + 1) Sy.d ++
              (treeCells pre ++ Sy.P :: List.replicate q Sy.d ++ [Sy.d]) =
            (List.replicate (a + 1) Sy.d ++ treeCells pre ++
              Sy.P :: List.replicate q Sy.d) ++ [Sy.d] := by
          simp [List.append_assoc]
        rw [hconcat, List.dropLast_concat]
      have hfront : ∀ x ∈ front, x = Sy.P ∨ x = Sy.d ∨ x = Sy.D := by
        intro x hx
        dsimp [front] at hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · rw [List.mem_append] at hx
          rcases hx with hx | hx
          · exact .inr (.inr (List.mem_replicate.mp hx).2)
          · rcases mem_treeCells hx with rfl | rfl
            · exact .inl rfl
            · exact .inr (.inl rfl)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inl rfl
          · exact .inr (.inl (List.mem_replicate.mp hx).2)
      have h := eraseLeaf_reaches_repStart cells a Sy.d front l r (.inl rfl) hfront
      rw [hmarked]
      simpa [front, htree,
        restoreD, map_restoreD_treeCells, List.map_append, List.map_replicate,
        List.reverse_append, List.reverse_replicate, List.replicate_succ',
        replicate_append_cons_self, List.append_assoc] using h

/-- The full search-and-erase prefix of a deep chop.  Starting on the final depth mark of a
well-formed tree, the machine finds the rightmost parent, deletes the leaf, and presents the
exact marked parent block to the replicate loop. -/
theorem chopStart_reaches_repStart_of_wf (cells : List Sy) (a : ℕ)
    (s : List ℕ) (l r : List Sy) (ht : WF (s ++ [a + 2])) :
    ∃ p u, s = p ++ (a + 1) :: u ∧
      Reaches (machine cells)
        ⟨.core .CHOP_START,
          List.replicate (a + 1) .d ++ .P :: (treeCells s).reverse ++ l,
          .d, .blank :: r⟩
        ⟨.core .REP_START, (treeCells p).reverse ++ l, .S,
          markedCopyTail a u ++ List.replicate (a + 4) .blank ++ r⟩ := by
  obtain ⟨p, u, hsplit, hparent⟩ :=
    chopStart_reaches_parent_of_wf cells a s l r ht
  have hpositive : ∀ k ∈ u, 1 ≤ k := by
    intro k hk
    apply wf_mem_lower ht
    rw [hsplit]
    simp [hk]
  have herase := parentFound_reaches_repStart cells a u
    ((treeCells p).reverse ++ l) r hpositive
  have hparent' := hparent
  simp only [List.cons_append, List.append_assoc] at hparent'
  have herase' := herase
  simp only [List.cons_append, List.append_assoc] at herase'
  refine ⟨p, u, hsplit, ?_⟩
  simpa [List.cons_append, List.append_assoc] using reaches_trans hparent' herase'

/-- Strengthened search-and-erase theorem retaining the defining rightmost-parent property.  This
property is what identifies the copied suffix with `parentBlock` in the executable hydra move. -/
theorem chopStart_reaches_repStart_of_wf_deep (cells : List Sy) (a : ℕ)
    (s : List ℕ) (l r : List Sy) (ht : WF (s ++ [a + 2])) :
    ∃ p u, s = p ++ (a + 1) :: u ∧ (∀ k ∈ u, a + 2 ≤ k) ∧
      Reaches (machine cells)
        ⟨.core .CHOP_START,
          List.replicate (a + 1) .d ++ .P :: (treeCells s).reverse ++ l,
          .d, .blank :: r⟩
        ⟨.core .REP_START, (treeCells p).reverse ++ l, .S,
          markedCopyTail a u ++ List.replicate (a + 4) .blank ++ r⟩ := by
  obtain ⟨p, u, hsplit, hdeep⟩ := exists_parent_split_of_wf ht (by omega)
  have hsplit' : s = p ++ (a + 1) :: u := by simpa using hsplit
  have hsearch := chopStartThrough_reaches_parent cells a u
    ((treeCells p).reverse ++ l) r (by
      intro k hk
      have := hdeep k hk
      omega)
  have hpositive : ∀ k ∈ u, 1 ≤ k := by
    intro k hk
    have := hdeep k hk
    omega
  have herase := parentFound_reaches_repStart cells a u
    ((treeCells p).reverse ++ l) r hpositive
  have hparent :
      Reaches (machine cells)
        ⟨.core .CHOP_START,
          List.replicate (a + 1) .d ++ .P :: (treeCells s).reverse ++ l,
          .d, .blank :: r⟩
        ⟨.core .PAR_END,
          .d :: List.replicate (a + 1) .D ++ .T ::
            (treeCells u).reverse ++ List.replicate (a + 1) .D ++
              .C :: (treeCells p).reverse ++ l,
          .blank, r⟩ := by
    rw [hsplit']
    simpa [List.reverse_append, List.reverse_replicate, List.replicate_succ,
      replicate_append_cons_self, List.append_assoc] using hsearch
  refine ⟨p, u, hsplit', hdeep, ?_⟩
  have hparent' := hparent
  simp only [List.cons_append, List.append_assoc] at hparent'
  have herase' := herase
  simp only [List.cons_append, List.append_assoc] at herase'
  simpa [List.cons_append, List.append_assoc] using reaches_trans hparent' herase'

private theorem rtakeWhile_append_eq_right_of_nil {α : Type*} (p : α → Bool)
    (l r : List α) (hl : l.rtakeWhile p = []) (hr : ∀ x ∈ r, p x) :
    (l ++ r).rtakeWhile p = r := by
  induction r using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using hl
  | append_singleton r x ih =>
    rw [← List.append_assoc, List.rtakeWhile_concat_pos]
    · rw [ih]
      intro y hy
      exact hr y (List.mem_append_left [x] hy)
    · exact hr x (by simp)

/-- The semantic rightmost-parent split determines the executable `parentBlock` exactly. -/
theorem parentBlock_eq_of_deep_split (a : ℕ) (p u : List ℕ)
    (hdeep : ∀ k ∈ u, a + 2 ≤ k) :
    parentBlock (p ++ (a + 1) :: u) (a + 2) = (a + 1) :: u := by
  have htake : (p ++ (a + 1) :: u).rtakeWhile (a + 2 ≤ ·) = u := by
    rw [show p ++ (a + 1) :: u = (p ++ [a + 1]) ++ u by simp]
    apply rtakeWhile_append_eq_right_of_nil
    · exact List.rtakeWhile_concat_neg (p := fun x ↦ decide (a + 2 ≤ x))
        (l := p) (a + 1) (by simp)
    · intro k hk
      simpa only [decide_eq_true_eq] using hdeep k hk
  simp [parentBlock, htake]

/-- Closed form of a deep executable chop at its rightmost-parent split. -/
theorem chop_eq_of_deep_split (n a : ℕ) (p u : List ℕ)
    (hdeep : ∀ k ∈ u, a + 2 ≤ k) :
    chop n ((p ++ (a + 1) :: u) ++ [a + 2]) =
      (p ++ (a + 1) :: u) ++
        (List.replicate n ((a + 1) :: u)).flatten := by
  rw [chop]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_concat]
  rw [if_neg (by omega), parentBlock_eq_of_deep_split a p u hdeep]

/-- The complete finite nonblank tape segment at the start of a chop. -/
def tapeCells (b : ℕ) (t : List ℕ) : List Sy :=
  List.replicate b .b ++ [.lb, .rb] ++ treeCells t

/-- Configuration entering `CHOP_START`.  `j` explicit blanks represent an arbitrary finite
portion of the infinite blank tail. -/
def chopConfig (b : ℕ) (t : List ℕ) (j : ℕ) : Cfg St Sy :=
  let tape := tapeCells b t
  ⟨.core .CHOP_START, tape.dropLast.reverse, tape.getLastD .blank,
    List.replicate j .blank⟩

/-- Chop configuration retaining the one-bit far-left blank invariant exposed by consecutive
deep chops. -/
def chopConfigPadded (padded : Bool) (b : ℕ) (t : List ℕ) (j : ℕ) : Cfg St Sy :=
  let tape := tapeCells b t
  ⟨.core .CHOP_START, tape.dropLast.reverse ++ basePad padded,
    tape.getLastD .blank, List.replicate j .blank⟩

@[simp] theorem chopConfigPadded_false (b : ℕ) (t : List ℕ) (j : ℕ) :
    chopConfigPadded false b t j = chopConfig b t j := by
  simp [chopConfigPadded, chopConfig, basePad]

private theorem turnOnBlank_eq_paddedChop (tape : List Sy) (j : ℕ) (hne : tape ≠ []) :
    (⟨St.core .CHOP_START, (tape.reverse ++ [Sy.blank]).tail,
      (tape.reverse ++ [Sy.blank]).headD Sy.blank,
      List.replicate j Sy.blank⟩ : Cfg St Sy) =
    ⟨St.core .CHOP_START, tape.dropLast.reverse ++ [Sy.blank],
      tape.getLastD Sy.blank, List.replicate j Sy.blank⟩ := by
  induction tape using List.reverseRecOn with
  | nil => contradiction
  | append_singleton pre x _ => simp

private theorem turnOnBlank_eq_chop (tape : List Sy) (j : ℕ) (hne : tape ≠ []) :
    (⟨St.core .CHOP_START, tape.reverse.tail, tape.reverse.headD Sy.blank,
      List.replicate j Sy.blank⟩ : Cfg St Sy) =
    ⟨St.core .CHOP_START, tape.dropLast.reverse,
      tape.getLastD Sy.blank, List.replicate j Sy.blank⟩ := by
  induction tape using List.reverseRecOn with
  | nil => contradiction
  | append_singleton pre x _ => simp

/-- One complete deep machine chop.  The unary base is unchanged, the work region becomes the
executable hydra `chop`, and the far-left padding normalizes to one represented blank. -/
theorem deepChop_reaches (cells : List Sy) (padded : Bool) (n a : ℕ)
    (s : List ℕ) (j : ℕ) (hn : 1 ≤ n) (ht : WF (s ++ [a + 2])) :
    ∃ j', 1 ≤ j' ∧ Reaches (machine cells)
      (chopConfigPadded padded (n + 1) (s ++ [a + 2]) (j + 1))
      (chopConfigPadded true (n + 1) (chop n (s ++ [a + 2])) j') := by
  let baseLeft : List Sy :=
    .rb :: .lb :: (List.replicate (n + 1) .b ++ basePad padded)
  have hinput :
      chopConfigPadded padded (n + 1) (s ++ [a + 2]) (j + 1) =
        ⟨.core .CHOP_START,
          List.replicate (a + 1) .d ++ .P :: (treeCells s).reverse ++ baseLeft,
          .d, .blank :: List.replicate j .blank⟩ := by
    let preTape : List Sy :=
      (List.replicate (n + 1) Sy.b ++ [Sy.lb, Sy.rb] ++ treeCells s ++
        (Sy.P :: List.replicate (a + 1) Sy.d))
    have htape : tapeCells (n + 1) (s ++ [a + 2]) = preTape ++ [.d] := by
      simp [tapeCells, preTape, treeCells_append, treeCells_cons, List.replicate_succ',
        List.append_assoc]
    have hlast : (preTape ++ [Sy.d]).getLastD .blank = .d := by simp
    change (⟨.core .CHOP_START,
      (tapeCells (n + 1) (s ++ [a + 2])).dropLast.reverse ++ basePad padded,
      (tapeCells (n + 1) (s ++ [a + 2])).getLastD .blank,
      List.replicate (j + 1) .blank⟩ : Cfg St Sy) = _
    rw [htape, List.dropLast_concat]
    rw [hlast]
    simp [preTape, baseLeft, List.reverse_append, List.reverse_replicate,
      List.replicate_succ, replicate_append_cons_self, List.append_assoc]
  obtain ⟨p, u, hsplit, hdeep, hsearch⟩ :=
    chopStart_reaches_repStart_of_wf_deep cells a s baseLeft
      (List.replicate j .blank) ht
  let front : List Sy := .rb :: treeCells p
  let body : List Sy := markedCopyBody a u
  let out : List Sy := (List.replicate n (copiedBlock body)).flatten
  have hfrontLb : ∀ x ∈ front, x ≠ Sy.lb := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide
    · rcases mem_treeCells hx with rfl | rfl <;> decide
  have hfrontS : ∀ x ∈ front, x ≠ Sy.S := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide
    · rcases mem_treeCells hx with rfl | rfl <;> decide
  have hbody : ∀ x ∈ body, x = Sy.P ∨ x = Sy.d := by
    intro x hx
    exact mem_markedCopyBody hx
  obtain ⟨jCopy, hrep⟩ := repStart_reaches_repScanDonePadded cells padded n
    front body (a + 4 + j) hfrontLb hfrontS hbody
  have hrep' :
      Reaches (machine cells)
        ⟨.core .REP_START, (treeCells p).reverse ++ baseLeft, .S,
          markedCopyTail a u ++ List.replicate (a + 4) .blank ++
            List.replicate j .blank⟩
        (repScanConfig 0 (n + 1) front body out jCopy) := by
    simpa [front, body, out, baseLeft, markedCopyTail_eq, List.replicate_add,
      List.reverse_append, List.append_assoc] using hrep
  have hbodyZ : ∀ x ∈ body, x ≠ Sy.z := by
    intro x hx
    rcases hbody x hx with rfl | rfl <;> decide
  have hrestore := repScanDone_reaches_goChop cells (n + 1)
    front body out jCopy hfrontS hbodyZ
  let left : List Sy :=
    .d :: body.reverse ++ .P :: front.reverse ++ .lb ::
      List.replicate (n + 1) .b ++ [.blank]
  have houtNe : out ≠ [] := by
    cases n with
    | zero => omega
    | succ n => simp [out, copiedBlock]
  have houtBlank : ∀ x ∈ out, x ≠ Sy.blank := by
    intro x hx
    have hx' := mem_flatten_replicate_copiedBlock hbody hx
    rcases hx' with rfl | rfl <;> decide
  have hhead : (out ++ List.replicate jCopy Sy.blank).headD .blank =
      out.headD .blank := by
    exact headD_append_of_ne_nil out (List.replicate jCopy .blank) houtNe
  have htail : (out ++ List.replicate jCopy Sy.blank).tail =
      out.tail ++ List.replicate jCopy .blank :=
    tail_append_of_ne_nil out (List.replicate jCopy .blank) houtNe
  have hrestore' :
      Reaches (machine cells)
        (repScanConfig 0 (n + 1) front body out jCopy)
        ⟨.core .GO_CHOP, left, out.headD .blank,
          out.tail ++ List.replicate jCopy .blank⟩ := by
    rw [hhead, htail] at hrestore
    simpa [left] using hrestore
  obtain ⟨j', hj', hgo⟩ :=
    goChop_reaches_chopStart cells left out jCopy houtNe houtBlank
  have hpositive : ∀ k ∈ u, 1 ≤ k := by
    intro k hk
    have := hdeep k hk
    omega
  have hblock : copiedBlock body = treeCells ((a + 1) :: u) := by
    simpa [body] using copiedBlock_markedCopyBody a u hpositive
  have houtEq : out = treeCells (List.replicate n ((a + 1) :: u)).flatten := by
    dsimp [out]
    rw [hblock]
    exact (treeCells_flatten_replicate n ((a + 1) :: u)).symm
  have hchop := chop_eq_of_deep_split n a p u hdeep
  have hwork : treeCells (chop n (s ++ [a + 2])) =
      treeCells p ++ copiedBlock body ++ out := by
    rw [hsplit, hchop]
    simp only [treeCells_append]
    rw [hblock, houtEq]
  have hrev : out.reverse ++ left =
      (tapeCells (n + 1) (chop n (s ++ [a + 2]))).reverse ++ [.blank] := by
    simp [left, front, copiedBlock, tapeCells, hwork, List.reverse_append,
      List.reverse_replicate, List.append_assoc]
  have htapeNe : tapeCells (n + 1) (chop n (s ++ [a + 2])) ≠ [] := by
    simp [tapeCells]
  have htarget :
      ⟨.core .CHOP_START, (out.reverse ++ left).tail,
        (out.reverse ++ left).headD .blank, List.replicate j' .blank⟩ =
      chopConfigPadded true (n + 1) (chop n (s ++ [a + 2])) j' := by
    rw [hrev, turnOnBlank_eq_paddedChop _ _ htapeNe]
    rfl
  refine ⟨j', hj', ?_⟩
  rw [hinput]
  have hall := reaches_trans hsearch
    (reaches_trans hrep' (reaches_trans hrestore' hgo))
  exact htarget ▸ hall

/-- A depth-one chop on a non-singleton tree erases the final node, bumps the unary base, and
returns to an unpadded chop configuration for the surviving prefix. -/
theorem shallowChop_reaches (cells : List Sy) (padded : Bool) (b : ℕ)
    (s : List ℕ) (j : ℕ) (hs : s ≠ []) (ht : WF (s ++ [1])) :
    ∃ j', 1 ≤ j' ∧ Reaches (machine cells)
      (chopConfigPadded padded b (s ++ [1]) (j + 1))
      (chopConfigPadded false (b + 1) s j') := by
  have hpositive : ∀ k ∈ s, 1 ≤ k := by
    intro k hk
    exact wf_mem_lower ht (by simp [hk])
  obtain ⟨treePre, htree⟩ := exists_treeCells_append_d hs hpositive
  let preTape : List Sy :=
    List.replicate b .b ++ [.lb, .rb] ++ treePre
  have htapeS : tapeCells b s = preTape ++ [.d] := by
    simp [tapeCells, preTape, htree, List.append_assoc]
  have hinput :
      chopConfigPadded padded b (s ++ [1]) (j + 1) =
        ⟨.core .CHOP_START, .P :: .d :: preTape.reverse ++ basePad padded,
          .d, .blank :: List.replicate j .blank⟩ := by
    have hfull : tapeCells b (s ++ [1]) = (preTape ++ [.d, .P]) ++ [.d] := by
      calc
        tapeCells b (s ++ [1]) = tapeCells b s ++ [.P, .d] := by
          simp [tapeCells, treeCells_append, treeCells_cons, List.append_assoc]
        _ = (preTape ++ [.d, .P]) ++ [.d] := by
          rw [htapeS]
          simp [List.append_assoc]
    change (⟨.core .CHOP_START,
      (tapeCells b (s ++ [1])).dropLast.reverse ++ basePad padded,
      (tapeCells b (s ++ [1])).getLastD .blank,
      List.replicate (j + 1) .blank⟩ : Cfg St Sy) = _
    rw [hfull, List.dropLast_concat]
    simp [List.reverse_append, List.replicate_succ, List.append_assoc]
  let blanks := List.replicate (j + 3) Sy.blank
  have hfive :
      Reaches (machine cells)
        ⟨.core .CHOP_START, .P :: .d :: preTape.reverse ++ basePad padded,
          .d, .blank :: List.replicate j .blank⟩
        ⟨.core .GSTEP_BUMP, (preTape.reverse ++ basePad padded).tail,
          (preTape.reverse ++ basePad padded).headD .blank, .d :: blanks⟩ := by
    refine ⟨5, ?_⟩
    cases padded <;> rfl
  have hpreNe : preTape ≠ [] := by simp [preTape]
  have hpreSafe : ∀ x ∈ preTape, x ≠ Sy.blank := by
    intro x hx
    have hx' : x ∈ List.replicate b Sy.b ∨ x = .lb ∨ x = .rb ∨ x ∈ treePre := by
      simpa [preTape] using hx
    rcases hx' with hx' | rfl | rfl | hx'
    · have : x = Sy.b := (List.mem_replicate.mp hx').2
      subst x
      decide
    · decide
    · decide
    · have hxTree : x ∈ treeCells s := by rw [htree]; simp [hx']
      rcases mem_treeCells hxTree with rfl | rfl <;> decide
  have hscanRaw := stepN_scanLeftReverse (machine cells) (.core .GSTEP_BUMP)
    preTape (basePad padded) (.d :: blanks) hpreNe (by
      intro x hx
      have hne := hpreSafe x hx
      cases x <;> try rfl
      exact (hne rfl).elim)
  have hscan :
      Reaches (machine cells)
        ⟨.core .GSTEP_BUMP, (preTape.reverse ++ basePad padded).tail,
          (preTape.reverse ++ basePad padded).headD .blank, .d :: blanks⟩
        ⟨.core .GSTEP_BUMP, [], .blank, tapeCells b s ++ blanks⟩ := by
    apply reaches_of_stepN
    have hrevNe : preTape.reverse ≠ [] := by simpa using hpreNe
    cases padded <;>
      simpa [basePad, htapeS, show (default : Sy) = Sy.blank from rfl,
        tail_append_of_ne_nil preTape.reverse _ hrevNe,
        headD_append_of_ne_nil preTape.reverse _ hrevNe,
        List.append_assoc] using hscanRaw
  let oldTape := tapeCells b s
  have holdNe : oldTape ≠ [] := by simp [oldTape, tapeCells]
  have holdSafe : ∀ x ∈ oldTape, x ≠ Sy.blank := by
    intro x hx
    have hx' : x ∈ List.replicate b Sy.b ∨ x = .lb ∨ x = .rb ∨ x ∈ treeCells s := by
      simpa [oldTape, tapeCells] using hx
    rcases hx' with hx' | rfl | rfl | hx'
    · have : x = Sy.b := (List.mem_replicate.mp hx').2
      subst x
      decide
    · decide
    · decide
    · rcases mem_treeCells hx' with rfl | rfl <;> decide
  have holdHead : (oldTape ++ blanks).headD Sy.blank = oldTape.headD .blank :=
    headD_append_of_ne_nil oldTape blanks holdNe
  have holdTail : (oldTape ++ blanks).tail = oldTape.tail ++ blanks :=
    tail_append_of_ne_nil oldTape blanks holdNe
  have hbump :
      Reaches (machine cells)
        ⟨.core .GSTEP_BUMP, [], .blank, tapeCells b s ++ blanks⟩
        ⟨.core .GO_CHOP, [.b], oldTape.headD .blank, oldTape.tail ++ blanks⟩ := by
    have hraw : Reaches (machine cells)
        ⟨.core .GSTEP_BUMP, [], .blank, oldTape ++ blanks⟩
        ⟨.core .GO_CHOP, [.b],
          (oldTape ++ blanks).headD .blank, (oldTape ++ blanks).tail⟩ := ⟨1, rfl⟩
    rw [holdHead, holdTail] at hraw
    simpa [oldTape] using hraw
  obtain ⟨j', hj', hgo⟩ := goChop_reaches_chopStart cells [.b] oldTape
    (j + 3) holdNe holdSafe
  have hnewTape : tapeCells (b + 1) s = Sy.b :: oldTape := by
    simp [oldTape, tapeCells, List.replicate_succ, List.append_assoc]
  have hrev : oldTape.reverse ++ [Sy.b] = (tapeCells (b + 1) s).reverse := by
    rw [hnewTape]
    simp
  have htapeNe : tapeCells (b + 1) s ≠ [] := by simp [tapeCells]
  have htarget :
      ⟨.core .CHOP_START, (oldTape.reverse ++ [Sy.b]).tail,
        (oldTape.reverse ++ [Sy.b]).headD .blank, List.replicate j' .blank⟩ =
      chopConfigPadded false (b + 1) s j' := by
    rw [hrev, turnOnBlank_eq_chop _ _ htapeNe]
    simp [chopConfigPadded, basePad]
  refine ⟨j', hj', ?_⟩
  rw [hinput]
  have hall := reaches_trans hfive (reaches_trans hscan (reaches_trans hbump hgo))
  exact htarget ▸ hall

/-- Deleting the sole depth-one node reaches the intended undefined `STEP_DONE_CHECK2/rb`
transition. -/
theorem singletonChop_halts (cells : List Sy) (padded : Bool) (b j : ℕ) :
    Halts (machine cells) (chopConfigPadded padded b [1] (j + 1)) := by
  let final : Cfg St Sy :=
    ⟨.core .STEP_DONE_CHECK2,
      .lb :: List.replicate b .b ++ basePad padded,
      .rb, List.replicate (j + 3) .blank⟩
  have hinput : chopConfigPadded padded b [1] (j + 1) =
      ⟨.core .CHOP_START,
        .P :: .rb :: .lb :: List.replicate b .b ++ basePad padded,
        .d, .blank :: List.replicate j .blank⟩ := by
    simp [chopConfigPadded, tapeCells, treeCells, List.reverse_append,
      List.reverse_replicate, List.replicate_succ, List.append_assoc]
  refine ⟨4, final, ?_, ?_⟩
  · rw [hinput]
    cases padded <;> rfl
  · rfl

/-- The initializer has written any proper prefix while scanning the next implicit blank. -/
theorem init_write_prefix (cells pref : List Sy)
    (hprefix : ∃ suffix, suffix ≠ [] ∧ cells = pref ++ suffix) :
    stepN (machine cells) pref.length start =
      some ⟨.init pref.length, pref.reverse, .blank, []⟩ := by
  induction pref using List.reverseRecOn with
  | nil => rfl
  | append_singleton pre x ih =>
      obtain ⟨suffix, hsuffix, hcells⟩ := hprefix
      have hpre : ∃ suffix', suffix' ≠ [] ∧ cells = pre ++ suffix' := by
        refine ⟨x :: suffix, by simp, ?_⟩
        simpa [List.append_assoc] using hcells
      have hi := ih hpre
      have hget : cells.getD pre.length Sy.blank = x := by
        rw [hcells]
        simp [List.append_assoc]
      have hlt : pre.length + 1 < cells.length := by
        have hslen : 0 < suffix.length := by
          cases suffix with
          | nil => contradiction
          | cons y ys => simp
        rw [hcells]
        simp only [List.length_append, List.length_singleton]
        omega
      have htrans : machine cells (.init pre.length) .blank =
          some (x, .R, .init (pre.length + 1)) := by
        simp only [machine]
        rw [if_pos hlt, hget]
      rw [List.length_append, List.length_singleton, stepN_add, hi]
      simp [stepN, step, Cfg.move, htrans, List.reverse_append,
        show (default : Sy) = Sy.blank from rfl]

/-- After initialization, `GSTEP_BUMP` has scanned the written tape back to the blank immediately
left of it. -/
theorem init_reaches_bumpBlank (cells : List Sy) (hlen : 2 ≤ cells.length)
    (hsafe : ∀ x ∈ cells, x ≠ .blank) :
    Reaches (machine cells) start ⟨.core .GSTEP_BUMP, [], .blank, cells⟩ := by
  have hne : cells ≠ [] := by
    intro h
    simp [h] at hlen
  let pre := cells.dropLast
  let last := cells.getLast hne
  have hsplit : pre ++ [last] = cells := by
    exact List.dropLast_append_getLast hne
  have hpreNe : pre ≠ [] := by
    intro hp
    have hlenPre : pre.length = cells.length - 1 := by simp [pre]
    rw [hp] at hlenPre
    simp at hlenPre
    omega
  have hwrite := init_write_prefix cells pre ⟨[last], by simp, hsplit.symm⟩
  have hget : cells.getD pre.length Sy.blank = last := by
    rw [← hsplit]
    simp
  have hnot : ¬ (pre.length + 1 < cells.length) := by
    have hlenPre : pre.length = cells.length - 1 := by simp [pre]
    omega
  have htrans : machine cells (.init pre.length) .blank =
      some (last, .L, .core .GSTEP_BUMP) := by
    simp only [machine]
    rw [if_neg hnot, hget]
  have hlast :
      Reaches (machine cells)
        ⟨.init pre.length, pre.reverse, .blank, []⟩
        ⟨.core .GSTEP_BUMP, pre.reverse.tail,
          pre.reverse.headD .blank, [last]⟩ := by
    refine ⟨1, ?_⟩
    simp [stepN, step, Cfg.move, htrans,
      show (default : Sy) = Sy.blank from rfl]
  have hpreSafe : ∀ x ∈ pre, x ≠ Sy.blank := by
    intro x hx
    apply hsafe x
    rw [← hsplit]
    simp [hx]
  have hscan := stepN_scanLeftReverse (machine cells) (.core .GSTEP_BUMP)
    pre [] [last] hpreNe (by
      intro x hx
      have hneBlank := hpreSafe x hx
      cases x <;> try rfl
      exact (hneBlank rfl).elim)
  have hscan' :
      Reaches (machine cells)
        ⟨.core .GSTEP_BUMP, pre.reverse.tail,
          pre.reverse.headD .blank, [last]⟩
        ⟨.core .GSTEP_BUMP, [], .blank, cells⟩ := by
    apply reaches_of_stepN
    simpa [hsplit, show (default : Sy) = Sy.blank from rfl] using hscan
  exact reaches_trans (reaches_of_stepN hwrite) (reaches_trans hlast hscan')

theorem cellsOf_eq_tapeCells_two (t : List ℕ) : cellsOf t = tapeCells 2 t := by
  simp [cellsOf, tapeCells, treeCells]

/-- Initialization writes the seed, creates the third base counter, and enters the first chop. -/
theorem initial_reaches_chop (t : List ℕ) :
    ∃ j, 1 ≤ j ∧ Reaches (machine (cellsOf t)) start
      (chopConfigPadded false 3 t j) := by
  let cells := cellsOf t
  have hlen : 2 ≤ cells.length := by simp [cells, cellsOf]
  have hsafe : ∀ x ∈ cells, x ≠ Sy.blank := by
    intro x hx
    have hx' : x = Sy.b ∨ x = .lb ∨ x = .rb ∨ x ∈ treeCells t := by
      simpa [cells, cellsOf, treeCells] using hx
    rcases hx' with rfl | rfl | rfl | hx'
    · decide
    · decide
    · decide
    · rcases mem_treeCells hx' with rfl | rfl <;> decide
  have hinit := init_reaches_bumpBlank cells hlen hsafe
  have hcellsNe : cells ≠ [] := by simp [cells, cellsOf]
  have hbump :
      Reaches (machine cells)
        ⟨.core .GSTEP_BUMP, [], .blank, cells⟩
        ⟨.core .GO_CHOP, [.b], cells.headD .blank, cells.tail⟩ := ⟨1, by rfl⟩
  obtain ⟨j, hj, hgo⟩ :=
    goChop_reaches_chopStart cells [.b] cells 0 hcellsNe hsafe
  have hgo' :
      Reaches (machine cells)
        ⟨.core .GO_CHOP, [.b], cells.headD .blank, cells.tail⟩
        ⟨.core .CHOP_START, (cells.reverse ++ [Sy.b]).tail,
          (cells.reverse ++ [Sy.b]).headD .blank, List.replicate j .blank⟩ := by
    simpa using hgo
  have hnewTape : tapeCells 3 t = Sy.b :: cells := by
    simp [cells, cellsOf_eq_tapeCells_two, tapeCells, List.replicate_succ,
      List.append_assoc]
  have hrev : cells.reverse ++ [Sy.b] = (tapeCells 3 t).reverse := by
    rw [hnewTape]
    simp
  have htapeNe : tapeCells 3 t ≠ [] := by simp [tapeCells]
  have htarget :
      ⟨.core .CHOP_START, (cells.reverse ++ [Sy.b]).tail,
        (cells.reverse ++ [Sy.b]).headD .blank, List.replicate j .blank⟩ =
      chopConfigPadded false 3 t j := by
    rw [hrev, turnOnBlank_eq_chop _ _ htapeNe]
    simp [chopConfigPadded, basePad]
  refine ⟨j, hj, ?_⟩
  have hall := reaches_trans hinit (reaches_trans hbump hgo')
  exact htarget ▸ (by simpa [cells] using hall)

/-- Mathematical state after `k` machine-level hydra chops.  A depth-one chop increments the
base; every chop uses the current `base - 1` copy count. -/
def goodsteinBattle (b : ℕ) (t : List ℕ) : ℕ → ℕ × List ℕ
  | 0 => (b, t)
  | k + 1 =>
      let current := goodsteinBattle b t k
      let nextTree := chop (current.1 - 1) current.2
      if current.2.getLast? = some 1 then (current.1 + 1, nextTree)
      else (current.1, nextTree)

def goodsteinTurn (b : ℕ) (t : List ℕ) (k : ℕ) : ℕ :=
  (goodsteinBattle b t k).1 - 1

theorem goodsteinBattle_tree (b : ℕ) (t : List ℕ) : ∀ k,
    (goodsteinBattle b t k).2 = chopBattle (goodsteinTurn b t) t k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [goodsteinBattle, chopBattle, goodsteinTurn]
      rw [ih]
      split <;> rfl

theorem goodsteinBattle_base_ge {b : ℕ} {t : List ℕ} (hb : 2 ≤ b) : ∀ k,
    2 ≤ (goodsteinBattle b t k).1 := by
  intro k
  induction k with
  | zero => simpa [goodsteinBattle] using hb
  | succ k ih =>
      simp only [goodsteinBattle]
      split <;> simp <;> omega

theorem goodsteinBattle_wf {b : ℕ} {t : List ℕ} (ht : WF t) : ∀ k,
    WF (goodsteinBattle b t k).2 := by
  intro k
  induction k with
  | zero => simpa [goodsteinBattle] using ht
  | succ k ih =>
      simp only [goodsteinBattle]
      split <;> simp only [Prod.snd]
      all_goals exact chop_preserves_wf _ _ ih

theorem goodsteinBattle_terminates (b : ℕ) (t : List ℕ) (ht : WF t) :
    ∃ N, (goodsteinBattle b t N).2 = [] := by
  obtain ⟨N, hN⟩ := chopBattle_terminates (goodsteinTurn b t) t ht
  refine ⟨N, ?_⟩
  rw [goodsteinBattle_tree]
  exact hN

theorem halts_of_reaches {M : St → Sy → Option (Sy × Dir × St)} {c c' : Cfg St Sy}
    (hr : Reaches M c c') (hh : Halts M c') : Halts M c := by
  obtain ⟨m, hm⟩ := hr
  obtain ⟨n, final, hn, hhalt⟩ := hh
  refine ⟨m + n, final, ?_, hhalt⟩
  rw [stepN_add, hm]
  exact hn

theorem emptyChop_halts (cells : List Sy) (padded : Bool) (b j : ℕ) :
    Halts (machine cells) (chopConfigPadded padded b [] j) := by
  let c := chopConfigPadded padded b [] j
  refine ⟨0, c, rfl, ?_⟩
  change machine cells (.core .CHOP_START) ((tapeCells b []).getLastD .blank) = none
  have hhead : (tapeCells b []).getLastD Sy.blank = .rb := by simp [tapeCells]
  rw [hhead]
  rfl

/-- After any finite number of mathematical battle steps, the machine has either halted already
or reaches the corresponding chop configuration. -/
theorem reaches_goodsteinBattle_or_halts (cells : List Sy) (b : ℕ) (t : List ℕ)
    (padded : Bool) (j : ℕ) (hb : 2 ≤ b) (ht : WF t) (hj : 1 ≤ j) : ∀ N,
    Halts (machine cells) (chopConfigPadded padded b t j) ∨
      ∃ padded' j', 1 ≤ j' ∧
        Reaches (machine cells) (chopConfigPadded padded b t j)
          (chopConfigPadded padded' (goodsteinBattle b t N).1
            (goodsteinBattle b t N).2 j') := by
  intro N
  induction N with
  | zero =>
      right
      refine ⟨padded, j, hj, ?_⟩
      simpa [goodsteinBattle] using
        (reaches_refl (machine cells) (chopConfigPadded padded b t j))
  | succ N ih =>
      rcases ih with hhalt | ⟨currentPad, currentJ, hcurrentJ, hreach⟩
      · exact .inl hhalt
      · cases hcurrent : goodsteinBattle b t N with
        | mk currentBase currentTree =>
          have hreach' :
              Reaches (machine cells) (chopConfigPadded padded b t j)
                (chopConfigPadded currentPad currentBase currentTree currentJ) := by
            simpa [hcurrent] using hreach
          have hbase : 2 ≤ currentBase := by
            have := goodsteinBattle_base_ge (b := b) (t := t) hb N
            simpa [hcurrent] using this
          have htree : WF currentTree := by
            have := goodsteinBattle_wf (b := b) (t := t) ht N
            simpa [hcurrent] using this
          by_cases htreeNil : currentTree = []
          · exact .inl (halts_of_reaches hreach'
              (by simpa [htreeNil] using emptyChop_halts cells currentPad currentBase currentJ))
          · obtain ⟨s, k, hsplit⟩ : ∃ s k, currentTree = s ++ [k] := by
              exact ⟨currentTree.dropLast, currentTree.getLast htreeNil,
                (List.dropLast_append_getLast htreeNil).symm⟩
            subst currentTree
            have hshape : WF (s ++ [k]) := htree
            have hkPos : 1 ≤ k := by
              apply wf_mem_lower htree
              simp
            obtain ⟨q, rfl⟩ : ∃ q, currentJ = q + 1 :=
              ⟨currentJ - 1, by omega⟩
            by_cases hk : k = 1
            · subst k
              by_cases hs : s = []
              · subst s
                have hsingle := singletonChop_halts cells currentPad currentBase q
                exact .inl (halts_of_reaches hreach' hsingle)
              · obtain ⟨jNext, hjNext, hstep⟩ :=
                  shallowChop_reaches cells currentPad currentBase s q hs hshape
                have hnext : goodsteinBattle b t (N + 1) = (currentBase + 1, s) := by
                  simp [goodsteinBattle, hcurrent, chop_append_one]
                refine .inr ⟨false, jNext, hjNext, ?_⟩
                simpa [hnext] using reaches_trans hreach' hstep
            · have hkTwo : 2 ≤ k := by omega
              obtain ⟨a, rfl⟩ : ∃ a, k = a + 2 := ⟨k - 2, by omega⟩
              obtain ⟨n, rfl⟩ : ∃ n, currentBase = n + 1 :=
                ⟨currentBase - 1, by omega⟩
              have hn : 1 ≤ n := by omega
              obtain ⟨jNext, hjNext, hstep⟩ :=
                deepChop_reaches cells currentPad n a s q hn hshape
              have hnext : goodsteinBattle b t (N + 1) =
                  (n + 1, chop n (s ++ [a + 2])) := by
                simp [goodsteinBattle, hcurrent]
              refine .inr ⟨true, jNext, hjNext, ?_⟩
              simpa [hnext] using reaches_trans hreach' hstep

/-- Every well-formed chop configuration halts: mathematical hydra termination supplies a finite
number of chops, and `reaches_goodsteinBattle_or_halts` realizes that battle on the machine. -/
theorem halts_from_chop (cells : List Sy) (b : ℕ) (t : List ℕ) (padded : Bool) (j : ℕ)
    (hb : 2 ≤ b) (ht : WF t) (hj : 1 ≤ j) :
    Halts (machine cells) (chopConfigPadded padded b t j) := by
  obtain ⟨N, hN⟩ := goodsteinBattle_terminates b t ht
  rcases reaches_goodsteinBattle_or_halts cells b t padded j hb ht hj N with
    hhalt | ⟨finalPad, finalJ, _hfinalJ, hreach⟩
  · exact hhalt
  · apply halts_of_reaches hreach
    simpa [hN] using
      (emptyChop_halts cells finalPad (goodsteinBattle b t N).1 finalJ)

/-- Simulation theorem used by the public headline: initialization reaches the first chop, after
which the well-founded mathematical battle forces the machine to halt. -/
theorem halts_of_wf_sim (t : List ℕ) (ht : WF t) :
    Halts (machine (cellsOf t)) start := by
  obtain ⟨j, hj, hinit⟩ := initial_reaches_chop t
  apply halts_of_reaches hinit
  exact halts_from_chop (cellsOf t) 3 t false j (by omega) ht hj

/-- The empty well-formed seed reaches the undefined `CHOP_START`/`]` entry after 13 steps. -/
theorem empty_halts : Halts (machine (cellsOf [])) start := by
  refine ⟨13, chopConfig 3 [] 1, ?_, ?_⟩ <;> decide +kernel

end GoodsteinTM
