/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.GoodsteinTM.Hydra
import Mathlib.Logic.Hydra
import Mathlib.Tactic.Abel

/-!
# The well-founded tree order behind Goodstein hydra chops

`Hydra.lean` describes the machine's move directly on preorder level sequences.  This file gives
the structural termination engine.  A `Tree` is a rose tree, and `TreeLt` is the recursive
multiset/path order obtained by removing one child and replacing it by finitely many strictly
smaller children.  Mathlib's `Relation.CutExpand` proves this order well-founded.

The level-sequence bridge is kept here rather than importing the analogous development from
`lean-gallery`: the Goodstein machine must connect its concrete ordered preorder encoding to the
abstract tree order.
-/

namespace GoodsteinTM

/-- A finite rooted tree.  The machine tape encodes a list of these below an implicit root. -/
inductive Tree : Type
  | node : List Tree → Tree

namespace Tree

/-- A leaf/head. -/
def leaf : Tree := node []

/-- The ordered children of a tree. -/
def children : Tree → List Tree
  | node cs => cs

@[simp] theorem children_node (cs : List Tree) : children (.node cs) = cs := rfl

/-- Structural induction for the nested rose tree. -/
@[induction_eliminator]
theorem ind' {P : Tree → Prop} (h : ∀ cs : List Tree, (∀ c ∈ cs, P c) → P (node cs)) :
    ∀ t, P t :=
  fun t ↦
    Tree.rec (motive_1 := P) (motive_2 := fun l ↦ ∀ c ∈ l, P c)
      (fun cs ih ↦ h cs ih)
      (fun c hc ↦ (List.not_mem_nil hc).elim)
      (fun _ _ ihc ihcs c hc ↦ by
        rcases List.mem_cons.1 hc with rfl | hc'
        · exact ihc
        · exact ihcs c hc')
      t

mutual
  /-- Preorder level sequence of one tree whose root lies at depth `d`. -/
  def levelsAt : Tree → ℕ → List ℕ
    | node children, d => d :: forestLevelsAt children (d + 1)
  termination_by t _ => sizeOf t

  /-- Preorder level sequence of a forest whose roots lie at depth `d`. -/
  def forestLevelsAt : List Tree → ℕ → List ℕ
    | [], _ => []
    | t :: rest, d => levelsAt t d ++ forestLevelsAt rest d
  termination_by ts _ => sizeOf ts
end

@[simp] theorem levelsAt_node (children : List Tree) (d : ℕ) :
    levelsAt (.node children) d = d :: forestLevelsAt children (d + 1) := by
  rw [levelsAt]

@[simp] theorem forestLevelsAt_nil (d : ℕ) : forestLevelsAt [] d = [] := by
  rw [forestLevelsAt]

@[simp] theorem forestLevelsAt_cons (t : Tree) (ts : List Tree) (d : ℕ) :
    forestLevelsAt (t :: ts) d = levelsAt t d ++ forestLevelsAt ts d := by
  rw [forestLevelsAt]

@[simp] theorem levelsAt_leaf (d : ℕ) : levelsAt leaf d = [d] := by
  simp [leaf]

theorem forestLevelsAt_append (xs ys : List Tree) (d : ℕ) :
    forestLevelsAt (xs ++ ys) d = forestLevelsAt xs d ++ forestLevelsAt ys d := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

theorem forestLevelsAt_replicate (n : ℕ) (t : Tree) (d : ℕ) :
    forestLevelsAt (List.replicate n t) d = (List.replicate n (levelsAt t d)).flatten := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

mutual
  /-- Every level in one encoded tree is at least the root level. -/
  theorem mem_levelsAt_lower : ∀ {t : Tree} {d x : ℕ}, x ∈ levelsAt t d → d ≤ x
    | .node children, d, x, hx => by
      simp only [levelsAt_node, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_rfl
      · exact (mem_forestLevelsAt_lower hx).trans' (Nat.le_succ d)
  termination_by t _ _ _ => sizeOf t

  /-- Every level in an encoded forest is at least the forest's root level. -/
  theorem mem_forestLevelsAt_lower :
      ∀ {ts : List Tree} {d x : ℕ}, x ∈ forestLevelsAt ts d → d ≤ x
    | [], _, _, hx => by simp at hx
    | t :: ts, d, x, hx => by
      simp only [forestLevelsAt_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact mem_levelsAt_lower hx
      · exact mem_forestLevelsAt_lower hx
  termination_by ts _ _ _ => sizeOf ts
end

/-- Every list whose roots are exactly at `d`, whose entries never lie above `d`, and whose
successive levels rise by at most one is the preorder encoding of a forest. -/
theorem exists_forestLevelsAt (t : List ℕ) (d : ℕ)
    (hlower : ∀ x ∈ t, d ≤ x)
    (hroot : t.head?.all (· = d))
    (hchain : t.IsChain fun a b => 1 ≤ b ∧ b ≤ a + 1) :
    ∃ cs, forestLevelsAt cs d = t := by
  induction hlen : t.length using Nat.strong_induction_on generalizing t d with
  | h len ih =>
    cases t with
    | nil => exact ⟨[], by simp⟩
    | cons x s =>
      have hx : x = d := by simpa using hroot
      subst x
      let u := s.takeWhile (d < ·)
      let v := s.dropWhile (d < ·)
      have hsplit : u ++ v = s := List.takeWhile_append_dropWhile
      have hlower_s : ∀ x ∈ s, d ≤ x := by
        intro x hx
        exact hlower x (by simp [hx])
      have hlower_u : ∀ x ∈ u, d + 1 ≤ x := by
        intro x hx
        have hp := List.mem_takeWhile_imp hx
        simpa [u] using hp
      have hlower_v : ∀ x ∈ v, d ≤ x := by
        intro x hx
        apply hlower_s x
        rw [← hsplit]
        simp [hx]
      have hchain_s : s.IsChain fun a b => 1 ≤ b ∧ b ≤ a + 1 := hchain.tail
      have hchain_uv : (u ++ v).IsChain fun a b => 1 ≤ b ∧ b ≤ a + 1 := by
        simpa only [hsplit] using hchain_s
      have hchain_u : u.IsChain fun a b => 1 ≤ b ∧ b ≤ a + 1 :=
        hchain_uv.left_of_append
      have hchain_v : v.IsChain fun a b => 1 ≤ b ∧ b ≤ a + 1 :=
        hchain_uv.right_of_append
      have hroot_u : u.head?.all (· = d + 1) := by
        cases hu : u with
        | nil => simp
        | cons y ys =>
          have hy_pred : d < y := by
            have hp := List.mem_takeWhile_imp (p := fun z => decide (d < z))
              (l := s) (x := y) (by simp [u, hu])
            simpa using hp
          have hs_eq : s = y :: (ys ++ v) := by
            rw [← hsplit, hu]
            rfl
          have hrel : 1 ≤ y ∧ y ≤ d + 1 := by
            rw [hs_eq] at hchain
            exact (List.isChain_cons_cons.mp hchain).1
          simp
          omega
      have hroot_v : v.head?.all (· = d) := by
        cases hv : v with
        | nil => simp
        | cons y ys =>
          have hy_s : y ∈ s := by
            rw [← hsplit, hv]
            simp
          have hy_lower := hlower_s y hy_s
          have hnot := List.dropWhile_get_zero_not (fun z => decide (d < z)) s
            (by simp [v, hv])
          simp [v, hv] at hnot
          have hy : y = d := by omega
          simp [hy]
      have hulen : u.length < len := by
        have hslen := congrArg List.length hsplit
        simp only [List.length_append] at hslen
        simp only [List.length_cons] at hlen
        omega
      have hvlen : v.length < len := by
        have hslen := congrArg List.length hsplit
        simp only [List.length_append] at hslen
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨cu, hcu⟩ := ih u.length hulen u (d + 1) hlower_u hroot_u hchain_u rfl
      obtain ⟨cv, hcv⟩ := ih v.length hvlen v d hlower_v hroot_v hchain_v rfl
      refine ⟨.node cu :: cv, ?_⟩
      simp only [forestLevelsAt_cons, levelsAt_node]
      rw [hcu, hcv]
      simpa only [List.cons_append] using congrArg (fun z => d :: z) hsplit

end Tree

/-- Every entry of a well-formed level sequence has positive depth. -/
theorem wf_mem_lower {t : List ℕ} (ht : WF t) {x : ℕ} (hx : x ∈ t) : 1 ≤ x := by
  suffices h : ∀ (l : List ℕ), l.head?.all (1 ≤ ·) →
      l.IsChain (fun a b => 1 ≤ b ∧ b ≤ a + 1) → ∀ x ∈ l, 1 ≤ x by
    apply h t
    · cases t with
      | nil => simp
      | cons a t =>
          have ha : a = 1 := by simpa using ht.1
          simp [ha]
    · exact ht.2
    · exact hx
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      intro hhead hchain x hx
      have ha : 1 ≤ a := by simpa using hhead
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · apply ih
        · cases l with
          | nil => simp
          | cons b l =>
              have hab := (List.isChain_cons_cons.mp hchain).1
              simpa using hab.1
        · exact hchain.tail
        · exact hx

/-- Every well-formed machine level sequence has a concrete rose-forest representation. -/
theorem exists_forestLevelsAt_of_wf {t : List ℕ} (ht : WF t) :
    ∃ cs, Tree.forestLevelsAt cs 1 = t := by
  exact Tree.exists_forestLevelsAt t 1 (fun _ hx ↦ wf_mem_lower ht hx) ht.1 ht.2

open Relation

private theorem rtakeWhile_append_eq_right {α : Type*} (p : α → Bool) (l r : List α)
    (hl : l.rtakeWhile p = []) (hr : ∀ x ∈ r, p x) : (l ++ r).rtakeWhile p = r := by
  induction r using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using hl
  | append_singleton r x ih =>
    rw [← List.append_assoc, List.rtakeWhile_concat_pos]
    · rw [ih]
      intro y hy
      exact hr y (List.mem_append_left [x] hy)
    · exact hr x (by simp)

/-- Recursive multiset/path order on rose trees. -/
inductive TreeLt : Tree → Tree → Prop
  | mk {s' s t : List Tree} {a : Tree} (ha : a ∈ s) (hr : ∀ a' ∈ t, TreeLt a' a)
      (he : (s' : Multiset Tree) + {a} = (s : Multiset Tree) + (t : Multiset Tree)) :
      TreeLt (.node s') (.node s)

theorem treeLt_irrefl : ∀ h : Tree, ¬ TreeLt h h := by
  intro h
  induction h with
  | _ s ih =>
    intro hh
    cases hh with
    | @mk s' s t a ha hr he =>
      have ht : ({a} : Multiset Tree) = (t : Multiset Tree) := add_left_cancel he
      have hat : a ∈ t := by
        have : a ∈ (t : Multiset Tree) := ht ▸ Multiset.mem_singleton_self a
        simpa using this
      exact ih a ha (hr a hat)

instance : Std.Irrefl TreeLt := ⟨treeLt_irrefl⟩

private theorem cutExpand_of_treeLt {s' s : List Tree} (h : TreeLt (.node s') (.node s)) :
    CutExpand TreeLt (↑s') (↑s) := by
  cases h with
  | @mk s'2 s2 t a ha hr he =>
    exact ⟨↑t, a, fun a' ha' ↦ hr a' (by simpa using ha'), by simpa using he⟩

private theorem acc_node {s : List Tree} (h : Acc (CutExpand TreeLt) (↑s)) :
    Acc TreeLt (.node s) := by
  suffices H : ∀ S : Multiset Tree, Acc (CutExpand TreeLt) S →
      ∀ s : List Tree, (↑s : Multiset Tree) = S → Acc TreeLt (.node s) by
    exact H _ h s rfl
  intro S hS
  induction hS with
  | intro S _ ih =>
    intro s hsS
    refine Acc.intro _ fun y hy ↦ ?_
    cases y with
    | node s' =>
      have hcut : CutExpand TreeLt (↑s') (↑s) := cutExpand_of_treeLt hy
      exact ih (↑s') (hsS ▸ hcut) s' rfl

/-- The recursive tree order is well-founded. -/
theorem treeLt_wf : WellFounded TreeLt := by
  refine ⟨fun h ↦ ?_⟩
  induction h with
  | _ s ih =>
    apply acc_node
    apply acc_of_singleton
    intro a ha
    exact (ih a (by simpa using ha)).cutExpand

/-- Removing a leaf from a node strictly lowers it. -/
theorem treeLt_eraseLeaf {p p' : List Tree} (hp : List.Perm p (Tree.leaf :: p')) :
    TreeLt (.node p') (.node p) := by
  have hp' : (p : Multiset Tree) = Tree.leaf ::ₘ (p' : Multiset Tree) := by
    rw [Multiset.cons_coe]
    exact Multiset.coe_eq_coe.2 hp
  refine TreeLt.mk (a := Tree.leaf) (t := []) ?_ ?_ ?_
  · exact (hp.mem_iff).2 (List.mem_cons_self ..)
  · intro a' ha'
    exact (List.not_mem_nil ha').elim
  · rw [hp']
    simp only [← Multiset.singleton_add, Multiset.coe_nil, add_zero]
    abel

/-- A regrowing chop below the implicit root.  In the `grand` case the chopped leaf's parent is
replaced by `n + 1` copies of its pruned form; `deep` routes the same operation down the tree. -/
inductive TreeChop (n : ℕ) : Tree → Tree → Prop
  | grand {gs gs' ps ps' : List Tree}
      (hg : List.Perm gs (.node ps :: gs')) (hp : List.Perm ps (Tree.leaf :: ps')) :
      TreeChop n (.node gs) (.node (gs' ++ List.replicate (n + 1) (.node ps')))
  | deep {cs cs' : List Tree} {c c' : Tree}
      (hc : List.Perm cs (c :: cs')) (hrec : TreeChop n c c') :
      TreeChop n (.node cs) (.node (c' :: cs'))

/-- One hydra move at the implicit root. -/
inductive TreeStep (n : ℕ) : Tree → Tree → Prop
  | root {cs rest : List Tree} (h : List.Perm cs (Tree.leaf :: rest)) :
      TreeStep n (.node cs) (.node rest)
  | chop {h h' : Tree} (hc : TreeChop n h h') : TreeStep n h h'

/-- Every structural regrowing chop strictly lowers the recursive tree order. -/
theorem treeChop_lt {n : ℕ} {h h' : Tree} (hc : TreeChop n h h') : TreeLt h' h := by
  induction hc with
  | @grand gs gs' ps ps' hg hp =>
    have hgs : (gs : Multiset Tree) = .node ps ::ₘ (gs' : Multiset Tree) := by
      rw [Multiset.cons_coe]
      exact Multiset.coe_eq_coe.2 hg
    refine TreeLt.mk (a := .node ps) (t := List.replicate (n + 1) (.node ps')) ?_ ?_ ?_
    · exact (hg.mem_iff).2 (List.mem_cons_self ..)
    · intro a' ha'
      rw [List.eq_of_mem_replicate ha']
      exact treeLt_eraseLeaf hp
    · rw [hgs]
      simp only [← Multiset.coe_add, ← Multiset.singleton_add]
      abel
  | @deep cs cs' c c' hc hrec ih =>
    have hcs : (cs : Multiset Tree) = c ::ₘ (cs' : Multiset Tree) := by
      rw [Multiset.cons_coe]
      exact Multiset.coe_eq_coe.2 hc
    refine TreeLt.mk (a := c) (t := [c']) ?_ ?_ ?_
    · exact (hc.mem_iff).2 (List.mem_cons_self ..)
    · intro a' ha'
      rw [List.mem_singleton.1 ha']
      exact ih
    · rw [hcs]
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add]
      abel

/-- Every structural hydra move strictly lowers the recursive tree order. -/
theorem treeStep_lt {n : ℕ} {h h' : Tree} (hs : TreeStep n h h') : TreeLt h' h := by
  cases hs with
  | root h => exact treeLt_eraseLeaf h
  | chop hc => exact treeChop_lt hc

/-! ## The deterministic rightmost move

The tape always cuts the final preorder node.  These two relations specialize the permutation-
invariant structural move above to the last child at every level.  Their append-shaped constructors
are the seam used by the concrete level-sequence bridge.
-/

/-- A chop of the rightmost leaf below the implicit root. -/
inductive RightChop (n : ℕ) : Tree → Tree → Prop
  | grand (gs ps : List Tree) :
      RightChop n (.node (gs ++ [.node (ps ++ [Tree.leaf])]))
        (.node (gs ++ List.replicate (n + 1) (.node ps)))
  | deep (gs : List Tree) {c c' : Tree} (h : RightChop n c c') :
      RightChop n (.node (gs ++ [c])) (.node (gs ++ [c']))

/-- The rightmost hydra step, including a leaf directly below the implicit root. -/
inductive RightStep (n : ℕ) : Tree → Tree → Prop
  | root (cs : List Tree) : RightStep n (.node (cs ++ [Tree.leaf])) (.node cs)
  | chop {h h' : Tree} (hc : RightChop n h h') : RightStep n h h'

/-- Every non-dead ordered tree has a next rightmost hydra step. -/
theorem rightStep_exists (n : ℕ) : ∀ h : Tree, h ≠ Tree.leaf → ∃ h', RightStep n h h' := by
  intro h
  induction h using Tree.ind' with
  | h cs ih =>
      intro hne
      induction cs using List.reverseRecOn with
      | nil => exact (hne rfl).elim
      | append_singleton gs c =>
        by_cases hc : c = Tree.leaf
        · subst c
          exact ⟨.node gs, RightStep.root gs⟩
        · obtain ⟨c', hs⟩ := ih c (by simp) hc
          cases hs with
          | root ps =>
              exact ⟨.node (gs ++ List.replicate (n + 1) (.node ps)),
                RightStep.chop (RightChop.grand gs ps)⟩
          | chop hchop =>
              exact ⟨.node (gs ++ [c']), RightStep.chop (RightChop.deep gs hchop)⟩

/-- Every ordered rightmost chop strictly lowers the tree order.  The proof uses the ordered
append decomposition directly; unlike `TreeChop`, it does not permute the untouched siblings. -/
theorem rightChop_lt {n : ℕ} {h h' : Tree} (hc : RightChop n h h') : TreeLt h' h := by
  induction hc with
  | grand gs ps =>
    exact treeChop_lt (TreeChop.grand (List.perm_append_singleton _ _)
      (List.perm_append_singleton _ _))
  | @deep gs c c' h ih =>
    refine TreeLt.mk (a := c) (t := [c']) ?_ ?_ ?_
    · simp
    · simpa using ih
    · simp only [← Multiset.coe_add]
      abel

/-- In particular, every ordered rightmost step strictly lowers the well-founded tree order. -/
theorem rightStep_lt {n : ℕ} {h h' : Tree} (hs : RightStep n h h') : TreeLt h' h :=
  by
    cases hs with
    | root cs => exact treeLt_eraseLeaf (List.perm_append_singleton _ _)
    | chop hc => exact rightChop_lt hc

/-- Every sequence of rightmost hydra moves reaches the dead tree. -/
theorem rightBattle_terminates {H : ℕ → Tree} {turn : ℕ → ℕ}
    (hstep : ∀ k, H k ≠ Tree.leaf → RightStep (turn k) (H k) (H (k + 1))) :
    ∃ N, H N = Tree.leaf := by
  by_contra hcon
  rw [not_exists] at hcon
  have hdec : ∀ k, TreeLt (H (k + 1)) (H k) := fun k ↦ rightStep_lt (hstep k (hcon k))
  obtain ⟨a, ⟨N, hNa⟩, hmin⟩ := treeLt_wf.has_min (Set.range H) ⟨H 0, 0, rfl⟩
  exact hmin (H (N + 1)) ⟨N + 1, rfl⟩ (hNa ▸ hdec N)

/-- The level-sequence `chop` agrees with the root case of the ordered tree move. -/
theorem chop_forestLevelsAt_root (n : ℕ) (cs : List Tree) :
    chop n (Tree.forestLevelsAt (cs ++ [Tree.leaf]) 1) = Tree.forestLevelsAt cs 1 := by
  rw [Tree.forestLevelsAt_append]
  simp

/-- The concrete chop is insensitive to an earlier prefix when the rightmost leaf and its parent
both lie in the encoded tree.  This is the depth-general form of the `RightChop.grand` case. -/
theorem chop_append_forestLevelsAt_grand (n d : ℕ) (hd : 1 ≤ d)
    (a : List ℕ) (gs ps : List Tree) :
    chop n (a ++ Tree.forestLevelsAt (gs ++ [.node (ps ++ [Tree.leaf])]) d) =
      a ++ Tree.forestLevelsAt (gs ++ List.replicate (n + 1) (.node ps)) d := by
  let g := Tree.forestLevelsAt gs d
  let f := Tree.forestLevelsAt ps (d + 1)
  have hbefore : a ++ Tree.forestLevelsAt (gs ++ [.node (ps ++ [Tree.leaf])]) d =
      (a ++ g ++ [d] ++ f) ++ [d + 1] := by
    simp only [Tree.forestLevelsAt_append, Tree.forestLevelsAt_cons, Tree.forestLevelsAt_nil,
      Tree.levelsAt_node, Tree.levelsAt_leaf, g, f]
    simp [List.append_assoc]
  have htake : (a ++ g ++ [d] ++ f).rtakeWhile (d + 1 ≤ ·) = f := by
    apply rtakeWhile_append_eq_right
    · exact List.rtakeWhile_concat_neg (p := fun x ↦ decide (d + 1 ≤ x))
        (l := a ++ g) d (by simp)
    · intro x hx
      simpa only [decide_eq_true_eq] using Tree.mem_forestLevelsAt_lower hx
  rw [hbefore, chop]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, List.dropLast_concat,
    if_neg (by omega : d + 1 ≠ 1), parentBlock, Nat.add_sub_cancel, htake]
  rw [Tree.forestLevelsAt_append, Tree.forestLevelsAt_replicate]
  simp only [Tree.levelsAt_node, List.replicate_succ, List.flatten_cons]
  simp [g, f, List.append_assoc]

/-- The level-sequence `chop` agrees with the first regrowing constructor of `RightChop`: a
rightmost depth-two leaf is deleted and its pruned parent is present in `n + 1` copies. -/
theorem chop_forestLevelsAt_grand (n : ℕ) (gs ps : List Tree) :
    chop n (Tree.forestLevelsAt (gs ++ [.node (ps ++ [Tree.leaf])]) 1) =
      Tree.forestLevelsAt (gs ++ List.replicate (n + 1) (.node ps)) 1 := by
  simpa using chop_append_forestLevelsAt_grand n 1 (by omega) [] gs ps

/-- Every ordered structural chop is exactly the executable level-sequence `chop`.  The arbitrary
prefix is the context accumulated while descending through the rightmost branch. -/
theorem chop_append_forestLevelsAt_of_rightChop {n : ℕ} {h h' : Tree}
    (hc : RightChop n h h') (a : List ℕ) (d : ℕ) (hd : 1 ≤ d) :
    chop n (a ++ Tree.forestLevelsAt h.children d) =
      a ++ Tree.forestLevelsAt h'.children d := by
  induction hc generalizing a d with
  | grand gs ps =>
      exact chop_append_forestLevelsAt_grand n d hd a gs ps
  | @deep gs c c' hc ih =>
      cases c with
      | node cs =>
        cases c' with
        | node cs' =>
          have hrec := ih (a ++ Tree.forestLevelsAt gs d ++ [d]) (d + 1) (by omega)
          simpa only [Tree.children_node, Tree.forestLevelsAt_append,
            Tree.forestLevelsAt_cons, Tree.forestLevelsAt_nil, Tree.levelsAt_node,
            List.append_nil, List.singleton_append, List.append_assoc] using hrec

/-- A rightmost tree step and the executable chop agree on the preorder level encoding. -/
theorem chop_forestLevelsAt_of_rightStep {n : ℕ} {cs cs' : List Tree}
    (hs : RightStep n (.node cs) (.node cs')) :
    chop n (Tree.forestLevelsAt cs 1) = Tree.forestLevelsAt cs' 1 := by
  cases hs with
  | root => exact chop_forestLevelsAt_root n cs'
  | chop hc =>
      simpa using chop_append_forestLevelsAt_of_rightChop hc [] 1 (by omega)

/-- Version of `chop_forestLevelsAt_of_rightStep` with arbitrary tree endpoints. -/
theorem chop_encoding_of_rightStep {n : ℕ} {h h' : Tree} (hs : RightStep n h h') :
    chop n (Tree.forestLevelsAt h.children 1) =
      Tree.forestLevelsAt h'.children 1 := by
  cases h with
  | node cs =>
      cases h' with
      | node cs' => exact chop_forestLevelsAt_of_rightStep hs

/-- A nonempty executable chop has tree representatives related by the strict well-founded
tree order. -/
theorem chop_strict_tree_descent (n : ℕ) {t : List ℕ} (ht : WF t) (hne : t ≠ []) :
    ∃ h h', Tree.forestLevelsAt h.children 1 = t ∧
      Tree.forestLevelsAt h'.children 1 = chop n t ∧ TreeLt h' h := by
  obtain ⟨cs, hcs⟩ := exists_forestLevelsAt_of_wf ht
  have htree : Tree.node cs ≠ Tree.leaf := by
    intro heq
    have : cs = [] := by simpa [Tree.leaf] using heq
    subst cs
    have ht_nil : t = [] := by
      simpa only [Tree.forestLevelsAt_nil] using hcs.symm
    exact hne ht_nil
  obtain ⟨h', hs⟩ := rightStep_exists n (.node cs) htree
  refine ⟨.node cs, h', ?_, ?_, rightStep_lt hs⟩
  · simpa using hcs
  · rw [← hcs]
    exact (chop_encoding_of_rightStep hs).symm

/-- Choose the unique kind of ordered move available from a live tree; keep the dead tree fixed. -/
noncomputable def rightNext (n : ℕ) (h : Tree) : Tree := by
  classical
  exact if hdead : h = Tree.leaf then Tree.leaf else (rightStep_exists n h hdead).choose

@[simp] theorem rightNext_leaf (n : ℕ) : rightNext n Tree.leaf = Tree.leaf := by
  simp [rightNext]

theorem rightNext_step (n : ℕ) {h : Tree} (hne : h ≠ Tree.leaf) :
    RightStep n h (rightNext n h) := by
  simpa [rightNext, hne] using (rightStep_exists n h hne).choose_spec

/-- The tree battle driven by an arbitrary sequence of copy counts. -/
noncomputable def rightBattle (turn : ℕ → ℕ) (h : Tree) : ℕ → Tree
  | 0 => h
  | k + 1 => rightNext (turn k) (rightBattle turn h k)

/-- Repeated executable list chops driven by arbitrary copy counts. -/
def chopBattle (turn : ℕ → ℕ) (t : List ℕ) : ℕ → List ℕ
  | 0 => t
  | k + 1 => chop (turn k) (chopBattle turn t k)

/-- The chosen ordered tree battle encodes exactly the repeated executable list chops. -/
theorem rightBattle_encoding {turn : ℕ → ℕ} {cs : List Tree} {t : List ℕ}
    (henc : Tree.forestLevelsAt cs 1 = t) : ∀ k,
    Tree.forestLevelsAt (rightBattle turn (.node cs) k).children 1 = chopBattle turn t k := by
  intro k
  induction k with
  | zero => simpa [rightBattle, chopBattle] using henc
  | succ k ih =>
      rw [chopBattle, ← ih, rightBattle]
      by_cases hk : rightBattle turn (.node cs) k = Tree.leaf
      · rw [hk]
        rw [rightNext_leaf]
        simp [Tree.leaf]
      · exact (chop_encoding_of_rightStep (rightNext_step (turn k) hk)).symm

/-- Every well-formed level sequence dies after finitely many rightmost chops, for any schedule of
finite copy counts. -/
theorem chopBattle_terminates (turn : ℕ → ℕ) (t : List ℕ) (ht : WF t) :
    ∃ N, chopBattle turn t N = [] := by
  obtain ⟨cs, hcs⟩ := exists_forestLevelsAt_of_wf ht
  have hstep : ∀ k, rightBattle turn (.node cs) k ≠ Tree.leaf →
      RightStep (turn k) (rightBattle turn (.node cs) k)
        (rightBattle turn (.node cs) (k + 1)) := by
    intro k hk
    simpa [rightBattle] using rightNext_step (turn k) hk
  obtain ⟨N, hN⟩ := rightBattle_terminates (H := rightBattle turn (.node cs)) hstep
  refine ⟨N, ?_⟩
  rw [← rightBattle_encoding hcs, hN]
  simp [Tree.leaf]

/-! Small encoding controls.  The full chop bridge follows in this module. -/

example : Tree.levelsAt (.node []) 3 = [3] := by decide +kernel
example : Tree.levelsAt (.node [.node [], .node [.node []]]) 1 = [1, 2, 2, 3] := by
  decide +kernel

example (n : ℕ) :
    TreeStep n (.node [.node [.node []]])
      (.node (List.replicate (n + 1) (.node []))) :=
  TreeStep.chop (TreeChop.grand (List.Perm.refl _) (List.Perm.refl _))

end GoodsteinTM
