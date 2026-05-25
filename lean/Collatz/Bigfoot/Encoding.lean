import Collatz.BB
import Collatz.Bigfoot.Machine
import Collatz.Bigfoot.Dynamics

/-!
# Bigfoot encoding: `Dyn → BB.Cfg`

Ligocki's parametric form (Bigfoot blog, 2023-10-16):

```
0^∞ 12^a 11^b <A 11^c 0^∞
```

Reading cells left to right at positions 0, 1, 2, ...:
* Positions `[0, 2a)` carry the alternating block `1 2 1 2 ... 1 2`
  (the `12^a` part). Cell at position `i` has value `1` when `i` is even,
  `2` when `i` is odd.
* Positions `[2a, 2a + 2(b+c))` carry all `1`s
  (the `11^b 11^c` blocks - they're indistinguishable at the cell level).
* All other positions are blank (`0`).
* Head: state `A`, at position `2a + 2b - 1`
  (the *last* cell of the `11^b` block), facing left.

Verified for `A(2, 1, 2)` against `Quick_Sim` micro-trace: at TM step 69
the tape reads `1 2 1 2 1 1 1 1 1 1` with the head at position 5
(= `2·2 + 2·1 - 1`).

The "facing left" direction isn't part of `BB.Cfg` (which only tracks
state + tape + position). The cell-the-head-reads convention is "the
cell at `pos`", so we set `pos = 2a + 2b - 1`, the cell whose value
gets rewritten on the next TM step.
-/

namespace Collatz.Bigfoot

/-- The Bigfoot encoding: a `Dyn` state `A(a, b, c)` becomes the TM
configuration with tape `0^∞ 12^a 11^(b+c) 0^∞`, anchored so the
start of the `11^(b+c)` block is at position `0` (matching where the
TM ends up after the 69-step bootstrap from blank).

- Positions `[-2a, 0)` carry the `12^a` block: cell `i` is `1` when `i`
  is even, `2` when `i` is odd.
- Positions `[0, 2(b+c))` carry all `1`s.
- All other positions are blank `0`.
- Head: state `A`, position `2b - 1` (last cell of the `11^b` part,
  i.e., where `<A` sits in Quick_Sim notation). -/
def bigfootEnc (d : Dyn) : BB.Cfg :=
  let leftEdge : ℤ := -(2 * (d.a : ℤ))
  let rightEdge : ℤ := 2 * ((d.b : ℤ) + (d.c : ℤ))
  let hdpos : ℤ := 2 * (d.b : ℤ) - 1
  ⟨BB.State.A,
    fun (i : ℤ) =>
      if i < leftEdge then BB.Sym.s0
      else if i ≥ rightEdge then BB.Sym.s0
      else if i < 0 then
        if i % 2 = 0 then BB.Sym.s1 else BB.Sym.s2
      else BB.Sym.s1,
    hdpos⟩

/-- For Bigfoot's initial state `A(2, 1, 2)`, the encoded head sits at
Lean position `2·1 - 1 = 1`. (Quick_Sim's `<A` between `1^2` and `1^4`
maps to absolute position 1 in the post-bootstrap tape.) -/
example : (bigfootEnc Dyn.init).pos = 1 := by
  unfold bigfootEnc Dyn.init
  rfl

/-- For `A(2, 1, 2)`, the tape at positions -4..5 reads
`1 2 1 2 | 1 1 1 1 1 1` (vertical bar marks the position-0 anchor,
i.e., the start of the `11^(b+c)` block). -/
example :
    (bigfootEnc Dyn.init).tape (-4) = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape (-3) = BB.Sym.s2 ∧
    (bigfootEnc Dyn.init).tape (-2) = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape (-1) = BB.Sym.s2 ∧
    (bigfootEnc Dyn.init).tape 0 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 1 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 2 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 3 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 4 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 5 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape (-5) = BB.Sym.s0 ∧
    (bigfootEnc Dyn.init).tape 6 = BB.Sym.s0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold bigfootEnc Dyn.init; rfl)

/-! ## Bootstrap probe

Cheap experiments. `rfl` won't suffice because `BB.Tape` is `ℤ → Sym` and
function equality isn't definitional in Lean. But the *state* and *pos*
projections of `stepN machine 69 Cfg.blank` should reduce to concrete
values - those are pure `decide`-able comparisons.
-/

/-! ## Bootstrap

The bridge: 69 TM steps from the blank tape land on `bigfootEnc init`. -/

-- State after 69 micro-steps is `A`.
set_option maxRecDepth 2000 in
theorem bootstrap_state :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.state) =
      some BB.State.A := by
  decide

-- Head position after 69 micro-steps is `1`
-- (= `2·1 - 1` for `(b, c) = (1, 2)`).
set_option maxRecDepth 2000 in
theorem bootstrap_pos :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.pos) =
      some 1 := by
  decide

/-! ### Tape equality at specific positions

For i ∈ [-4, 5], (stepN 69 blank).tape i is decidable and matches
bigfootEnc init's tape. We prove each of the 10 positions individually
via `decide`.
-/

set_option maxRecDepth 2000 in
theorem bootstrap_tape_neg4 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape (-4)) =
      some BB.Sym.s1 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_neg3 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape (-3)) =
      some BB.Sym.s2 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_neg2 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape (-2)) =
      some BB.Sym.s1 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_neg1 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape (-1)) =
      some BB.Sym.s2 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_0 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape 0) =
      some BB.Sym.s1 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_1 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape 1) =
      some BB.Sym.s1 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_2 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape 2) =
      some BB.Sym.s1 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_3 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape 3) =
      some BB.Sym.s1 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_4 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape 4) =
      some BB.Sym.s1 := by decide

set_option maxRecDepth 2000 in
theorem bootstrap_tape_5 :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape 5) =
      some BB.Sym.s1 := by decide

/-! ### Position bounds

The head moves by exactly ±1 per micro-step, so after `n` steps from
configuration `c`, the head's position is within `[c.pos - n, c.pos + n]`.
-/

lemma BB.step_pos_diff {M : BB.Machine} {c c' : BB.Cfg}
    (h : BB.step M c = some c') :
    c'.pos = c.pos + 1 ∨ c'.pos = c.pos - 1 := by
  unfold BB.step at h
  rcases hM : M c.state (c.tape.read c.pos) with _ | t
  · rw [hM] at h; simp at h
  · rw [hM] at h
    simp only [Option.map_some] at h
    have hc' : c' = ⟨t.state, c.tape.write c.pos t.write, BB.shift t.dir c.pos⟩ :=
      (Option.some.inj h).symm
    rw [hc']
    cases t.dir with
    | L => right; rfl
    | R => left; rfl

lemma BB.stepN_pos_dist {M : BB.Machine} {n : ℕ} {c c' : BB.Cfg}
    (h : BB.stepN M n c = some c') :
    (-(n : ℤ)) ≤ c'.pos - c.pos ∧ c'.pos - c.pos ≤ (n : ℤ) := by
  induction n generalizing c' with
  | zero =>
    rw [show BB.stepN M 0 c = some c from rfl] at h
    have : c = c' := Option.some.inj h
    subst this
    exact ⟨by simp, by simp⟩
  | succ k ih =>
    rw [show BB.stepN M (k+1) c = (BB.stepN M k c).bind (BB.step M) from rfl] at h
    rcases hk : BB.stepN M k c with _ | ck
    · rw [hk] at h; simp at h
    · rw [hk] at h
      have hstep_some : BB.step M ck = some c' := h
      obtain ⟨ih_lo, ih_hi⟩ := ih hk
      rcases BB.step_pos_diff hstep_some with hstep | hstep
      · refine ⟨?_, ?_⟩ <;> push_cast <;> omega
      · refine ⟨?_, ?_⟩ <;> push_cast <;> omega

/-- One step doesn't change the tape value at any position other than
the head's current cell. -/
lemma BB.step_tape_other {M : BB.Machine} {c c' : BB.Cfg} (i : ℤ)
    (h : BB.step M c = some c') (hne : i ≠ c.pos) :
    c'.tape i = c.tape i := by
  unfold BB.step at h
  rcases hM : M c.state (c.tape.read c.pos) with _ | t
  · rw [hM] at h; simp at h
  · rw [hM] at h
    simp only [Option.map_some] at h
    have hc' : c' = ⟨t.state, c.tape.write c.pos t.write, BB.shift t.dir c.pos⟩ :=
      (Option.some.inj h).symm
    rw [hc']
    change (c.tape.write c.pos t.write) i = c.tape i
    unfold BB.Tape.write
    simp [hne]

/-- Over `n` steps, the tape value at position `i` is unchanged if the
head never visits `i` (formally: at every intermediate step `k < n`, the
head's position differs from `i`). -/
lemma BB.stepN_tape_unvisited {M : BB.Machine} {n : ℕ} {c c' : BB.Cfg} (i : ℤ)
    (h : BB.stepN M n c = some c')
    (h_unvisited : ∀ k, k < n → ∀ ck, BB.stepN M k c = some ck → i ≠ ck.pos) :
    c'.tape i = c.tape i := by
  induction n generalizing c' with
  | zero =>
    have hcc : c = c' := Option.some.inj h
    rw [← hcc]
  | succ k ih =>
    rw [show BB.stepN M (k+1) c = (BB.stepN M k c).bind (BB.step M) from rfl] at h
    rcases hk : BB.stepN M k c with _ | ck
    · rw [hk] at h; simp at h
    · rw [hk] at h
      have hstep_some : BB.step M ck = some c' := h
      have hne_at_k : i ≠ ck.pos := h_unvisited k (Nat.lt_succ_self k) ck hk
      have htape_eq : c'.tape i = ck.tape i :=
        BB.step_tape_other i hstep_some hne_at_k
      have ih_app : ck.tape i = c.tape i := by
        apply ih hk
        intro j hj cj hcj
        exact h_unvisited j (Nat.lt_succ_of_lt hj) cj hcj
      rw [htape_eq, ih_app]

-- After 69 steps from blank, the tape at any position with |i| > 69 is s0.
-- The head can shift by at most 1 per step, so positions outside [-69, 69]
-- were never visited.
set_option maxRecDepth 4000 in
lemma BB.stepN_69_blank_tape_far (i : ℤ) (h : 69 < i.natAbs) :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape i) =
      some BB.Sym.s0 := by
  rcases hN : BB.stepN machine 69 BB.Cfg.blank with _ | c
  · -- Show this can't happen via bootstrap_state
    have := bootstrap_state
    rw [hN] at this; simp at this
  · change some (c.tape i) = some BB.Sym.s0
    congr 1
    have hblank_tape : BB.Cfg.blank.tape i = BB.Sym.s0 := rfl
    have h_unv : ∀ k, k < 69 → ∀ ck, BB.stepN machine k BB.Cfg.blank = some ck →
                 i ≠ ck.pos := by
      intro k hk ck hck
      have ⟨lo, hi⟩ := BB.stepN_pos_dist hck
      -- BB.Cfg.blank.pos = 0, so -k ≤ ck.pos ≤ k
      have hblank0 : (BB.Cfg.blank.pos : ℤ) = 0 := rfl
      rw [hblank0] at lo hi
      simp at lo hi
      -- |ck.pos| ≤ k < 69 < |i|, so i ≠ ck.pos
      have hk69 : (k : ℤ) < 69 := by exact_mod_cast hk
      have hi_abs : (69 : ℤ) < |i| := by
        have := h
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h
      intro heq
      rw [heq] at hi_abs
      have habs : |ck.pos| ≤ (k : ℤ) := abs_le.mpr ⟨lo, hi⟩
      omega
    exact (BB.stepN_tape_unvisited i hN h_unv).trans hblank_tape

-- Pointwise tape equality at any bounded position i ∈ [-69, 69].
-- Each of the 139 cases is handled by `decide`.
set_option maxRecDepth 4000 in
lemma bootstrap_tape_at_bounded (i : ℤ) (hlo : -69 ≤ i) (hhi : i ≤ 69) :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape i) =
      some ((bigfootEnc Dyn.init).tape i) := by
  interval_cases i <;> decide

-- Pointwise tape equality at any far position. Both LHS and RHS are s0.
lemma bootstrap_tape_at_far (i : ℤ) (h : 69 < i.natAbs) :
    (BB.stepN machine 69 BB.Cfg.blank).map (fun c => c.tape i) =
      some ((bigfootEnc Dyn.init).tape i) := by
  rw [BB.stepN_69_blank_tape_far i h]
  congr 1
  -- Extract: i > 69 or i < -69
  have hi : i > 69 ∨ i < -69 := by
    have h' : (69 : ℤ) < |i| := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h
    rcases lt_or_ge i 0 with hneg | hnneg
    · right
      have : -i > 69 := by rwa [abs_of_neg hneg] at h'
      omega
    · left
      have : i > 69 := by rwa [abs_of_nonneg hnneg] at h'
      omega
  unfold bigfootEnc Dyn.init
  push_cast
  rcases hi with hpos | hneg
  all_goals (split_ifs <;> first | rfl | omega)

-- The full bootstrap. Combines state, pos, and tape equality.
set_option maxRecDepth 4000 in
theorem bootstrap_full :
    BB.stepN machine 69 BB.Cfg.blank = some (bigfootEnc Dyn.init) := by
  rcases hN : BB.stepN machine 69 BB.Cfg.blank with _ | c
  · -- Contradicts bootstrap_state.
    exfalso
    have := bootstrap_state
    rw [hN] at this
    simp at this
  · -- Show c = bigfootEnc Dyn.init by deconstructing.
    have hs : c.state = BB.State.A := by
      have := bootstrap_state; rw [hN] at this; simpa using this
    have hp : c.pos = 1 := by
      have := bootstrap_pos; rw [hN] at this; simpa using this
    -- hs : c.state = State.A, hp : c.pos = 1
    have htape : ∀ i, c.tape i = (bigfootEnc Dyn.init).tape i := by
      intro i
      by_cases h : 69 < i.natAbs
      · -- Far case
        have hf := bootstrap_tape_at_far i h
        rw [hN] at hf
        simpa using hf
      · -- Bounded case: |i| ≤ 69, so -69 ≤ i ≤ 69
        push_neg at h
        have h_abs : |i| ≤ 69 := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast h
        obtain ⟨hlo, hhi⟩ := abs_le.mp h_abs
        have hb := bootstrap_tape_at_bounded i hlo hhi
        rw [hN] at hb
        simpa using hb
    -- Assemble c = bigfootEnc Dyn.init via componentwise equality.
    congr 1
    have henc_state : (bigfootEnc Dyn.init).state = BB.State.A := by
      unfold bigfootEnc Dyn.init; rfl
    have henc_pos : (bigfootEnc Dyn.init).pos = 1 := by
      unfold bigfootEnc Dyn.init; rfl
    ext
    · rw [hs, henc_state]
    · funext i; exact htape i
    · rw [hp, henc_pos]

end Collatz.Bigfoot
