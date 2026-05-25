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

/-- 🚧 The full bootstrap: tape equality on top of state + pos.

Open. The hard part is tape equality `(stepN 69 blank).get.tape = (bigfootEnc init).tape`
on `ℤ → Sym`. Strategy: a `Tape.ext_of_support` lemma + per-cell `decide`
on each of the 10 active positions + a "blank-outside-support" lemma for
the post-69-step tape. The blank-outside lemma needs to track which
positions can possibly have been written during 69 steps (head visited
[-4, 5]). Likely a custom-induction proof. Estimated ~2-4 more hours.
-/
theorem bootstrap_full :
    BB.stepN machine 69 BB.Cfg.blank = some (bigfootEnc Dyn.init) :=
  sorry

end Collatz.Bigfoot
