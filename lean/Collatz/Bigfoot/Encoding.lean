import Collatz.BB
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
configuration with tape `0^∞ 12^a 11^(b+c) 0^∞`, state `A`, head at
position `2a + 2b - 1`. -/
def bigfootEnc (d : Dyn) : BB.Cfg :=
  let A : ℤ := 2 * (d.a : ℤ)
  let span : ℤ := A + 2 * ((d.b : ℤ) + (d.c : ℤ))
  let hdpos : ℤ := A + 2 * (d.b : ℤ) - 1
  ⟨BB.State.A,
    fun (i : ℤ) =>
      if i < 0 then BB.Sym.s0
      else if i ≥ span then BB.Sym.s0
      else if i < A then
        if i % 2 = 0 then BB.Sym.s1 else BB.Sym.s2
      else BB.Sym.s1,
    hdpos⟩

/-- For Bigfoot's initial state `A(2, 1, 2)`, the encoded head sits at
position 5. -/
example : (bigfootEnc Dyn.init).pos = 5 := by
  unfold bigfootEnc Dyn.init
  rfl

/-- For `A(2, 1, 2)`, the tape at positions 0..9 carries
`1 2 1 2 1 1 1 1 1 1`, matching the Quick_Sim cell-level trace at
TM step 69. -/
example :
    (bigfootEnc Dyn.init).tape 0 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 1 = BB.Sym.s2 ∧
    (bigfootEnc Dyn.init).tape 2 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 3 = BB.Sym.s2 ∧
    (bigfootEnc Dyn.init).tape 4 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 5 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 6 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 7 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 8 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape 9 = BB.Sym.s1 ∧
    (bigfootEnc Dyn.init).tape (-1) = BB.Sym.s0 ∧
    (bigfootEnc Dyn.init).tape 10 = BB.Sym.s0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold bigfootEnc Dyn.init; rfl)

end Collatz.Bigfoot
