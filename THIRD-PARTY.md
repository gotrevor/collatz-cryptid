# Third-party notices

This repository is licensed under Apache-2.0 (see `LICENSE`).  It also contains work
derived from the projects below, whose notices are reproduced as their licences require.

## busycoq — MIT

Parts of `lean/Collatz/BB/` are a **Lean 4 port of Rocq/Coq sources from
[`meithecatte/busycoq`](https://github.com/meithecatte/busycoq)** and its BB(6) fork
[`ccz181078/busycoq`](https://github.com/ccz181078/busycoq).  The port follows the
originals closely enough that names and lemma statements correspond one-to-one.

Derived material, by original source file:

| Original (busycoq) | Lean port here |
|---|---|
| `verify/TM.v` — `side`, tape ops, `-[M]->` / `-[M]->*` | `lean/Collatz/BB/SideTape.lean`, `lean/Collatz/BB/Multistep.lean` |
| `verify/TM.v` — `halts`, `multistep_nonhalt`, `progress_nonhalt_simple` | `lean/Collatz/BB/Multistep.lean` |
| `verify/TM.v` — `merge_1`, `merge_2`, `r20_l12` and friends | `lean/Collatz/BB/SideTape.lean` |
| `verify/BB33_494.v` — the 494 non-halting proof | `lean/Collatz/BB33_494.lean` |

Original licence text, reproduced verbatim from the busycoq `LICENSE`:

```
Copyright (c) 2023 Maja Kądziołka

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software
is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
```

## bbchallenge wiki — CC BY

Machine names, discovery attributions and the Cryptid taxonomy referenced throughout
`notes/` come from [wiki.bbchallenge.org](https://wiki.bbchallenge.org), whose content is
available under Creative Commons Attribution unless otherwise noted.  No wiki text is
reproduced verbatim in this repository.

## Reference papers

PDFs of cited papers are **not** committed.  `notes/refs.md` links to arXiv.
