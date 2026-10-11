#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Vet the BMO#7 and BMO#9 Lean statements against their sources, independently of the proofs.

Checks (each prints PASS/FAIL; exit 1 on any FAIL):

  lean      The Lean statements' own recurrences (`tools/bmo-vet/Vet.lean`, which instantiates the
            proved headlines) agree with the wiki definitions, reimplemented here from the wiki text:
            BMO#7 for n < 300, BMO#9 for 400 rewrite steps.
  listed    BMO#7's first values match the ten listed in the docstring.
  macro9    BMO#9's wiki single-step rules compose into the macro rules E and O of busycoq's
            `verify/BMO9.v` module `Prefix`, which is the system the Rocq proof shows never halts.
  tm9       BMO#9's wiki rules match the Turing machine itself: for every small configuration xs,
            the TM run from `Config xs` reaches `Config (T xs)`, or halts exactly when T halts.
            `Config` is the tape encoding in `BMO9.v` module `TM1`.  Also, the TM run from the
            blank tape visits the first 150 wiki configurations in order.
  pinned    The statement in the formal-conjectures branch is the statement at the pinned
            `formal_proof` link, character for character up to whitespace, and the link's line
            anchor points at it.

Usage: bmo_statement_vet.py [--lean-root DIR] [--fc-repo DIR] [--skip-lean] [--skip-pinned]
       bmo_statement_vet.py test
"""

import argparse
import itertools
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

# ---------------------------------------------------------------- BMO#7, from the wiki text


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def f7(n: int) -> int:
    return n + 1 + v2(n + 1) % 2


def a7(count: int) -> list[int]:
    a = [1]
    for n in range(count - 1):
        x = a[-1] // 2
        for _ in range(n + 2):
            x = f7(x)
        a.append(x)
    return a


LISTED7 = [1, 3, 5, 7, 11, 15, 17, 19, 21, 23]  # docstring and wiki "first values"

# ---------------------------------------------------------------- BMO#9, from the wiki text


def canon(xs) -> tuple[int, ...]:
    xs = tuple(xs)
    while xs and xs[-1] == 0:
        xs = xs[:-1]
    return xs


def wiki9(xs):
    """The four published rewrite rules; None = Halt."""
    x0, x1, x2 = (tuple(xs) + (0, 0, 0))[:3]
    r = tuple(xs)[3:]
    if x0 == 0:
        return canon((3 + x1 + x2,) + r)
    if x0 == 1:
        return None if x1 == 0 else canon((x1 - 1, 0, 1, 1 + x2) + r)
    return canon((x0 - 2, 1 + x1, 1 + x2) + r)


def traj9(step, count: int) -> list[tuple[int, ...]]:
    t = [()]
    while len(t) < count:
        t.append(step(t[-1]))
    return t


# ---------------------------------------------------------------- BMO#9 Turing machine

TM9 = "1RB1LA_1RC0RD_1LA---_1RE1RD_1LF0LA_---0LE"


def parse_tm(s: str):
    table = {}
    for q, blk in enumerate(s.split("_")):
        for sym in (0, 1):
            tr = blk[3 * sym:3 * sym + 3]
            table[q, sym] = None if tr[2] == "-" else (int(tr[0]), 1 if tr[1] == "R" else -1,
                                                       ord(tr[2]) - 65)
    return table


def config9(xs) -> tuple[int, frozenset]:
    """busycoq BMO9.v `TM1.Config`: [u;v;w;r..] = S1 v u w (tail_words r), where
    S1 a b c r = 0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0;0] *> [1]^^c *> r.
    `l <{{q}} r` reads the top of l (TM.v), so the head is on the [0].
    Returns (state, set of 1-cell offsets from the head)."""
    u, v, w = (tuple(xs) + (0, 0, 0))[:3]
    rest = tuple(xs)[3:]
    ones = {-k for k in range(1, v + 1)}            # 1^a, a = v, left of the head cell
    cells = [1] * u + [0, 0] + [1] * w
    for n in rest:                                   # tail_words: [0] *> [1]^^n *> ...
        cells += [0] + [1] * n
    ones |= {k + 1 for k, c in enumerate(cells) if c}
    return 0, frozenset(ones)


def run_until(table, start, targets: dict, bound: int):
    """Run from start; return the first target key reached, 'halt', or None at the bound."""
    state, ones = start
    tape = set(ones)
    pos = 0
    for _ in range(bound):
        tr = table[state, 1 if pos in tape else 0]
        if tr is None:
            return "halt"
        w, d, state = tr
        (tape.add if w else tape.discard)(pos)
        pos += d
        if state == 0:  # every Config is in state A
            key = (state, frozenset(p - pos for p in tape))
            if key in targets:
                return targets[key]
    return None


# ---------------------------------------------------------------- checks


def check_lean(lean_root: Path, count7=300, count9=400) -> list[str]:
    out = subprocess.run(["lake", "env", "lean", str(REPO / "tools/bmo-vet/Vet.lean")],
                         cwd=lean_root, capture_output=True, text=True)
    if out.returncode:
        return [f"Vet.lean failed to elaborate:\n{out.stdout}{out.stderr}"]
    got7, got9 = {}, {}
    for line in out.stdout.splitlines():
        tag, n, val = (line.split(" ", 2) + [""])[:3]
        if tag == "a7":
            got7[int(n)] = int(val)
        elif tag == "x9":
            got9[int(n)] = tuple(int(x) for x in val.split(",")) if val else ()
    errs = []
    want7 = a7(count7)
    if [got7.get(n) for n in range(count7)] != want7:
        bad = next(n for n in range(count7) if got7.get(n) != want7[n])
        errs.append(f"BMO#7: Lean a {bad} = {got7.get(bad)}, wiki gives {want7[bad]}")
    want9 = traj9(wiki9, count9)
    if [got9.get(n) for n in range(count9)] != want9:
        bad = next(n for n in range(count9) if got9.get(n) != want9[n])
        errs.append(f"BMO#9: Lean x {bad} = {got9.get(bad)}, wiki gives {want9[bad]}")
    return errs


def check_listed() -> list[str]:
    got = a7(len(LISTED7))
    return [] if got == LISTED7 else [f"BMO#7 first values {got} != listed {LISTED7}"]


def check_macro9(step=wiki9, size=7) -> list[str]:
    """busycoq Prefix.Step: E (2n,v,w,r) -> (2n+v+w+3, r);
    O (2n+1,v,w,r) -> (n+v-1, 0, 1, w+n+1, r) when 1 <= n+v.  Each takes n+1 wiki steps."""
    errs = []
    for n, v, w, r0, r1 in itertools.product(range(size), repeat=5):
        r = (r0, r1)
        for start, want in (((2 * n, v, w) + r, (2 * n + v + w + 3,) + r),
                            ((2 * n + 1, v, w) + r,
                             (n + v - 1, 0, 1, w + n + 1) + r if n + v >= 1 else None)):
            x = canon(start)
            for _ in range(n + 1):
                x = step(x) if x is not None else None
            if x != (canon(want) if want is not None else None):
                errs.append(f"macro from {start}: wiki gives {x}, BMO9.v gives {want}")
    return errs[:5]


def check_tm9(step=wiki9, size=5, steps=150) -> list[str]:
    table = parse_tm(TM9)
    errs = []
    for n in range(1, 6):
        for xs in itertools.product(range(size), repeat=n):
            xs = canon(xs)
            nxt = step(xs)
            if nxt is None:
                got = run_until(table, config9(xs), {}, 10_000)
                if got != "halt":
                    errs.append(f"T{xs} halts, TM from Config{xs} does not")
            else:
                got = run_until(table, config9(xs), {config9(nxt): "hit"}, 20_000)
                if got != "hit":
                    errs.append(f"T{xs} = {nxt}, TM from Config{xs} gives {got}")
    want = traj9(step, steps)
    targets = {config9(x): k for k, x in enumerate(want)}
    state, ones = config9(())
    tape, pos, k, last = set(ones), 0, 1, 0
    for t in range(50_000_000):
        if k == len(want) or t - last > 1_000_000:  # done, or stalled on a mismatch
            break
        tr = table[state, 1 if pos in tape else 0]
        if tr is None:
            errs.append("TM halted from the blank tape")
            break
        w, d, state = tr
        (tape.add if w else tape.discard)(pos)
        pos += d
        if state == 0 and targets.get((state, frozenset(p - pos for p in tape))) == k:
            k, last = k + 1, t
    if k < len(want):
        errs.append(f"blank-tape TM run reached wiki configurations 0..{k - 1} of {len(want) - 1}")
    return errs[:5]


def theorem_text(src: str, name: str) -> tuple[str, int]:
    m = re.search(rf"^theorem {name}\b(.*?):= by", src, re.S | re.M)
    if not m:
        return "", 0
    return " ".join(m.group(0).split()), src[:m.start()].count("\n") + 1


def git_show(repo: Path, rev: str, path: str) -> str:
    return subprocess.run(["git-ro", "-C", str(repo), "show", f"{rev}:{path}"],
                          check=True, capture_output=True, text=True).stdout


FC_FILE = "FormalConjectures/Other/BeaverMathOlympiad.lean"


def check_pinned(fc_repo: Path, branches: dict) -> list[str]:
    errs = []
    for num, ref in branches.items():
        fc = git_show(fc_repo, ref, FC_FILE)
        name = f"beaver_math_olympiad_problem_{num}"
        fc_text, _ = theorem_text(fc, name)
        m = re.search(rf'formal_proof using lean4 at\s*"https://github.com/gotrevor/collatz-cryptid/'
                      rf'blob/([0-9a-f]{{40}})/(\S+?)#L(\d+)"\]\s*theorem {name}\b', fc)
        if not (fc_text and m):
            errs.append(f"BMO#{num}: no statement or pinned link on {ref}")
            continue
        sha, path, line = m.group(1), m.group(2), int(m.group(3))
        pinned_text, pinned_line = theorem_text(git_show(REPO, sha, path), name)
        if pinned_text.split(":=")[0] != fc_text.split(":=")[0]:
            errs.append(f"BMO#{num}: {ref} statement differs from {sha[:9]}:{path}")
        if pinned_line != line:
            errs.append(f"BMO#{num}: link anchor #L{line}, theorem is at line {pinned_line}")
    return errs


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("command", nargs="?", choices=["test"])
    p.add_argument("--lean-root", type=Path, default=REPO,
                   help="checkout whose built oleans `lake env lean` uses (default: this repo)")
    p.add_argument("--fc-repo", type=Path, default=Path.home() / "src/forks/formal-conjectures")
    p.add_argument("--fc-branch", action="append", default=[], metavar="N=REF",
                   help="formal-conjectures ref holding BMO#N (default 7=bmo-7-only 9=bmo-9)")
    p.add_argument("--skip-lean", action="store_true")
    p.add_argument("--skip-pinned", action="store_true")
    args = p.parse_args()
    if args.command == "test":
        raise SystemExit(subprocess.call([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
                                          str(REPO / "tests" / "test_bmo_statement_vet.py")]))
    branches = dict(b.split("=", 1) for b in args.fc_branch) or {"7": "bmo-7-only", "9": "bmo-9"}
    checks = [("listed", check_listed), ("macro9", check_macro9), ("tm9", check_tm9)]
    if not args.skip_lean:
        checks.insert(0, ("lean", lambda: check_lean(args.lean_root)))
    if not args.skip_pinned:
        checks.append(("pinned", lambda: check_pinned(args.fc_repo, branches)))
    failed = False
    for name, check in checks:
        errs = check()
        print(f"{'PASS' if not errs else 'FAIL'}  {name}")
        for e in errs:
            print(f"      {e}")
        failed |= bool(errs)
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
