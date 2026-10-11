"""Teeth for tools/sandbox/bmo_statement_vet.py: every check must fail on a planted defect.

The Lean tests need built oleans for Collatz.BMO.Problem7/9 under $BMO_VET_LEAN_ROOT (default:
this repo) and take about a minute; they are skipped when the oleans are missing.
"""

import importlib.util
import os
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("vet", REPO / "tools/sandbox/bmo_statement_vet.py")
vet = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vet)

LEAN_ROOT = Path(os.environ.get("BMO_VET_LEAN_ROOT", REPO))
HAVE_OLEANS = (LEAN_ROOT / ".lake/build/lib/lean/Collatz/BMO/Problem9.olean").exists()


WIKI9 = vet.wiki9


def wrong_rule1(xs):
    """Rule 1 with 2 + a + c instead of 3 + a + c."""
    x = WIKI9(xs)
    if xs[:1] in ((), (0,)) and x is not None:
        return (x[0] - 1,) + x[1:]
    return x


def test_clean_checks_pass():
    assert vet.check_listed() == []
    assert vet.check_macro9() == []
    assert vet.check_tm9(size=3, steps=40) == []


def test_macro9_catches_a_wrong_rule():
    assert vet.check_macro9(step=wrong_rule1, size=3)


def test_tm9_catches_a_wrong_rule():
    assert vet.check_tm9(step=wrong_rule1, size=3, steps=40)


def test_tm9_catches_a_wrong_encoding(monkeypatch):
    real = vet.config9
    monkeypatch.setattr(vet, "config9", lambda xs: real(tuple(xs)[1:2] + tuple(xs)[:1] + tuple(xs)[2:]))
    assert vet.check_tm9(size=3, steps=40)


def test_listed_catches_a_wrong_value(monkeypatch):
    monkeypatch.setattr(vet, "LISTED7", vet.LISTED7[:-1] + [25])
    assert vet.check_listed()


@pytest.mark.parametrize("old,new,msg", [("a 0 = 1", "a 0 = 3", "differs"),
                                          ("\ntheorem beaver", "\n\ntheorem beaver", "anchor")])
def test_pinned_catches_a_changed_statement_or_anchor(monkeypatch, old, new, msg):
    fc = Path.home() / "src/forks/formal-conjectures"
    if not fc.exists():
        pytest.skip("no formal-conjectures checkout")
    assert vet.check_pinned(fc, {"7": "bmo-7-only"}) == []
    real = vet.git_show
    monkeypatch.setattr(vet, "git_show", lambda repo, rev, path: (
        real(repo, rev, path).replace(old, new) if repo == vet.REPO else real(repo, rev, path)))
    assert any(msg in e for e in vet.check_pinned(fc, {"7": "bmo-7-only"}))


@pytest.mark.skipif(not HAVE_OLEANS, reason="needs built Collatz.BMO oleans")
def test_lean_comparison_catches_a_wrong_wiki_rule(monkeypatch):
    monkeypatch.setattr(vet, "wiki9", wrong_rule1)
    assert any("BMO#9" in e for e in vet.check_lean(LEAN_ROOT))


@pytest.mark.skipif(not HAVE_OLEANS, reason="needs built Collatz.BMO oleans")
@pytest.mark.parametrize("old,new", [("3 + y 1 + y 2", "2 + y 1 + y 2"),
                                     ("f7^[n + 2]", "f7^[n + 1]")])
def test_vet_lean_rejects_a_recurrence_that_differs_from_the_statement(tmp_path, old, new):
    src = (REPO / "tools/bmo-vet/Vet.lean").read_text()
    assert old in src
    bad = tmp_path / "Vet.lean"
    bad.write_text(src.replace(old, new, 1))
    out = subprocess.run(["lake", "env", "lean", str(bad)], cwd=LEAN_ROOT, capture_output=True, text=True)
    assert out.returncode != 0
