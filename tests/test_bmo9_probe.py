"""Independent rule examples from the published four-branch definition."""

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "sandbox" / "bmo9_probe.py"


def run(*args: str):
    result = subprocess.run([sys.executable, str(SCRIPT), *args],
                            check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def test_published_rules():
    assert run("step", "0,2,3,7") == [8, 7]
    assert run("step", "1,0,1") is None
    assert run("step", "1,3,2,5") == [2, 0, 1, 3, 5]
    assert run("step", "4,2,3") == [2, 3, 4]


def test_implicit_zero_tail():
    assert run("step", "") == [3]
    assert run("step", "1,2") == [1, 0, 1, 1]
