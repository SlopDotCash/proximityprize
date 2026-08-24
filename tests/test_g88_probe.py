"""Unit coverage for scripts/probes/probe_g88.py.

The probe function is a self-contained verification of rotation invariance,
Parseval identity, class-mass quantization, frame collisions, and the
shadow-energy bracket. Importing the module runs four small demo cells
(all fast: n^r <= 16^3); the tests re-run the same cells and add extra
small instances, asserting the invariants directly.
"""

import contextlib
import io
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

# Module-level probe() calls run at import; capture their stdout.
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    import probe_g88  # noqa: E402

from probe_g88 import probe  # noqa: E402


def test_module_demo_cells_pass() -> None:
    out = buf.getvalue()
    assert out.count("ALL OK") == 5  # 5 demo cells in the module


def test_probe_rotation_invariance_small() -> None:
    # p=17, g=4 (order 4), n=4, m=2, r=2 — runs the invariant asserts.
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        probe(17, 4, 4, 2, 2)
    assert "ALL OK" in out.getvalue()


def test_probe_r3_cell() -> None:
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        probe(17, 4, 4, 2, 3)
    assert "ALL OK" in out.getvalue()


def test_probe_p97_cell() -> None:
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        probe(97, 33, 8, 4, 2)
    assert "ALL OK" in out.getvalue()
