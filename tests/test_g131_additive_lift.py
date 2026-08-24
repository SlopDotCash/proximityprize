"""Unit coverage for scripts/probes/probe_466_g131_additive_lift_saddle.py.

Tests the additive-lift envelope root formula: the positive root of
x^2 = n*x + 4*rho*W*n^2, and the certificate logic that x = T+1 must be
excluded by the quadratic constraint.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_466_g131_additive_lift_saddle import check, root_upper  # noqa: E402


def test_root_upper_small_cell() -> None:
    n, rho, W = 16, 1, 64
    root = root_upper(n, rho, W)
    # Envelope x^2 <= n*x + 4*rho*W*n^2 = 16x + 4*64*256.
    # At root: x^2 - 16x - 65536 = 0 → x = (16 + sqrt(256+262144))/2.
    import math

    expected = (n + math.sqrt(n * n + 16 * rho * W * n * n)) / 2
    assert root == expected


def test_root_upper_positive() -> None:
    for n, rho, W in [(16, 1, 64), (32, 1, 256), (64, 1, 1024)]:
        root = root_upper(n, rho, W)
        assert root > n  # root exceeds the linear term


def test_check_witness_excludes_T_plus_1() -> None:
    # For the recorded small cell (16, 257, 4): window_ok and the witness
    # x = T+1 must satisfy the envelope (x^2 <= rhs), per the probe claim.
    import io
    import contextlib

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        check(16, 257, 4, 1)
    out = buf.getvalue()
    assert "window_ok=True" in out
    assert "witness_Tplus1_ok=True" in out


def test_check_production_cells() -> None:
    # The production-shaped windows must all be valid (window_ok).
    import io
    import contextlib

    cells = [
        (16, 257, 4, 1),
        (32, 1153, 5, 1),
        (64, 4289, 6, 1),
        (128, 17921, 9, 1),
    ]
    for row in cells:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            check(*row)
        assert "window_ok=True" in buf.getvalue()
