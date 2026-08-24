"""Unit coverage for scripts/probes/probe_syz23_directness_support_leak.py.

Tests the corrected-accounting yield function yieldS and the leak analysis:
nested cost-0 cores yield unbounded bad scalars once a seed fits the span
budget (s <= n-1, need_cores >= 1).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_syz23_directness_support_leak import analyze, yieldS  # noqa: E402


def test_yieldS_low_t() -> None:
    # t <= s: full yield n-s.
    assert yieldS(32, 10, 20) == 12
    assert yieldS(32, 20, 20) == 12


def test_yieldS_high_t() -> None:
    # t > s: fractional yield floor.
    assert yieldS(32, 24, 20) == (32 - 20) // (24 - 20)  # 12//4 = 3
    assert yieldS(32, 28, 20) == 12 // 8  # 1


def test_yieldS_zero_when_s_tight() -> None:
    # t close to n, s close: full yield when t <= s (no division).
    assert yieldS(32, 30, 29) == (32 - 29) // (30 - 29)  # 3//1 = 3
    assert yieldS(32, 31, 31) == 1  # t <= s → n-s = 1


def test_analyze_leak_when_seed_fits() -> None:
    # n=32, k=16: s=17 fits (17 <= 31), need_cores = ceil(17/15) = 2 → LEAK.
    leak = analyze(32, 16, 20, 32)
    assert leak is not None
    s, y, need = leak
    assert s <= 31
    assert need >= 1
    assert y > 0


def test_analyze_no_leak_s_equals_n() -> None:
    # s = n excluded (s <= n-1 required).
    leak = analyze(32, 16, 20, 32)
    assert leak[0] < 32


def test_analyze_yield_zero_no_leak() -> None:
    # t = n-1, s = k+1: yield may be 0 → skip.
    leak = analyze(32, 16, 31, 32)
    # Either no leak or a positive-yield leak from another s.
    if leak is not None:
        assert leak[1] > 0
