"""Unit coverage for scripts/probes/probe_syz56_hrank_cross_witness_chain.py.

Tests the cross-witness chaining overlap math: the minimal m-fold overlap
m*t-(m-1)*n = n - m(n-t) is DECREASING in m (largest guaranteed region is
the pairwise one, m=2), and pairwise 2t-n < k throughout the rate-1/2 strip,
so no chain certifies a size->=k region.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_syz56_hrank_cross_witness_chain import thresholds  # noqa: E402


def _min_mfold_overlap(n: int, t: int, m: int) -> int:
    return m * t - (m - 1) * n


def test_mfold_overlap_decreasing_in_m() -> None:
    # For fixed n, t in the strip, deeper merges shrink the guaranteed region.
    for n in (32, 64, 128):
        for t in (n // 2 + 1, 3 * n // 4 - 1):
            overlaps = [_min_mfold_overlap(n, t, m) for m in range(2, 9)]
            assert all(overlaps[i] > overlaps[i + 1] for i in range(len(overlaps) - 1))


def test_pairwise_is_largest_region() -> None:
    for n in (32, 64, 128):
        for t in (n // 2 + 1, 3 * n // 4 - 1):
            pair = _min_mfold_overlap(n, t, 2)
            assert all(_min_mfold_overlap(n, t, m) < pair for m in range(3, 9))


def test_pairwise_below_k_in_strip() -> None:
    # k = n/2; in the strip (2t < n + k), pairwise 2t-n < k.
    for n in (32, 64, 128):
        k = n // 2
        t = 3 * n // 4 - 1  # inside the strip (2t < n+k)
        pairwise = _min_mfold_overlap(n, t, 2)
        assert pairwise < k


def test_thresholds_prints_strip_context(capsys) -> None:
    thresholds(32)
    out = capsys.readouterr().out
    assert "n=32" in out
    assert "strip" in out
