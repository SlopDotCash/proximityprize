"""Unit coverage for scripts/probes/g209_tail_floor_partition_engine.py.

Tests the pure-N extremal engine: min Σk² over partitions of n-1 into at
most n/2 parts equals 2n-3 (tight witness [2,...,2,1]), and the pointwise
k² >= 3k-2 identity.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g209_tail_floor_partition_engine import check, min_sumsq  # noqa: E402


def test_min_sumsq_small() -> None:
    best, part = min_sumsq(5, 3)
    assert sum(part) == 5
    assert len(part) <= 3
    assert best == sum(k * k for k in part)


def test_min_sumsq_flat_is_minimal() -> None:
    # total=7, tmax=4: flat partitions minimize; try all partitions.
    import itertools


    best, part = min_sumsq(7, 4)
    assert best == 2 * 2 + 2 * 2 + 2 * 2 + 1  # [2,2,2,1] = 13


def test_min_sumsq_tightness_vs_brute_force() -> None:
    def brute(total, tmax):
        best = None
        for t in range(1, tmax + 1):
            if t > total:
                break
            # Enumerate compositions of total into t positive parts.
            for parts in _compositions(total, t):
                s = sum(k * k for k in parts)
                if best is None or s < best:
                    best = s
        return best

    def _compositions(n, t):
        if t == 1:
            yield [n]
            return
        for first in range(1, n - t + 2):
            for rest in _compositions(n - first, t - 1):
                yield [first] + rest

    for total in range(2, 10):
        for tmax in range(1, total + 1):
            best, _ = min_sumsq(total, tmax)
            assert best == brute(total, tmax), (total, tmax, best)


def test_check_identity_holds() -> None:
    for n in (4, 8, 16, 32, 64):
        r = check(n)
        assert r["match"]
        assert r["witness_tight"]
        assert r["min_sumsq"] == 2 * n - 3
        assert r["engine"] == 2 * n - 3


def test_pointwise_inequality() -> None:
    for k in range(1, 20):
        assert k * k >= 3 * k - 2
        if k in (1, 2):
            assert k * k == 3 * k - 2
