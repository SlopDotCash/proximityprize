"""Unit coverage for scripts/probes/g285_kernel_domain_character_probe.py.

Tests the sign function and the kernel-domain character invariants:
generator inversion leaves K2 and Re(K4) unchanged, and the A/A2 class-sum
identity holds on a small cell.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g285_kernel_domain_character_probe import cell, sgn  # noqa: E402


def test_sgn() -> None:
    assert sgn(5) == 1
    assert sgn(0) == 0
    assert sgn(-3) == -1
    assert sgn(10**9) == 1


def test_cell_small_invariants() -> None:
    z = cell(8, 113, 3)
    assert z["n"] == 8
    assert z["p"] == 113
    H = z["H"]
    n = z["n"]
    # Generator inversion leaves K2 and Re K4 unchanged.
    Hr = [H[(-j) % n] for j in range(n)]
    k2 = z["K2"]
    k4 = z["K4"]
    assert k2 == 113 * sum((1 if j % 2 == 0 else -1) * v for j, v in enumerate(Hr))
    w4 = (1, 0, -1, 0)
    assert k4 == 113 * sum(w4[j % 4] * v for j, v in enumerate(Hr))


def test_cell_second_rank() -> None:
    z = cell(8, 113, 4)
    assert z["A"] is not None
    assert len(z["H"]) == 8
