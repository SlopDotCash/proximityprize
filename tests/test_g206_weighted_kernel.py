"""Unit coverage for scripts/probes/g206_weighted_kernel_injective_nogo.py.

Tests the weighted-kernel quotient-label function: it must be collision-free
(injective) at the recorded cells and reproduce the exact A_5/A_6 integers
documented in the probe header.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g206_weighted_kernel_injective_nogo import (  # noqa: E402
    CELLS,
    EXPECTED,
    quotient_labels,
)


def test_quotient_labels_injective_at_all_cells() -> None:
    for n, p in CELLS:
        labels = quotient_labels(n, p)
        assert len(labels) == n
        assert len(set(labels)) == n, f"collision at n={n} p={p}"


def test_expected_integers_match_records() -> None:
    import g56_late_alignment_probe as late

    for (n, p), expected in EXPECTED.items():
        rows = [late.row(n, p, r) for r in (5, 6)]
        actual = (rows[0]["A"], rows[1]["A"])
        assert actual == expected, f"A5/A6 mismatch at n={n} p={p}"
        assert all(row["maxW"] == 1 for row in rows)


def test_quotient_labels_zero_handling() -> None:
    # (2 - u) % p == 0 → label 0 (u = 2 mod p). For small p this may occur;
    # the label must be 0, never a negative modulo result.
    import g56_late_alignment_probe as late

    n, p = CELLS[0]
    labels = quotient_labels(n, p)
    assert all(0 <= label < p or label == 0 for label in labels)
