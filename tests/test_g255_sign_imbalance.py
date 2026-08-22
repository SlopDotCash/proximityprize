"""Unit coverage for scripts/probes/g255_sign_imbalance_phase_decoupling_probe.py.

Tests the exact finite model: balanced sign histogram (imbalance 0) while a
full half of phase atoms move (phase_changed = k), and the scale gap between
the one-atom multiplier scale and the observed 1/2 phase-change fraction.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g255_sign_imbalance_phase_decoupling_probe import model_check  # noqa: E402


def test_model_check_balanced_sign() -> None:
    for k in (1, 2, 5, 10, 932):
        r = model_check(k)
        assert r["sign_imbalance"] == 0
        assert r["N"] == 2 * k


def test_model_check_half_phase_changes() -> None:
    for k in (1, 2, 5, 10):
        r = model_check(k)
        assert r["phase_changed"] == k
        assert abs(r["phase_change_frac"] - 0.5) < 1e-12


def test_model_check_one_atom_scale() -> None:
    r = model_check(5)
    assert r["one_atom_scale"] == 1.0 / (10 - 1)
    assert r["gap_ratio"] > 1  # phase change exceeds the multiplier scale


def test_model_check_k1_edge() -> None:
    r = model_check(1)
    assert r["N"] == 2
    assert r["one_atom_scale"] == 1.0  # N=2 → N-1=1
    assert r["phase_changed"] == 1
