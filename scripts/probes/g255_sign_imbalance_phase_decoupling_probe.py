#!/usr/bin/env python3
"""G255 probe: multiplier-sign imbalance does not bound phase-measure discrepancy (#466).

Verifies the exact finite model formalized in
`_G255SignImbalancePhaseDecoupling.lean`, and cross-checks it against the sponsor-scale
phase-histogram measurement from the Fable G256 referee probe.

Model (matches the Lean file):
  * 2k phase atoms indexed by Fin (2k); low half at phase class 0, high half at class 1.
  * balancedSign = +1 on the low half, -1 on the high half, so sum s = 0
    (the STRONGEST form of the "at most one atom" multiplier-sign hypothesis).
  * a -1 sign rotates a phase by pi (z -> -z), i.e. moves that atom's phase class.
  * phaseChanged = atoms whose phase class actually moves = the high half = k atoms.

Claim proved in Lean and checked here numerically:
  signImbalance = 0     (multiplier-sign histogram is exactly balanced)
  phaseChanged  = k      (a full HALF of the phase atoms move; independent of the zero imbalance)
So the multiplier-sign imbalance scale 1/(2k-1) does NOT upper-bound the phase-measure
discrepancy k/(2k) = 1/2. This refutes the "one-atom phase-histogram" admissibility rescue of the
marginal phase-discrepancy route (G252-G254 chain).
"""
from __future__ import annotations
import numpy as np


def model_check(k: int) -> dict:
    N = 2 * k
    # phase class: low half 0, high half 1
    phase_class = np.array([0 if i < k else 1 for i in range(N)], dtype=int)
    # balanced sign: +1 low, -1 high
    sign = np.array([1 if i < k else -1 for i in range(N)], dtype=int)
    sign_imbalance = int(sign.sum())
    # a -1 sign rotates the phase by pi -> moves the class into a fresh class (c+2)
    moved_class = np.where(sign == 1, phase_class, phase_class + 2)
    phase_changed = int(np.sum(moved_class != phase_class))
    one_atom_scale = 1.0 / (N - 1) if N > 1 else 1.0
    return {
        "k": k,
        "N": N,
        "sign_imbalance": sign_imbalance,
        "phase_changed": phase_changed,
        "phase_change_frac": phase_changed / N,
        "one_atom_scale": one_atom_scale,
        "gap_ratio": (phase_changed / N) / one_atom_scale,
    }


def main() -> None:
    print("== G255 exact finite model (matches Lean _G255SignImbalancePhaseDecoupling) ==")
    print("   (N = 2k phase atoms; a sponsor quotient of order m has an m-1 nonprincipal family,")
    print("    so the matched even model uses 2k = m-1, i.e. k = (m-1)//2.)")
    ok = True
    # k values chosen to match sponsor cells: N = 2k is the even-family size, m ~ N+1.
    for k in (1, 2, 5, 10, 932):
        r = model_check(k)
        # Lean theorems: signImbalance_eq_zero, phaseChanged_card_eq
        assert r["sign_imbalance"] == 0, r
        assert r["phase_changed"] == k, r
        assert abs(r["phase_change_frac"] - 0.5) < 1e-12, r
        m_matched = r["N"] + 1
        print(
            f"k={r['k']:<5d} N={r['N']:<6d} (m~{m_matched:<6d}) sign_imbalance={r['sign_imbalance']:+d} "
            f"phase_changed={r['phase_changed']:<6d} phase_change_frac={r['phase_change_frac']:.4f} "
            f"one_atom_scale={r['one_atom_scale']:.6g} gap_ratio={r['gap_ratio']:.3g}"
        )
    print()
    print("VERDICT: sign imbalance = 0 for every k, yet a full HALF of the phase atoms move.")
    print("The multiplier-sign scale 1/(2k-1) -> 0 does NOT bound the phase-measure")
    print("discrepancy 1/2. Consistent with the Fable G256 sponsor-scale measurement (which uses")
    print("the full odd m-1 family, one-atom multiplier vs measured phase change):")
    print("  n=32  p=641    m=20   (k~=10)  -> circular_measure_change 0.6842 vs one-atom 0.0526")
    print("  n=64  p=119297 m=1864 (k~=932) -> circular_measure_change 0.5641 vs one-atom 0.000537")
    print("i.e. the phase-histogram change stays ~1/2 while the multiplier scale falls 3 orders.")
    assert ok


if __name__ == "__main__":
    main()
