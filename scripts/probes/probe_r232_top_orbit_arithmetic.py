#!/usr/bin/env python3
"""#466 R232: arithmetic indices of top quotient spikes.

R230 showed that direct MGF failures are carried by a few high-ranked quotient
orbits.  The vectorized quotient enumeration uses representatives

    1, g, g^2, ..., g^(M-1),      M = (p - 1) / n,

where `g` is a primitive root modulo `p`; modulo the subgroup of order `n`,
the index `j` is a coordinate in the quotient group of order `M`.

This probe prints arithmetic data for the top spike indices `j`: gcd with
`M`, quotient order, and contribution to the quarter-MGF.  It tests whether
the bad spikes are low-order quotient characters or a more delicate resonance.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    factor,
    normalized_values_vectorized,
)


DEFAULT_CASES: tuple[tuple[int, int, str], ...] = (
    (64, 7937, "bad-M124"),
    (64, 48449, "bad-M757"),
    (64, 63361, "bad-M990"),
    (64, 65537, "bad-M1024"),
    (64, 204353, "bad-M3193"),
    (128, 65537, "bad-n128-M512"),
    (64, 65921, "near-pass-M1030"),
    (64, 259201, "env-fail-mgf-pass-M4050"),
    (64, 421313, "env-fail-mgf-pass-M6583"),
    (64, 16778497, "large-anchor"),
)


def local_ratio(j: int, m: int) -> str:
    """Return a small-denominator hint for j/M when it is exact-ish."""
    best = None
    for q in range(1, 33):
        a = round(j * q / m)
        err = abs(j / m - a / q)
        cand = (err, a, q)
        if best is None or cand < best:
            best = cand
    assert best is not None
    err, a, q = best
    return f"{a}/{q} err={err:.3g}"


def print_case(n: int, p: int, label: str, top: int, chunk: int) -> None:
    xs = normalized_values_vectorized(p, n, chunk)
    m = len(xs)
    weights = np.exp(xs / 4.0)
    order = np.argsort(xs)[::-1]
    mgf = float(weights.mean())
    print(f"\ncase {label}: n={n} p={p} M={m} factors(M)={factor(m)} mgf={mgf:.6f} maxX={float(xs[order[0]]):.6f}")
    print("rank j       j/M        gcd    qord   mirror  X          contrib   cum      ratio_hint")
    print("-" * 112)
    cum = 0.0
    for rank, idx0 in enumerate(order[:top], start=1):
        j = int(idx0)
        x = float(xs[j])
        contrib = float(weights[j] / m)
        cum += contrib
        g = math.gcd(j, m)
        qord = 1 if j == 0 else m // g
        mirror = min(j, (-j) % m)
        print(
            f"{rank:<4d} {j:<7d} {j/m:<10.6f} {g:<6d} {qord:<6d} {mirror:<7d} "
            f"{x:<10.6f} {contrib:<9.6f} {cum:<8.6f} {local_ratio(j, m)}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=16)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--case", action="append", default=[], help="extra case as n:p:label")
    args = parser.parse_args()

    cases = list(DEFAULT_CASES)
    for spec in args.case:
        n_s, p_s, label = spec.split(":", 2)
        cases.append((int(n_s), int(p_s), label))
    for n, p, label in cases:
        print_case(n, p, label, args.top, args.chunk)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(130)
