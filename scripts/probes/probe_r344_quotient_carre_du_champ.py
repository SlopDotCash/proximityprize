#!/usr/bin/env python3
"""Test pointwise carré-du-champ of the H-1 quotient walk on periods."""

import numpy as np

from probe_r342_difference_quotient_walk import primitive_root
from probe_r343_beta5_quotient_energy import bsgs_many


def run(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    indicator = np.zeros(p, dtype=np.float64)
    h = 1
    H = []
    for _ in range(n):
        H.append(h)
        indicator[h] = 1.0
        h = h * pow(g, m, p) % p
    # numpy uses exp(-2 pi i bx/p); periods are real and invariant under sign.
    spectrum = np.fft.fft(indicator).real
    reps = np.empty(m, dtype=np.int64)
    x = 1
    for j in range(m):
        reps[j] = x
        x = x * g % p
    f = spectrum[reps]
    shifts = np.array([(r - 1) % p for r in H if r != 1])
    base = pow(g, n, p)
    powered = {pow(int(s), n, p) for s in shifts}
    logs = bsgs_many(base, powered, m, p)
    step = np.array([logs[pow(int(s), n, p)] for s in shifts], dtype=np.int64)
    pf = np.zeros(m)
    pf2 = np.zeros(m)
    for s in step:
        pf += np.roll(f, -int(s))
        pf2 += np.roll(f * f, -int(s))
    pf /= n - 1
    pf2 /= n - 1
    gamma = pf2 - pf * pf
    imax = int(np.argmax(np.abs(f)))
    bands = []
    for c in (0.0, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0):
        mask = f >= c * np.sqrt(n)
        bands.append(
            f"g+[{c:g}]={np.max(gamma[mask]) / n:.4f}" if np.any(mask) else f"g+[{c:g}]=empty"
        )
    print(
        f"p={p} n={n} m={m} max|f|={np.max(np.abs(f)):.6f} "
        f"maxGamma/n={np.max(gamma)/n:.6f} "
        f"GammaAtMax/n={gamma[imax]/n:.6f} minGamma={np.min(gamma):.3e} "
        + " ".join(bands)
    )


for cell in ((521, 8), (100049, 8), (1048609, 16), (16777601, 32)):
    run(*cell)
