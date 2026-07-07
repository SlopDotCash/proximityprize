#!/usr/bin/env python3
"""R17: higher even moments of the shifted thin character sums T_chi.

The r=2/quadruple-Weil lane proves a Wick-shaped fourth moment for

    T_chi(s) = sum_{x in mu_n} chi(s - x)

in the beta ~= 4 regime.  This probe asks the next question needed for the prize:
do higher moments stay Gaussian enough to approach the deep rung r ~= log p?

For corrected Problem B, pass ``--away``.  Full-line mode intentionally includes the deleted
``s=0`` and ``s in mu_n`` spikes; it is useful for diagnosing why a naive full moment fails, but
it is not the away-rung object consumed by the incidence tower.

For each cell and character order it prints

    M_r / ((2r-1)!! * p * n^r)

and the single-largest-offset lower contribution

    max_s |T_chi(s)|^(2r) / ((2r-1)!! * p * n^r)

for r = 1..rmax, using 3!!/5!!/... as the real-Gaussian Wick constant.  This is only a
normalization probe, not a theorem: complex characters have a different exact Gaussian constant,
so ratios below 1 there are expected.  Growth above 1 flags that shallow Weil control is not
enough for a deep-rung argument; max-lower ratios near the total ratio mean the moment is already
dominated by the worst offset.
"""

import argparse
import math

import numpy as np
from sympy import isprime, primitive_root


def double_factorial_odd(r):
    out = 1
    for k in range(1, 2 * r, 2):
        out *= k
    return out


def run_cell(n, p, orders, rmax, away):
    if not isprime(p) or (p - 1) % n:
        print(f"SKIP n={n} p={p}: need prime p with n | p-1")
        return
    g = primitive_root(p)
    dlog = np.zeros(p, dtype=np.int64)
    v = 1
    for k in range(p - 1):
        dlog[v] = k
        v = v * g % p
    mu = np.array([pow(g, (p - 1) // n * k, p) for k in range(n)], dtype=np.int64)
    shifts = (np.arange(p, dtype=np.int64)[:, None] - mu[None, :]) % p
    nz = shifts != 0
    dl = dlog[shifts]
    beta = math.log(p) / math.log(n)
    support = np.ones(p, dtype=bool)
    if away:
        support[0] = False
        support[mu] = False
    support_count = int(np.sum(support))
    label = "away D={0}u mu_n" if away else "full line"
    print(f"\n== n={n} p={p} beta={beta:.3f} ({label}, offsets={support_count}) ==")
    for order in orders:
        d = order if order else n
        if (p - 1) % d:
            print(f"  order-{d}: skip, d ∤ p-1")
            continue
        j = (p - 1) // d
        phase = np.exp(2j * np.pi * ((j * dl) % (p - 1)) / (p - 1)) * nz
        abs_t_all = np.abs(phase.sum(axis=1))
        abs_t = abs_t_all[support]
        support_indices = np.nonzero(support)[0]
        max_t = float(abs_t.max())
        max_norm = max_t / math.sqrt(n)
        spike_s = int(support_indices[np.argmax(abs_t)])
        print(f"  order-{d:<4} max|T|/sqrt(n)={max_norm:7.3f} at s={spike_s}")
        ratios = []
        max_lowers = []
        shares = []
        for r in range(1, rmax + 1):
            moment = float(np.sum(abs_t ** (2 * r)))
            wick = double_factorial_odd(r) * p * (n ** r)
            max_contrib = max_t ** (2 * r)
            ratios.append(moment / wick)
            max_lowers.append(max_contrib / wick)
            shares.append(max_contrib / moment if moment else 0.0)
        first_total = next((i + 1 for i, x in enumerate(ratios) if x > 1), None)
        first_max = next((i + 1 for i, x in enumerate(max_lowers) if x > 1), None)
        print("    total/Wick: " + "  ".join(f"r{r}:{ratios[r-1]:7.3f}" for r in range(1, rmax + 1)))
        print("    max/Wick:   " + "  ".join(f"r{r}:{max_lowers[r-1]:7.3f}" for r in range(1, rmax + 1)))
        print("    max share:  " + "  ".join(f"r{r}:{shares[r-1]:7.3f}" for r in range(1, rmax + 1)))
        print(f"    first total>1: {first_total or '-'}; first max-lower>1: {first_max or '-'}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rmax", type=int, default=8)
    parser.add_argument("--orders", default="2,4,0",
                        help="Comma-separated character orders; 0 means order n.")
    parser.add_argument("--away", action="store_true",
                        help="Delete offsets {0} union mu_n before measuring moments.")
    parser.add_argument("cells", nargs="*",
                        help="Cells n:p. Defaults hit beta≈4 and one lower-beta contrast.")
    args = parser.parse_args()
    orders = [int(x) for x in args.orders.split(",") if x]
    cells = args.cells or [
        "16:65537",
        "32:786433",
        "32:12289",
        "64:16777601",
    ]
    for spec in cells:
        n, p = [int(x) for x in spec.split(":")]
        run_cell(n, p, orders, args.rmax, args.away)


if __name__ == "__main__":
    main()
