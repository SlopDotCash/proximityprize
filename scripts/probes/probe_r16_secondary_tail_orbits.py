#!/usr/bin/env python3
"""R16 B2: secondary-tail orbit census for the refuted naive away-Wick rung.

The exact diagonal lane proves ``I_H(u*s0) = I_H(s0)`` for ``u in mu_n`` when
``mu_n <= H``.  This probe uses that structure on failing/stress cells:

* group all away offsets ``s0 notin ({0} union mu_n)`` into ``mu_n``-orbits;
* verify the numeric orbit-invariance plateau;
* report the top orbit contributions to
  ``S2away / (3 q Sigma^2)``.

The point is to distinguish a missed algebraic diagonal from an extreme-value tail:
the ``p=7681, n=64, deg=8`` failure is caused by many full-size away orbits with
large but non-diagonal incidence values, not by a single forgotten ``mu_n`` coset.
"""

import argparse
import math
import numpy as np
from sympy import factorint, isprime


def primitive_root(p):
    fs = list(factorint(p - 1).keys())
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError(f"no primitive root found for p={p}")


def multiplicative_order(x, p):
    if x % p == 0:
        return 0
    order = p - 1
    for q, exponent in factorint(p - 1).items():
        for _ in range(exponent):
            candidate = order // q
            if pow(x, candidate, p) == 1:
                order = candidate
            else:
                break
    return order


def cell(p, n, deg, top):
    if not isprime(p):
        raise ValueError(f"p={p} is not prime")
    if (p - 1) % n != 0 or (p - 1) % deg != 0:
        raise ValueError(f"need n,deg | p-1; got p={p}, n={n}, deg={deg}")

    g = primitive_root(p)
    gm = pow(g, (p - 1) // n, p)
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x)
        x = x * gm % p
    muset = set(mu)

    gh = pow(g, deg, p)
    hsize = (p - 1) // deg
    hset = set()
    x = 1
    for _ in range(hsize):
        hset.add(x)
        x = x * gh % p
    if not muset <= hset:
        raise ValueError("mu_n is not contained in H for this cell")

    ind = np.zeros(p, dtype=complex)
    for x in mu:
        ind[x] = 1
    eta = np.fft.ifft(ind) * p
    h = np.array(sorted(hset))
    w = np.zeros(p, dtype=complex)
    w[h] = np.conj(eta[h])
    inc = np.fft.ifft(w) * p
    abs_inc = np.abs(inc)
    sigma = float(np.sum(np.abs(eta[h]) ** 2))

    deleted = {0} | muset
    seen = set(deleted)
    orbits = []
    max_spread = 0.0
    for s in range(1, p):
        if s in seen:
            continue
        orbit = sorted({s * u % p for u in mu})
        seen.update(orbit)
        values = abs_inc[orbit]
        spread = float(np.max(values) - np.min(values))
        max_spread = max(max_spread, spread)
        rep = min(orbit)
        value = float(np.mean(values))
        contribution = len(orbit) * value**4
        order = multiplicative_order(rep, p)
        sum2 = False
        # Cheap structural test: is the representative in mu_n + mu_n?
        for u in mu:
            if ((rep - u) % p) in muset:
                sum2 = True
                break
        orbits.append(
            {
                "rep": rep,
                "size": len(orbit),
                "value": value,
                "contribution": contribution,
                "order": order,
                "index": (p - 1) // order if order else None,
                "in_h": rep in hset,
                "in_mu_plus_mu": sum2,
            }
        )

    total = sum(o["contribution"] for o in orbits)
    wick = 3.0 * p * sigma**2
    orbits.sort(key=lambda o: o["contribution"], reverse=True)

    print(
        f"p={p} n={n} deg={deg} |H|={hsize} beta={math.log(p) / math.log(n):.3f} "
        f"orbits={len(orbits)} max_orbit_spread={max_spread:.3e}"
    )
    print(
        f"  S2away/Wick2={total / wick:.6f}  sqrtSigma={math.sqrt(sigma):.3f} "
        f"max|I|/sqrtSigma={orbits[0]['value'] / math.sqrt(sigma):.3f}"
    )
    running = 0.0
    for i, o in enumerate(orbits[:top], start=1):
        running += o["contribution"]
        print(
            f"  #{i:02d} rep={o['rep']:>8} size={o['size']:>4} "
            f"|I|={o['value']:>10.3f} |I|/sqrtSigma={o['value'] / math.sqrt(sigma):>6.3f} "
            f"share={o['contribution'] / total:>7.4f} cum/Wick={running / wick:>8.5f} "
            f"ord={o['order']:>8} idx={o['index']:>5} inH={o['in_h']} "
            f"in(mu+mu)={o['in_mu_plus_mu']}"
        )

    without_top = (total - orbits[0]["contribution"]) / wick
    needed = 0
    running = total
    for o in orbits:
        if running / wick <= 1:
            break
        running -= o["contribution"]
        needed += 1
    print(
        f"  without_top_orbit/Wick2={without_top:.6f}  "
        f"top_orbits_to_drop_below_1={needed}"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument(
        "cells",
        nargs="*",
        help="Cells as p:n:deg. Defaults include the first reproduced failure and beta=4 stress cells.",
    )
    args = parser.parse_args()

    cells = args.cells or [
        "7681:64:8",
        "65537:16:128",
        "65537:16:256",
        "1073153:32:128",
    ]
    for spec in cells:
        p, n, deg = [int(x) for x in spec.split(":")]
        try:
            cell(p, n, deg, args.top)
        except ValueError as exc:
            print(f"SKIP {spec}: {exc}")


if __name__ == "__main__":
    main()
