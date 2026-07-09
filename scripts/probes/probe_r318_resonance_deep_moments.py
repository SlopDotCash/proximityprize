#!/usr/bin/env python3
"""#466 R318: deep DC-subtracted moments at a rational-resonance prime.

The Gauss period eta_b is constant on multiplicative cosets of mu_n.  We
enumerate one representative per coset, evaluate every period in chunks, and
use log-sum-exp to measure moments far beyond direct additive-energy census.
The reported K_r is defined by

  sum_{b != 0} |eta_b|^(2r) = p * K_r^r * (2r-1)!! * n^r.

Thus bounded K_r is exactly the exponential loss allowed by the prize-facing
DC-subtracted moment target.
"""

from __future__ import annotations

import argparse
import math

import numpy as np
import sympy as sp


def log_double_factorial_odd(r: int) -> float:
    return math.lgamma(2 * r + 1) - r * math.log(2.0) - math.lgamma(r + 1)


def logsumexp(values: np.ndarray) -> float:
    top = float(np.max(values))
    return top + math.log(float(np.exp(values - top).sum()))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--p", type=int, default=21523361)
    parser.add_argument("--depths", default="1,2,3,4,5,8,16,32,64,128")
    parser.add_argument("--chunk", type=int, default=8192)
    args = parser.parse_args()

    n, p = args.n, args.p
    if (p - 1) % n:
        raise ValueError("n must divide p-1")
    index = (p - 1) // n
    primitive = int(sp.primitive_root(p))
    subgroup_generator = pow(primitive, index, p)
    subgroup = np.fromiter(
        (pow(subgroup_generator, j, p) for j in range(n)), dtype=np.int64, count=n
    )
    representatives = np.fromiter(
        (pow(primitive, j, p) for j in range(index)), dtype=np.int64, count=index
    )

    abs_eta = np.empty(index, dtype=np.float64)
    tau = 2.0 * math.pi / p
    for start in range(0, index, args.chunk):
        reps = representatives[start : start + args.chunk]
        residues = (reps[:, None] * subgroup[None, :]) % p
        periods = np.exp(1j * tau * residues).sum(axis=1)
        abs_eta[start : start + len(reps)] = np.abs(periods)

    logs = np.log(abs_eta, where=abs_eta > 0, out=np.full_like(abs_eta, -np.inf))
    depths = [int(item) for item in args.depths.split(",")]
    print("# R318 deep moments at a rational-resonance prime")
    print(
        f"n={n} p={p} index={index} primitive={primitive} "
        f"subgroup_generator={subgroup_generator} max_eta={abs_eta.max():.12f}"
    )
    for r in depths:
        # Every nonzero frequency occurs in a coset of cardinality n.
        log_moment = math.log(n) + logsumexp(2.0 * r * logs)
        log_wick_total = math.log(p) + log_double_factorial_odd(r) + r * math.log(n)
        log_ratio = log_moment - log_wick_total
        ratio = math.exp(log_ratio) if log_ratio < 700 else math.inf
        k_eff = math.exp(log_ratio / r)
        print(f"r={r:3d} ratio={ratio:.12g} K_eff={k_eff:.12g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
