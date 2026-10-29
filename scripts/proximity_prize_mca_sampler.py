#!/usr/bin/env python3
"""Sampled eps_mca prober for larger prime fields (the prize 'unhappy case' probe).

The exhaustive harness (proximity_prize_rs_experiments.py --mca) is exact but
caps at q<=11. This prober reaches q ~ 101..257 with k<=2 by vectorized
brute-force list decoding over all q^k codewords, SAMPLING worst-case-shaped
pairs instead of enumerating all pairs. It measures, per pair, the EXACT set
of bad gammas (mca event: the combined word f1+gamma*f2 is delta-close to some
codeword on a witness agreement set S, but (f1,f2) is NOT jointly explained on
that same S), and reports the max over sampled pairs as a LOWER BOUND on
eps_mca.

Pair families sampled (adversarial shapes, not just uniform):
  - uniform:        f1, f2 uniform random words
  - near_code:      f1 = codeword + e (weight ~ delta*n/2), f2 uniform
  - both_near:      f1, f2 both codeword + small error
  - aligned_error:  f1 = c1 + e, f2 = c2 + e' with e, e' supported on the SAME
                    coordinate set (the S-minus-S' trap shape from the formal
                    obstruction mcaEvent_witness_eq_combined_of_jointProximity_udr)
  - rank_one:       f2 = scalar * f1 + codeword (degenerate direction)

Scope: lower-bound evidence only (sampling cannot certify a max). Exact joint
explanation check: S determines the degree<k interpolant of f|S when |S| >= k;
the pair is jointly explained on S iff each of f1|S, f2|S extends to a
codeword that AGREES WITH f ON ALL OF S (interpolate on the first k points of
S, then verify on the rest of S).

This is regression/falsification evidence for the prize conjectures, not
asymptotic proof.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from pathlib import Path

import numpy as np


def validate_parameters(q: int, n: int, k: int, pairs_per_family: int | None = None) -> None:
    """Require the prime-field RS model before allocating or reporting samples."""
    if q < 2 or any(q % divisor == 0 for divisor in range(2, math.isqrt(q) + 1)):
        raise ValueError("q must be prime; integer arithmetic modulo q is not an extension field")
    if not 1 <= k <= n <= q:
        raise ValueError("require 1 <= k <= n <= q for an injective RS evaluation domain")
    if pairs_per_family is not None and pairs_per_family <= 0:
        raise ValueError("pairs-per-family must be positive to report a sampled lower bound")


def vandermonde_codewords(q: int, n: int, k: int) -> np.ndarray:
    """All q^k RS codewords as a (q^k, n) int array, domain = 0..n-1."""
    validate_parameters(q, n, k)
    xs = np.arange(n) % q
    powers = np.stack([pow_mat(xs, j, q) for j in range(k)], axis=0)  # (k, n)
    coeffs = np.indices((q,) * k).reshape(k, -1).T  # (q^k, k)
    return (coeffs @ powers) % q


def pow_mat(xs: np.ndarray, j: int, q: int) -> np.ndarray:
    out = np.ones_like(xs)
    for _ in range(j):
        out = (out * xs) % q
    return out


def interpolate_check(f: np.ndarray, S: np.ndarray, k: int, q: int) -> bool:
    """Is f|S the restriction of a degree<k polynomial? (|S| >= k assumed)."""
    pts = S[:k]
    # Lagrange interpolation over F_q at points pts with values f[pts]
    # then verify on the remaining coordinates of S.
    poly = np.zeros(k, dtype=np.int64)
    for i, xi in enumerate(pts):
        # basis polynomial l_i with l_i(xj)=delta_ij, expanded coefficients
        num = np.array([1], dtype=np.int64)
        denom = 1
        for j2, xj in enumerate(pts):
            if j2 == i:
                continue
            num = np.convolve(num, np.array([-xj % q, 1], dtype=np.int64)) % q
            denom = (denom * (xi - xj)) % q
        inv = pow(int(denom % q), q - 2, q)
        contrib = (num * (int(f[xi]) * inv % q)) % q
        poly[: len(contrib)] = (poly[: len(contrib)] + contrib) % q
    xs = S
    vals = np.zeros(len(S), dtype=np.int64)
    for j, c in enumerate(poly):
        vals = (vals + int(c) * pow_mat(xs, j, q)) % q
    return bool(np.all(vals == f[S]))


def bad_gammas_for_pair(
    f1: np.ndarray, f2: np.ndarray, C: np.ndarray, q: int, n: int, k: int, radius: int
) -> int:
    """Exact count of gammas where the mca bad event fires for (f1, f2)."""
    validate_parameters(q, n, k)
    if not 0 <= radius <= n:
        raise ValueError("radius must be between zero and n")
    bad = 0
    for gamma in range(q):
        w = (f1 + gamma * f2) % q
        dists = (C != w[None, :]).sum(axis=1)
        close_idx = np.nonzero(dists <= radius)[0]
        is_bad = False
        for ci in close_idx:
            S = np.nonzero(C[ci] == w)[0]
            if len(S) < k:
                continue
            # jointly explained on S?
            if not (interpolate_check(f1, S, k, q) and interpolate_check(f2, S, k, q)):
                is_bad = True
                break
        if is_bad:
            bad += 1
    return bad


def sample_pair(family: str, C: np.ndarray, q: int, n: int, radius: int, rng: random.Random):
    def rand_word():
        return np.array([rng.randrange(q) for _ in range(n)], dtype=np.int64)

    def rand_codeword():
        return C[rng.randrange(len(C))].copy()

    def err(weight: int, support=None):
        e = np.zeros(n, dtype=np.int64)
        sup = support if support is not None else rng.sample(range(n), weight)
        for i in sup:
            e[i] = rng.randrange(1, q)
        return e, sup

    w = max(1, radius // 2)
    if family == "uniform":
        return rand_word(), rand_word()
    if family == "near_code":
        e, _ = err(w)
        return (rand_codeword() + e) % q, rand_word()
    if family == "both_near":
        e1, _ = err(w)
        e2, _ = err(w)
        return (rand_codeword() + e1) % q, (rand_codeword() + e2) % q
    if family == "aligned_error":
        e1, sup = err(w)
        e2, _ = err(w, support=sup)
        return (rand_codeword() + e1) % q, (rand_codeword() + e2) % q
    if family == "rank_one":
        f1 = (rand_codeword() + err(w)[0]) % q
        return f1, (rng.randrange(q) * f1 + rand_codeword()) % q
    raise ValueError(family)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=101)
    ap.add_argument("--n", type=int, default=12)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--pairs-per-family", type=int, default=40)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="reports/proximity-prize-mca-sampled.json")
    args = ap.parse_args()

    q, n, k = args.q, args.n, args.k
    try:
        validate_parameters(q, n, k, args.pairs_per_family)
    except ValueError as error:
        ap.error(str(error))
    rng = random.Random(args.seed)
    C = vandermonde_codewords(q, n, k)
    rate = k / n
    regimes = {
        "udr": (1 - rate) / 2,
        "johnson": 1 - math.sqrt(rate),
        "capacity_minus": 1 - rate - 0.05,
    }
    families = ["uniform", "near_code", "both_near", "aligned_error", "rank_one"]
    rows = []
    for regime, delta in regimes.items():
        radius = math.floor(delta * n)
        if radius < 1:
            continue
        worst = {"bad": -1}
        hist: dict[str, int] = {}
        for family in families:
            for _ in range(args.pairs_per_family):
                f1, f2 = sample_pair(family, C, q, n, radius, rng)
                bad = bad_gammas_for_pair(f1, f2, C, q, n, k, radius)
                hist[str(bad)] = hist.get(str(bad), 0) + 1
                if bad > worst["bad"]:
                    worst = {"bad": bad, "family": family, "f1": f1.tolist(), "f2": f2.tolist()}
        rows.append(
            {
                "regime": regime,
                "delta": delta,
                "radius": radius,
                "eps_mca_lower_bound": worst["bad"] / q,
                "worst": worst,
                "bad_histogram": dict(sorted(hist.items(), key=lambda x: int(x[0]))),
                "n_over_q": n / q,
                "one_over_q": 1 / q,
                "conjectured_shape": "poly(m,1/rho)/q",
            }
        )
        print(f"q={q} n={n} k={k} {regime}: eps_mca >= {worst['bad']}/{q} = {worst['bad']/q:.4f}  (n/q={n/q:.4f})")
    report = {
        "kind": "sampled_eps_mca_lower_bounds",
        "scope": "sampling_lower_bound_only_not_exhaustive_not_asymptotic",
        "q": q, "n": n, "k": k, "rate": rate,
        "pairs_per_family": args.pairs_per_family, "families": families,
        "rows": rows,
    }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
