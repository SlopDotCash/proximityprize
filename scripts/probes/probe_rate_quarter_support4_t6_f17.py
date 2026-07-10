#!/usr/bin/env python3
"""Search RS[16,4] over F17 for large support-four t=6 strata.

The evaluation domain is F17^* in the order 1,...,16.  A candidate consists
of an offset u0 and a direction u1 supported on coordinates 0,1,2,3.  For
each candidate this script exhaustively enumerates all 17^4 degree-<4
polynomials, so every reported stratum cardinality and witness is exact.

The outer search is a deterministic seeded hill climb.  Use --verify on a
saved JSON certificate or --verify-known for the checked-in degree-eight
counterexample to rerun only the exhaustive checker.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


P = 17
N = 16
K = 4
SUPPORT = np.array([0, 1, 2, 3], dtype=np.int64)
ZEROS = np.array([i for i in range(N) if i not in SUPPORT], dtype=np.int64)

KNOWN_U0 = np.array(
    [0, 4, 12, 5, 4, 2, 8, 11, 12, 11, 6, 9, 12, 2, 1, 1], dtype=np.int64
)
KNOWN_U1 = np.array(
    [1, 12, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], dtype=np.int64
)

# Best total-bad configuration from three 40x800 searches with seeds
# 446401, 446402, and 446403.  This is evidence, not an optimality claim.
BEST_BAD_U0 = np.array(
    [15, 16, 9, 8, 1, 8, 11, 11, 5, 16, 2, 15, 12, 8, 0, 0], dtype=np.int64
)
BEST_BAD_U1 = np.array(
    [2, 13, 11, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], dtype=np.int64
)


def codewords() -> tuple[np.ndarray, np.ndarray]:
    coeffs = np.array(list(itertools.product(range(P), repeat=K)), dtype=np.int64)
    x = np.arange(1, N + 1, dtype=np.int64)
    powers = np.stack([(x**d) % P for d in range(K)], axis=0)
    values = coeffs @ powers % P
    return coeffs, values


def inverse_table() -> np.ndarray:
    inv = np.zeros(P, dtype=np.int64)
    for x in range(1, P):
        inv[x] = pow(x, P - 2, P)
    return inv


COEFFS, VALUES = codewords()
INV = inverse_table()


def score(
    u0: np.ndarray,
    u1: np.ndarray,
    details: bool = False,
    objective: str = "t6",
    threshold: int = 9,
):
    zero_agreements = np.sum(VALUES[:, ZEROS] == u0[ZEROS], axis=1)
    safe = int(np.max(zero_agreements)) < threshold
    residual = (VALUES[:, SUPPORT] - u0[SUPPORT]) % P
    ratios = residual * INV[u1[SUPPORT]] % P
    triple = (
        ((ratios[:, 0] == ratios[:, 1]) & (ratios[:, 0] == ratios[:, 2]))
        | ((ratios[:, 0] == ratios[:, 1]) & (ratios[:, 0] == ratios[:, 3]))
        | ((ratios[:, 0] == ratios[:, 2]) & (ratios[:, 0] == ratios[:, 3]))
        | ((ratios[:, 1] == ratios[:, 2]) & (ratios[:, 1] == ratios[:, 3]))
    )
    selected = np.flatnonzero((zero_agreements == 6) & triple)
    max_fiber = np.zeros(VALUES.shape[0], dtype=np.int64)
    bad_scalars = []
    for gamma in range(P):
        fiber_size = np.sum(ratios == gamma, axis=1)
        max_fiber = np.maximum(max_fiber, fiber_size)
        if np.any(zero_agreements + fiber_size >= threshold):
            bad_scalars.append(gamma)
    if not details:
        value = int(selected.size) if objective == "t6" else len(bad_scalars)
        return value, safe

    appearing = zero_agreements + max_fiber >= threshold
    appearing_strata = {
        str(t): int(np.sum(appearing & (zero_agreements == t))) for t in range(9)
    }

    witnesses = []
    for row in selected:
        trace = ZEROS[VALUES[row, ZEROS] == u0[ZEROS]].tolist()
        fibers: dict[int, list[int]] = {}
        for pos, gamma in zip(SUPPORT.tolist(), ratios[row].tolist()):
            fibers.setdefault(gamma, []).append(pos)
        heavy = {str(g): fiber for g, fiber in fibers.items() if len(fiber) >= 3}
        witnesses.append(
            {
                "coefficients": COEFFS[row].tolist(),
                "zero_trace": trace,
                "support_ratios": ratios[row].tolist(),
                "heavy_fibers": heavy,
            }
        )
    return {
        "field": P,
        "domain": list(range(1, N + 1)),
        "support": SUPPORT.tolist(),
        "u0": u0.tolist(),
        "u1": u1.tolist(),
        "zero_safe": safe,
        "max_zero_agreement": int(np.max(zero_agreements)),
        "stratum_t6_card": int(selected.size),
        "appearing_strata": appearing_strata,
        "bad_scalars": bad_scalars,
        "witnesses": witnesses,
    }


def random_candidate(rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray]:
    u0 = rng.integers(0, P, size=N, dtype=np.int64)
    u1 = np.zeros(N, dtype=np.int64)
    u1[SUPPORT] = rng.integers(1, P, size=SUPPORT.size, dtype=np.int64)
    return u0, u1


def mutate(
    u0: np.ndarray, u1: np.ndarray, rng: np.random.Generator
) -> tuple[np.ndarray, np.ndarray]:
    v0 = u0.copy()
    v1 = u1.copy()
    if rng.random() < 0.82:
        pos = int(rng.integers(0, N))
        value = int(rng.integers(0, P - 1))
        if value >= v0[pos]:
            value += 1
        v0[pos] = value
    else:
        pos = int(rng.choice(SUPPORT))
        value = int(rng.integers(1, P))
        while value == v1[pos]:
            value = int(rng.integers(1, P))
        v1[pos] = value
    return v0, v1


def search(seed: int, restarts: int, steps: int, objective: str, threshold: int):
    rng = np.random.default_rng(seed)
    best_score = -1
    best = None
    for restart in range(restarts):
        u0, u1 = random_candidate(rng)
        current, safe = score(u0, u1, objective=objective, threshold=threshold)
        if not safe:
            current = -1
        for _ in range(steps):
            v0, v1 = mutate(u0, u1, rng)
            candidate, candidate_safe = score(
                v0, v1, objective=objective, threshold=threshold
            )
            if candidate_safe and candidate >= current:
                u0, u1, current = v0, v1, candidate
            if current > best_score:
                best_score = current
                best = score(u0, u1, details=True, threshold=threshold)
                print(
                    f"seed={seed} objective={objective} restart={restart} "
                    f"best={best_score} "
                    f"maxZero={best['max_zero_agreement']}",
                    flush=True,
                )
    assert best is not None
    return best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=466406)
    parser.add_argument("--restarts", type=int, default=40)
    parser.add_argument("--steps", type=int, default=500)
    parser.add_argument("--objective", choices=("t6", "bad"), default="t6")
    parser.add_argument("--threshold", type=int, default=9)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--verify-known", action="store_true")
    parser.add_argument("--verify-best-bad", action="store_true")
    args = parser.parse_args()

    if args.verify_best_bad:
        result = score(BEST_BAD_U0, BEST_BAD_U1, details=True)
        expected = {
            "zero_safe": True,
            "max_zero_agreement": 8,
            "stratum_t6_card": 0,
            "appearing_strata": {
                "0": 0,
                "1": 0,
                "2": 0,
                "3": 0,
                "4": 0,
                "5": 4,
                "6": 0,
                "7": 0,
                "8": 1,
            },
            "bad_scalars": [0, 1, 2, 3, 4, 6, 9, 13],
        }
        for key, value in expected.items():
            if result[key] != value:
                raise SystemExit(f"best-bad certificate mismatch at {key}")
        print(json.dumps(result, indent=2, sort_keys=True))
        return

    if args.verify_known:
        result = score(KNOWN_U0, KNOWN_U1, details=True)
        expected = {
            "zero_safe": True,
            "max_zero_agreement": 6,
            "stratum_t6_card": 5,
            "appearing_strata": {
                "0": 0,
                "1": 0,
                "2": 0,
                "3": 0,
                "4": 0,
                "5": 0,
                "6": 5,
                "7": 0,
                "8": 0,
            },
            "bad_scalars": [2, 5, 10, 12, 15],
        }
        for key, value in expected.items():
            if result[key] != value:
                raise SystemExit(f"known certificate mismatch at {key}")
        print(json.dumps(result, indent=2, sort_keys=True))
        return

    if args.verify:
        saved = json.loads(args.verify.read_text())
        u0 = np.array(saved["u0"], dtype=np.int64)
        u1 = np.array(saved["u1"], dtype=np.int64)
        result = score(u0, u1, details=True)
        if result != saved:
            raise SystemExit("certificate mismatch")
        print(json.dumps(result, indent=2, sort_keys=True))
        return

    result = search(
        args.seed, args.restarts, args.steps, args.objective, args.threshold
    )
    encoded = json.dumps(result, indent=2, sort_keys=True)
    print(encoded)
    if args.output:
        args.output.write_text(encoded + "\n")


if __name__ == "__main__":
    main()
