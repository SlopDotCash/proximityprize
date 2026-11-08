#!/usr/bin/env python3
"""Search RS[16,4] over F17 for large support-four t=6 strata.

The evaluation domain is F17^* in the order 1,...,16.  A candidate consists
of an offset u0 and a direction u1 supported on coordinates 0,1,2,3.  For
each candidate this script exhaustively enumerates all 17^4 degree-<4
polynomials, so every reported stratum cardinality and witness is exact.

The outer search is a deterministic seeded hill climb.  Use --verify on a
saved JSON certificate or --verify-known for the checked-in degree-eight
counterexample to rerun only the exhaustive checker.

Checker preconditions (enforced, not just assumed by the search): u0 and u1
have shape (16,) with field representatives in [0, 17), and u1 is nonzero at
every support coordinate 0,1,2,3 and zero elsewhere.  Only then is a codeword's
agreement with the line at scalar gamma equal to (matches of u0 off the support)
+ (size of its gamma ratio fibre on the support); a zero direction entry would
otherwise be silently treated as ratio 0.  Invalid inputs raise ValueError.

Threshold and model: the agreement threshold (default 9, allowed 7..10) is
used consistently.  The selected "t6" stratum is the set of codewords with
exactly six off-support matches and a support ratio fibre of size at least
threshold - 6 (a three-point fibre at the default 9), so every selected
codeword reaches the threshold.  Certificates record "threshold" and "model",
and --verify recomputes at the saved threshold.  Each emitted witness is
re-checked independently (direct polynomial evaluation: agreement >= threshold
and non-jointness), and bad_scalars is cross-checked against direct
enumeration of the whole codeword table.  (Repository audit 2026-10-28, L118;
compare L110's fixed-decoder-threshold boundary.)
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
DOMAIN = list(range(1, N + 1))
MODEL = "t6"  # exactly six off-support matches + one support fibre
DEFAULT_THRESHOLD = 9


def validate_threshold(threshold: object) -> int:
    """The t6 model needs a support fibre of size 1..|SUPPORT| = threshold - 6."""
    if isinstance(threshold, bool) or not isinstance(threshold, (int, np.integer)):
        raise ValueError(f"threshold must be an integer, got {threshold!r}")
    threshold = int(threshold)
    if not 6 + 1 <= threshold <= 6 + SUPPORT.size:
        raise ValueError(
            f"threshold {threshold} outside [7, {6 + SUPPORT.size}] for the t6 model"
        )
    return threshold


def validate_candidate(u0: object, u1: object) -> tuple[np.ndarray, np.ndarray]:
    """Check shapes, field representatives and the exact support of u1."""
    arrays = []
    for name, raw in (("u0", u0), ("u1", u1)):
        arr = np.asarray(raw)
        if arr.shape != (N,):
            raise ValueError(f"{name} must have shape ({N},), got {arr.shape}")
        if arr.dtype == bool or not np.issubdtype(arr.dtype, np.integer):
            raise ValueError(f"{name} must hold integers, got dtype {arr.dtype}")
        arr = arr.astype(np.int64)
        if np.any((arr < 0) | (arr >= P)):
            raise ValueError(f"{name} entries must be field representatives in [0, {P})")
        arrays.append(arr)
    v0, v1 = arrays
    if np.any(v1[SUPPORT] == 0):
        raise ValueError("u1 must be nonzero at every support coordinate")
    if np.any(v1[ZEROS] != 0):
        raise ValueError("u1 must vanish off the support")
    return v0, v1


def evaluate(coefficients: list[int], x: int) -> int:
    """Direct Horner evaluation, independent of the precomputed VALUES table."""
    acc = 0
    for c in reversed(coefficients):
        acc = (acc * x + int(c)) % P
    return acc


def is_codeword_restriction(points: list[int], values: list[int]) -> bool:
    """Exact: does some degree-<K polynomial take values[i] at DOMAIN[points[i]]?"""
    if len(points) <= K:
        return True
    base = list(range(K))
    for t in range(K, len(points)):
        xt = DOMAIN[points[t]]
        acc = 0
        for a in base:
            num, den = 1, 1
            for b in base:
                if b != a:
                    num = num * (xt - DOMAIN[points[b]]) % P
                    den = den * (DOMAIN[points[a]] - DOMAIN[points[b]]) % P
            acc = (acc + values[a] * num * pow(den, P - 2, P)) % P
        if acc != values[t] % P:
            return False
    return True


def check_witness(
    u0: np.ndarray, u1: np.ndarray, coefficients: list[int], gamma: int, threshold: int
) -> dict:
    """Independently recompute agreement and non-jointness of one witness."""
    evals = [evaluate(coefficients, x) for x in DOMAIN]
    line = [(int(a) + gamma * int(b)) % P for a, b in zip(u0, u1)]
    agree = [i for i in range(N) if evals[i] == line[i]]
    joint = is_codeword_restriction(
        agree, [int(u0[i]) for i in agree]
    ) and is_codeword_restriction(agree, [int(u1[i]) for i in agree])
    if len(agree) < threshold or joint:
        raise AssertionError(
            f"witness {coefficients} at gamma={gamma} fails: agreement {len(agree)},"
            f" nonjoint {not joint}, threshold {threshold}"
        )
    return {"gamma": gamma, "agreement": len(agree), "nonjoint": not joint}


def direct_bad_scalars(u0: np.ndarray, u1: np.ndarray, threshold: int) -> list[int]:
    """Scalars at which some codeword agrees with the line on >= threshold points,
    by direct comparison against the full codeword table (no ratio algebra)."""
    out = []
    for gamma in range(P):
        line = (u0 + gamma * u1) % P
        if int(np.max(np.sum(VALUES == line, axis=1))) >= threshold:
            out.append(gamma)
    return out


def score(
    u0: np.ndarray,
    u1: np.ndarray,
    details: bool = False,
    objective: str = "t6",
    threshold: int = DEFAULT_THRESHOLD,
):
    u0, u1 = validate_candidate(u0, u1)
    threshold = validate_threshold(threshold)
    fibre_need = threshold - 6
    zero_agreements = np.sum(VALUES[:, ZEROS] == u0[ZEROS], axis=1)
    safe = int(np.max(zero_agreements)) < threshold
    residual = (VALUES[:, SUPPORT] - u0[SUPPORT]) % P
    # Exact: u1[SUPPORT] has no zero entries (validated above).
    ratios = residual * INV[u1[SUPPORT]] % P
    max_fiber = np.zeros(VALUES.shape[0], dtype=np.int64)
    bad_scalars = []
    for gamma in range(P):
        fiber_size = np.sum(ratios == gamma, axis=1)
        max_fiber = np.maximum(max_fiber, fiber_size)
        if np.any(zero_agreements + fiber_size >= threshold):
            bad_scalars.append(gamma)
    selected = np.flatnonzero((zero_agreements == 6) & (max_fiber >= fibre_need))
    if not details:
        value = int(selected.size) if objective == "t6" else len(bad_scalars)
        return value, safe

    if direct_bad_scalars(u0, u1, threshold) != bad_scalars:
        raise AssertionError("ratio-fibre bad scalars disagree with direct enumeration")

    appearing = zero_agreements + max_fiber >= threshold
    # Strata t = 0..threshold-1 cover every appearing codeword of a zero-safe
    # candidate (keys 0..8 at the default threshold 9, as before).
    appearing_strata = {
        str(t): int(np.sum(appearing & (zero_agreements == t)))
        for t in range(max(9, threshold))
    }

    witnesses = []
    for row in selected:
        trace = ZEROS[VALUES[row, ZEROS] == u0[ZEROS]].tolist()
        fibers: dict[int, list[int]] = {}
        for pos, gamma in zip(SUPPORT.tolist(), ratios[row].tolist()):
            fibers.setdefault(gamma, []).append(pos)
        heavy = {g: fiber for g, fiber in fibers.items() if len(fiber) >= fibre_need}
        coefficients = COEFFS[row].tolist()
        checks = [
            check_witness(u0, u1, coefficients, g, threshold) for g in sorted(heavy)
        ]
        witnesses.append(
            {
                "coefficients": coefficients,
                "zero_trace": trace,
                "support_ratios": ratios[row].tolist(),
                "heavy_fibers": {str(g): fiber for g, fiber in heavy.items()},
                "checks": checks,
            }
        )
    return {
        "field": P,
        "domain": DOMAIN,
        "support": SUPPORT.tolist(),
        "threshold": threshold,
        "model": MODEL,
        "u0": u0.tolist(),
        "u1": u1.tolist(),
        "zero_safe": safe,
        "max_zero_agreement": int(np.max(zero_agreements)),
        "stratum_t6_card": int(selected.size),
        "appearing_strata": appearing_strata,
        "bad_scalars": bad_scalars,
        "witnesses": witnesses,
    }


def verify_certificate(saved: dict) -> dict:
    """Recompute a saved certificate at its own recorded threshold and model."""
    if not isinstance(saved, dict) or "threshold" not in saved or "model" not in saved:
        raise ValueError("certificate lacks 'threshold'/'model' (pre-L118 format)")
    if saved["model"] != MODEL:
        raise ValueError(f"unsupported certificate model {saved['model']!r}")
    for key, expected in (("field", P), ("domain", DOMAIN), ("support", SUPPORT.tolist())):
        if saved.get(key) != expected:
            raise ValueError(f"certificate {key} does not match this checker")
    result = score(
        saved["u0"], saved["u1"], details=True, threshold=saved["threshold"]
    )
    if result != saved:
        raise ValueError("certificate mismatch")
    return result


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
        try:
            result = verify_certificate(saved)
        except ValueError as exc:
            raise SystemExit(str(exc)) from exc
        print(json.dumps(result, indent=2, sort_keys=True))
        return

    validate_threshold(args.threshold)
    result = search(
        args.seed, args.restarts, args.steps, args.objective, args.threshold
    )
    encoded = json.dumps(result, indent=2, sort_keys=True)
    print(encoded)
    if args.output:
        args.output.write_text(encoded + "\n")


if __name__ == "__main__":
    main()
