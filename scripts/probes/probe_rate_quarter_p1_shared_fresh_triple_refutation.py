#!/usr/bin/env python3
"""Certify the root-product refutation of the P1 shared-fresh residual.

The construction is uniform in the injective evaluation domain.  The finite
F_101 instance below checks every pointwise clause at manageable parameters;
the exact integer ledger then checks that the same proof applies at P1.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass


def _require(condition, detail):
    """Keep the refutation ledger and finite-model checks active under Python optimization."""
    if not condition:
        raise AssertionError(detail)


def poly_eval(coeffs: list[int], x: int, prime: int) -> int:
    value = 0
    for coefficient in reversed(coeffs):
        value = (value * x + coefficient) % prime
    return value


def poly_mul(left: list[int], right: list[int], prime: int) -> list[int]:
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % prime
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def vanishing_polynomial(roots: set[int], prime: int) -> list[int]:
    out = [1]
    for root in sorted(roots):
        out = poly_mul(out, [(-root) % prime, 1], prime)
    return out


@dataclass(frozen=True)
class Parameters:
    length: int
    dimension: int
    threshold: int

    @property
    def pair_intersection_floor(self) -> int:
        return 2 * self.threshold - self.length

    @property
    def complement(self) -> int:
        return self.length - self.threshold


def check_ledger(params: Parameters) -> dict[str, int]:
    n, k, threshold = params.length, params.dimension, params.threshold
    core = params.pair_intersection_floor
    complement = params.complement
    root_core = core - 1

    _require(0 < root_core, "root core is not positive")
    _require(root_core + 3 <= threshold, "root core plus 3 exceeds the threshold")
    _require(complement >= k, "complement is below the dimension")
    _require(core < k, "pair-intersection floor is not below the dimension")
    _require(
        root_core + 1 + complement == threshold,
        "root core plus complement does not recover the threshold",
    )
    _require(root_core < k, "root core is not below the dimension")
    _require(root_core + 1 < k, "root core plus 1 is not below the dimension")

    return {
        "N": n,
        "K": k,
        "T": threshold,
        "pair_intersection_floor": core,
        "root_core_card": root_core,
        "complement_card": complement,
        "shared_fresh_fiber_size": threshold - root_core,
        "q1_degree": root_core,
        "q0_degree": root_core + 1,
    }


def check_finite_model() -> dict[str, object]:
    prime = 101
    params = Parameters(length=32, dimension=8, threshold=18)
    ledger = check_ledger(params)
    n, threshold = params.length, params.threshold
    core = params.pair_intersection_floor

    domain = list(range(n))
    joint_set = set(range(threshold))
    root_core = set(range(core - 1))
    fiber_points = sorted(joint_set - root_core)
    exceptional = fiber_points[:3]
    complement = set(range(threshold, n))

    q1 = vanishing_polynomial({domain[i] for i in root_core}, prime)
    q0 = poly_mul([0, 1], q1, prime)
    gammas = [(-domain[i]) % prime for i in exceptional]
    received0 = [poly_eval(q0, x, prime) if i in joint_set else 0
                 for i, x in enumerate(domain)]
    received1 = [poly_eval(q1, x, prime) if i in joint_set else 0
                 for i, x in enumerate(domain)]
    witnesses = [complement | root_core | {x} for x in exceptional]

    _require(
        len(joint_set) == threshold,
        f"joint set has {len(joint_set)} points, expected {threshold}",
    )
    _require(
        len(fiber_points) == params.complement + 1,
        f"fiber has {len(fiber_points)} points, expected {params.complement + 1}",
    )
    _require(
        len(set(gammas)) == 3,
        f"expected 3 distinct gammas, got {len(set(gammas))}",
    )
    _require(
        len(q1) - 1 == core - 1 < params.dimension,
        f"q1 degree {len(q1) - 1} is not core - 1 = {core - 1} below the dimension",
    )
    _require(
        len(q0) - 1 == core < params.dimension,
        f"q0 degree {len(q0) - 1} is not core = {core} below the dimension",
    )

    for point, gamma, witness in zip(exceptional, gammas, witnesses, strict=True):
        _require(
            len(witness) == threshold,
            f"witness for {point} has size {len(witness)}, expected {threshold}",
        )
        _require(
            complement <= witness,
            f"witness for {point} misses the complement",
        )
        _require(
            point in witness,
            f"witness misses its exceptional point {point}",
        )
        _require(
            all(
                (received0[i] + gamma * received1[i]) % prime == 0
                for i in witness
            ),
            f"line does not agree with the stack on the witness for {point}",
        )
        _require(
            received1[point] != 0,
            f"q1 vanishes at the exceptional point {point}",
        )

        # Any degree-<K joint explanation agreeing on the complement has K
        # distinct zeros, hence is the zero pair.  It then fails at `point`.
        _require(
            len(complement) >= params.dimension,
            "complement does not pin a joint pair to zero",
        )

    # The same construction works for every point of J outside the root core,
    # all through any fixed coordinate in the common complement.
    all_fiber_gammas = [(-domain[i]) % prime for i in fiber_points]
    _require(
        len(set(all_fiber_gammas)) == len(fiber_points),
        "fiber gammas are not distinct",
    )
    for point, gamma in zip(fiber_points, all_fiber_gammas, strict=True):
        witness = complement | root_core | {point}
        _require(
            len(witness) == threshold,
            f"witness for {point} has size {len(witness)}, expected {threshold}",
        )
        _require(
            all(
                (received0[i] + gamma * received1[i]) % prime == 0
                for i in witness
            ),
            f"line does not agree with the stack on the witness for {point}",
        )
        _require(
            received1[point] != 0,
            f"q1 vanishes at the exceptional point {point}",
        )

    return {
        "field_order": prime,
        "parameters": ledger,
        "joint_set": sorted(joint_set),
        "root_core": sorted(root_core),
        "exceptional_points": exceptional,
        "gammas": gammas,
        "full_shared_fresh_fiber_size": len(fiber_points),
        "witness_sizes": [len(witness) for witness in witnesses],
        "q0_coefficients": q0,
        "q1_coefficients": q1,
    }


def main() -> None:
    p1 = check_ledger(
        Parameters(
            length=2**30,
            dimension=2**28,
            threshold=592_794_966,
        )
    )
    finite = check_finite_model()
    report = {
        "claim": (
            "The root-product construction refutes SharedFreshTripleFree for "
            "every injective literal-P1 evaluation domain."
        ),
        "p1": p1,
        "finite_model": finite,
        "proof_shape": {
            "joint_received_word": "eval(q0,q1) on J and zero off J",
            "polynomials": "q1=prod_{b in B}(X-dom(b)); q0=X*q1",
            "scalars": "gamma_j=-dom(x_j)",
            "witnesses": "(univ\\J) union B union {x_j}",
            "nonjointness": (
                "the complement has at least K points and pins a candidate "
                "joint pair to zero; q1(x_j) is nonzero"
            ),
        },
    }
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
    report["sha256"] = hashlib.sha256(encoded).hexdigest()
    print(json.dumps(report, indent=2, sort_keys=True))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
