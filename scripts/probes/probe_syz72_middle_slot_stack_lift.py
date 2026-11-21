#!/usr/bin/env python3
"""Sample actual RS stacks for the SYZ72 F_41 and F_181 middle-slot witnesses.

This joins the verified region/syzygy data to the SYZ52 stack-lift probe. The
per-stack scalar classification is exact, but the stack search is random and
finite: a result below budget is not a nonexistence proof.

Run with the repository's validation Python dependencies:
    python scripts/probes/probe_syz72_middle_slot_stack_lift.py
    python scripts/probes/probe_syz72_middle_slot_stack_lift.py --trials 100
"""

from __future__ import annotations

import argparse
from collections.abc import Sequence

from probe_syz52_witness_lift import check_profile, cores_of, lift_test
from probe_syz72_middle_band_sweep import (
    SYZ71_WITNESS,
    SYZ72_F181_WITNESS,
    certify,
    mu_domain,
)


N = 20
K = 10
REGION_SIZE = 6
TRIPLE_SIZE = 2
AGREEMENT_THRESHOLD = 2 * REGION_SIZE + TRIPLE_SIZE


def replay(witness: dict, seed: int, trials: int) -> dict:
    p = witness["p"]
    mu, _generator = mu_domain(N, p)
    if mu is None:
        raise RuntimeError(f"F_{p} has no certified order-{N} subgroup")

    supports = (witness["S_AC"], witness["S_BC"], witness["S_AB"])
    certificate = certify(p, mu, *supports)
    if not certificate["ok"]:
        raise RuntimeError(
            f"the recorded F_{p} region witness failed certification: "
            f"{certificate['reason']}"
        )

    point_to_index = {point: index for index, point in enumerate(mu)}
    if any(point not in point_to_index for support in supports for point in support):
        raise RuntimeError(f"an F_{p} support point is outside the order-{N} domain")
    indexed_supports = [
        [point_to_index[point] for point in support] for support in supports
    ]
    indexed_triple = [point_to_index[point] for point in certificate["T"]]
    cores = cores_of(*indexed_supports, indexed_triple)
    profile = check_profile(cores, N, K, REGION_SIZE, TRIPLE_SIZE)
    if profile != AGREEMENT_THRESHOLD:
        raise RuntimeError(f"unexpected lifted-core size {profile}")

    return lift_test(
        mu,
        K,
        AGREEMENT_THRESHOLD,
        p,
        cores,
        seed=seed,
        trials=trials,
    )


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=1500)
    args = parser.parse_args(argv)
    if args.trials < 1:
        parser.error("--trials must be positive")

    for label, witness, seed in (
        ("SYZ71", SYZ71_WITNESS, 72),
        ("SYZ72", SYZ72_F181_WITNESS, 18172),
    ):
        result = replay(witness, seed, args.trials)
        p = witness["p"]
        budget = N - 1
        outcome = (
            "sampled over-budget stack found"
            if result["maxbad"] > budget
            else "no over-budget stack in this sample"
        )
        print(
            f"{label} F_{p}: certified region witness; d={result['d']}; "
            f"sampled stacks={result['stacks']}; "
            f"max exact finite MCA-bad={result['maxbad']}; "
            f"max finite close={result['maxbad_raw']}; "
            f"u1-close/infinity={result['inf_close']}; "
            f"joint-set stacks={result['whole_stack_joint']}; "
            f"budget={budget}; {outcome}."
        )
    print("Search coverage is sampled only; these results prove no exhaustive absence claim.")


if __name__ == "__main__":
    main()
