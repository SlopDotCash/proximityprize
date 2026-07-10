#!/usr/bin/env python3
"""Exact local stability test at the n=32 rate-quarter adjacent lattice.

Imports the complete multiplicity-one GS decoder from
``probe_rate_quarter_smooth_next_lattice_gs`` and reruns its exact agreement-18
census after deterministic one-coordinate perturbations of each received row.
The purpose is adversarial: the unperturbed smooth stack has 36 MCA-bad
scalars at agreement 17 but an empty list at agreement 18.  This test checks
whether a tiny deformation immediately creates a predecessor counterexample.

SymPy is required.  Every candidate returned by the imported decoder divides
the interpolation polynomial as ``Y-q(X)``, so each reported count is a
complete census, not a heuristic list search.
"""

from __future__ import annotations

import probe_rate_quarter_smooth_next_lattice_gs as base


def census(u0: list[int], u1: list[int]) -> tuple[int, int, int]:
    bad = 0
    nonempty = 0
    max_list = 0
    for gamma in range(base.P):
        word = [(a + gamma * b) % base.P for a, b in zip(u0, u1)]
        decoded = []
        for q in base.gs_candidates(word):
            support = [
                i
                for i, (x, y) in enumerate(zip(base.XS, word))
                if base.eval_poly(q, x) == y
            ]
            if len(support) < 18:
                continue
            joint = (
                base.row_is_degree_lt_k(u0, support)
                and base.row_is_degree_lt_k(u1, support)
            )
            decoded.append(joint)
        if decoded:
            nonempty += 1
            max_list = max(max_list, len(decoded))
        if any(not joint for joint in decoded):
            bad += 1
    return bad, nonempty, max_list


def perturb(row: list[int], coordinate: int, amount: int = 1) -> list[int]:
    out = row.copy()
    out[coordinate] = (out[coordinate] + amount) % base.P
    return out


def main() -> None:
    cases: list[tuple[str, list[int], list[int]]] = [
        ("original", base.U0.copy(), base.U1.copy())
    ]
    # Touch both core and hole coordinates in each row.  The selected indices
    # meet all three lifted locator blocks and the exceptional hole fibres.
    for coordinate in [0, 2, 9, 10, 12, 16]:
        cases.append(
            (f"u0[{coordinate}]+=1", perturb(base.U0, coordinate), base.U1.copy())
        )
        cases.append(
            (f"u1[{coordinate}]+=1", base.U0.copy(), perturb(base.U1, coordinate))
        )

    results = []
    for name, u0, u1 in cases:
        bad, nonempty, max_list = census(u0, u1)
        results.append(
            {
                "case": name,
                "mca_bad_count": bad,
                "scalars_with_nonempty_list": nonempty,
                "maximum_list_size": max_list,
                "length_bound_holds": bad <= base.N,
            }
        )
    assert results[0]["mca_bad_count"] == 0
    assert all(result["length_bound_holds"] for result in results)
    print({"agreement_threshold": 18, "cases": results})


if __name__ == "__main__":
    main()
