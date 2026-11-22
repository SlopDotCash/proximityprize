import json
import subprocess

body = """The [weighted section](https://github.com/mashingaan/proximityprize/blob/d57248934/docs/research/proximity-gap/first-sponsor-reciprocal-locators.md) of the reciprocal-locator draft divides a sum over pairs of heads by `b(b-1)` and calls the result the mean pair-union size, and it compares a round mean surplus `4000000` against a round ledger gap `3800000`. This draft machine-checks the first step and carries the exact gap in the second.

## Mean pair-union ledger

`ArkLib/Research/ProximityGap/Frontier/_PairUnionMomentMean.lean` proves, for an arbitrary family of agreement sets:

- `sum_card_inter_eq_sum_degree_sq`: the ordered pair-intersection mass is the sum of squared agreement degrees.
- `sum_card_inter_erase_eq_sum_degree_mul_pred`: removing the diagonal leaves the falling square `M (M - 1)`.
- `ordered_pair_union_deficit`: the ordered pair-union total is `b (b-1) n` minus that falling square.
- `three_mul_sq_le` / `sum_three_mul_sq_le`: `3 q M^2 <= 2 M^3 + q^3` from `(M - q)^2 (2 M + q) >= 0`, summed against the cube budget.
- `mean_pair_union_moment`: an upper third moment `U` and a lower agreement mass `g` give `3 q (b (b-1) n - pairUnionTotal + g) <= 2 U + n q^3`.

The last inequality is exactly the `meanNum`/`denom` comparison that #842 consumes, so the mean bound `mu` stops being an assumed step. The local completion count, the sum of the local counts over pairs, and the transfer to a sponsor-facing floor remain written arguments.

## Successor radius

At `t = 223580000`, `a = 397300000`, `q = 852000000` the ledger gap per ordered triple is `3898095.9` and the mean surplus per unordered triple is `3931501.0`, so a single round bound `3900000` still separates them. `first_sponsor_weighted_locator_margins_successor` checks all eight conditions of the weighted certificate in exact integer arithmetic, including the band cap and the locator line cap.

`python3 scripts/probes/probe_weighted_locator_certificate.py --frontier` reproduces both certificates and reports the ceiling of the argument: the exact-gap comparison closes up to `t = 223591047` and fails at `223591048`, with the tangent point at its largest admissible value. The ceiling is set by the ledger gap, not by the band cap.

Candidate floors, at the same evidence class as #842: `223580001 / 2^30` with the arithmetic checked, and `223591048 / 2^30` as the exact-arithmetic limit of the same written argument. Neither is a sponsor-facing result, and the local-counting obligations are unchanged.

## Verification

- Hosted CI `Pair-union moment and weighted radius` (`.github/workflows/pair-union-moment.yml`): runs the exact-arithmetic probe and elaborates the new module, asserting that all nine `#print axioms` reports stay inside `propext`, `Classical.choice`, `Quot.sound` with no `sorryAx`.
- `Check Library File Imports`, `Check Docs Integrity`, and the existing kernel workflows run on the PR as usual.

Stacked on #842.

AI usage: generated with Codex (OpenCode harness), model `refuseless/deepseek-v4.1-flash-fast`, by an agent working under the repository owner's direction; the exact-arithmetic probe and the Lean statements were run and checked in hosted CI.
"""

out = subprocess.run(
    ["gh", "pr", "create", "--repo", "SlopDotCash/proximityprize",
     "--base", "main", "--head", "mashingaan:feat/pair-union-mean-bound",
     "--title", "Derive the pair-union mean bound and certify the successor radius",
     "--body", body],
    capture_output=True, text=True)
print(out.returncode)
print(out.stdout)
print(out.stderr[-2000:])
