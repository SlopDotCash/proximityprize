# Issue #466 G131: the per-rung descent series

Date: 2026-07-11 (UTC)

Generalizes the G128 series machinery from fixed rung 110 to every rung t ≤ 110
(`Frontier/_G131PerRungDescentSeries.lean`, 2 declarations, axiom-clean, 0 sorryAx):

- `descBT t q k = q·(t)_k²·n^(2t−1−k)`, the trivial-energy descent series at rung t;
- `descBT_halving`: one step deeper at least halves the series, uniformly for t ≤ 110;
- `descBT_tail`: every downward tail from the deepest term is ≤ 2× its head.

With G130's four uniform budget lemmas, the arithmetic layer of the tower is complete for
rungs 11..110. Remaining assembly (sequel): per-rung `shallow_descent_sharp` /
`full_descent_budget` analogues consuming descBT + the G130 gates, the per-rung tower step,
and the strong induction over rungs (descending 8 per step, base t₀ = 11).

CORE remains OPEN.
