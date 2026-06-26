# Issue #464: Johnson-Range Overhead vs Tight Production Budget

Date: 2026-06-25

Status: budget-scale guardrail; not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_JohnsonOverheadTightBudgetGate.lean`

## Point

The Johnson-range route has a positive in-tree budget theorem:

```text
ProductionJohnsonBudget.lean:
  johnsonBoundReal <= K(M) * n / q,
  K(M) = 4(M+1)^5 + 2(M+1).
```

That theorem is useful when the field is enlarged enough to absorb `K(M)`.  It is not a zero-loss
production-budget theorem at the same field size.

At the exact production target, the bad-scalar budget is `n`, so the error target is `n/q`.  A
Johnson-range bound of the form `K * n / q` proves `<= n/q` if and only if `K <= 1`.

## Lean Gate

The key theorem is:

```lean
overhead_bound_le_tightBudget_iff :
  0 < n -> 0 < q ->
  overheadJohnsonBound K n q <= tightProductionBudget n q <-> K <= 1
```

The concrete `M = 64` production cap has `K > 1`, so:

```lean
johnsonOverhead64_misses_exactBudget :
  0 < n -> 0 < q ->
  not (overheadJohnsonBound (johnsonOverhead 64 : R) n q <= tightProductionBudget n q)
```

## Consequence For #464

This separates two statements that are easy to conflate:

1. Enlarged-field Johnson reach: true under the existing `ProductionJohnsonBudget` arithmetic.
2. Zero-loss exact production budget at fixed `q`: not supplied by any theorem with multiplicative
   overhead `K > 1`.

So Hab25/BCHKS-style Johnson machinery can certify the Johnson side after paying field-size slack,
but it does not by itself prove the #464 floor at the exact `q * epsilon = n` production budget.
The remaining floor still needs a budget-sized worst-case incidence theorem, union-count collapse,
or the BGK/Paley hyperplane cancellation input.
