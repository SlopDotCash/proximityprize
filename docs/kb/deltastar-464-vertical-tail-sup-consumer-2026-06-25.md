# Issue #464: vertical tails must beat one atom

Date: 2026-06-25.

Status: **distributional-to-sup guardrail**, not a delta-star proof.

## What Was Formalized

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_VerticalTailSupConsumer.lean
```

formalizes the finite consumer for any vertical tail estimate.

For scores

```lean
X : alpha -> Real
```

and threshold `T`, Lean defines the strict upper-tail count and mass:

```lean
tailCount X T
tailMass X T
```

It proves:

```lean
tailCount_eq_zero_iff_forall_le
inv_card_le_tailMass_of_exists_gt
forall_le_of_tailMass_lt_inv_card
tailMass_single_spike
tailMass_budget_allows_single_score_spike
atomScaleGate_for_tailSupBound
```

## Critical Consequence

A distributional upper-tail theorem implies the pointwise bound `X a <= T` only if the tail-mass
upper bound is strictly below the mass of one atom:

```text
U < 1 / #alpha.
```

If `1 / #alpha <= U`, Lean constructs a one-score spike above threshold whose tail mass is still
within budget.

So a vertical Sato-Tate, empirical-tail, discrepancy, or Wasserstein estimate is prize-facing only
after it reaches atom scale.  Any weaker average statement remains compatible with one surviving
bad frequency.
