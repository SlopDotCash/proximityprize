# Issue #464: Wasserstein smoothing atom gate

Date: 2026-06-25.

Status: **smoothed-tail consumer and obstruction**, not a delta-star proof.

## What Was Added

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WassersteinSmoothingAtomGate.lean
```

formalizes the last-mile gate for smoothing-based Wasserstein or discrepancy arguments.

It defines:

```lean
softEmpiricalAverage
```

and proves that a soft test majorizing the hard upper-tail indicator can imply a pointwise bound
only when its certified budget is below one atom:

```text
B < 1 / #alpha
```

or equivalently:

```text
#alpha * B < 1.
```

The main consumers are:

```lean
tailMass_le_softEmpiricalAverage_of_majorizes_tail
forall_le_of_softEmpiricalAverage_bound_lt_inv_card
forall_le_of_softEmpiricalAverage_bound_card_mul_lt_one
forall_le_threshold_plus_margin_of_wassersteinSmoothBudget
```

## Obstruction

The file also constructs the one-spike model for a hard cutoff:

```lean
softEmpiricalAverage_single_spike_cutoff
softBudget_allows_single_spike
softBudget_allows_single_spike_of_one_le_card_mul
atomScaleGate_for_smoothedTailCertificate
```

Thus a smoothed Wasserstein certificate with budget

```text
targetTail + transport / eta
```

is prize-facing only if

```text
#alpha * (targetTail + transport / eta) < 1.
```

At or above one-atom scale, smoothing does not exclude the single bad frequency or stack that the
MCA floor must rule out.

## Verdict

This does not prove the Paley/BGK or delta-star statement.  It rules out a common false finish:
passing from a smooth distributional estimate to a worst-case theorem without paying the atom-scale
union bound.
