# Issue #464: Wasserstein smoothing gate

Date: 2026-06-25.

Status: **conversion-cost barrier**, not a delta-star proof.

## Claim Tested

The previous Wasserstein atom-scale note isolates the final finite consumer: a distributional tail
bound proves a worst-case statement only below one atom.  A natural response is to avoid hard tail
indicators and use a Lipschitz ramp, because Wasserstein distance controls Lipschitz tests.

This pass tests that response.

The standard schematic argument is:

```text
hard tail 1_{T + eta < x}
  <= soft ramp phi_eta(x)
empirical average(phi_eta)
  <= target average(phi_eta) + W1 / eta
```

The question is whether smoothing changes the last-mile threshold.  It does not.  It only replaces
the hard-tail budget `U` by the smoothed budget

```text
targetTail + transport / eta.
```

That entire quantity must still beat one atom.

## Lean Result

I added:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WassersteinSmoothingAtomGate.lean
```

The file defines:

```lean
softEmpiricalAverage (X : alpha -> Real) (phi : Real -> Real)
```

and proves the finite smoothing consumer:

```lean
tailMass_le_softEmpiricalAverage_of_majorizes_tail
forall_le_of_softEmpiricalAverage_bound_lt_inv_card
forall_le_of_softEmpiricalAverage_bound_card_mul_lt_one
forall_le_threshold_plus_margin_of_wassersteinSmoothBudget
```

The key operational theorem is:

```text
softAverage <= targetTail + transport / eta
#alpha * (targetTail + transport / eta) < 1
------------------------------------------------
forall a, X a <= T + eta
```

The converse side is also formalized:

```lean
softEmpiricalAverage_single_spike_cutoff
softBudget_allows_single_spike
softBudget_allows_single_spike_of_one_le_card_mul
atomScaleGate_for_smoothedTailCertificate
```

These construct a one-score spike compatible with a smoothed certificate whenever the soft budget is
at least one atom.  The theorem `atomScaleGate_for_smoothedTailCertificate` states the exact gate:

```text
every soft certificate with budget B forces X <= T
  iff
B < 1 / #alpha.
```

Validation:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WassersteinSmoothingAtomGate.lean
```

passed in 28 seconds.

## Critical Consequence

This identifies the precise missing inequality for Wasserstein/Katz/KU-style approaches to issue
#464.  If the empirical universe is the dilation quotient

```text
m = (p - 1) / n,
```

then a smoothed-tail proof at threshold `T + eta` must show:

```text
m * (targetTail(T, eta) + W1_error / eta) < 1.
```

The margin parameter cuts both ways.  Smaller `eta` makes the soft ramp closer to the hard
indicator, but it increases the Wasserstein error as `W1_error / eta`.  Larger `eta` improves the
transport term but weakens the final threshold from `T` to `T + eta`.

So smoothing is not a bypass of the atom-scale obstruction.  It is a tradeoff that has to be
optimized under the same one-atom gate.

## What This Refutes

The following proof shape is incomplete:

```text
Wasserstein convergence of period distributions
  -> smoothed tails converge
  -> therefore no bad period
```

The missing line is exactly:

```text
targetTail + W1_error / eta < 1 / m.
```

Without that strict inequality, the Lean theorem constructs a compatible single-spike model.  The
model is abstract; it does not assert that the actual Gauss-period spectrum is arbitrary.  It says
that the smoothed certificate alone has not ruled out the one bad representative that the MCA/list
decoding floor must exclude.

## What Would Be New Math

A winning Wasserstein route would need all of the following at once:

1. an effective vertical equidistribution theorem for the actual dyadic Gauss-period family in the
   thin `n = p^{1/4}` regime;
2. a Lipschitz or smoothed-indicator approximation whose constants are explicit at the prize
   threshold;
3. a tail computation for the target law at `T = C * sqrt(n log m)`;
4. an optimized margin `eta` making `m * (targetTail + W1 / eta) < 1`.

The fourth condition is the important audit line.  If it cannot be met, the approach remains a
distributional theorem and does not prove `WorstCaseIncidenceBounded`, `mcaConjecture`, or the
delta-star floor.

This is why the KU25 Wasserstein machinery is still useful but not yet prize-closing: it gives a
language for effective distributional convergence, while the prize needs atom-scale extreme-tail
control in a growing quotient family.
