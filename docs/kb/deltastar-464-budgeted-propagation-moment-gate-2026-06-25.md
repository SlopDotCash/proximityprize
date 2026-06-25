# Issue #464: budgeted propagation-moment gate

Date: 2026-06-25.

Status: **combined last-mile gate**, not a delta-star proof.

## Inputs Checked

- Live issue #464, whose floor remains a worst-case bound over all bad scalars / far-line
  incidences.
- `_BudgetedMomentTailCountGate.lean`: an average moment budget proves only a `B`-tail-count
  statement below the `B + 1` atom scale.
- `_PropagationTailGate.lean`: a distributional tail bound becomes pointwise only if every bad atom
  forces a propagated cluster of bad atoms.
- The adjacent KB notes on budgeted moment tails and propagation-tail gates.

## Verdict

This brick combines two finite facts that were previously recorded separately:

1. A moment estimate below `(B + 1) * T^k / #atoms` proves only that at most `B` atoms cross
   threshold `T`.
2. A worst-case/sup conclusion needs an anti-spike input: every nonempty bad tail must propagate
   to at least `B + 1` bad atoms.

Together they give the exact consumer:

> moment budget + propagation cluster of size `B + 1` implies `X a < T` for every atom.

The companion obstruction is sharp: if the moment budget can pay for one full propagated cluster,
a cluster-spike model satisfies the same moment budget, propagates internally, and still has more
than `B` threshold atoms.

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_BudgetedPropagationMomentGate.lean
```

defines the threshold predicate

```lean
scoreBad (X : α -> ℝ) (T : ℝ) : α -> Prop
```

and proves:

- `badCount_scoreBad_eq_weakTailCount`: the propagation-tail `badCount` for `scoreBad` is exactly
  the budgeted moment weak-tail count.
- `forall_lt_threshold_of_budgetedMoment_and_minimumTailCard`: moment budget plus minimum bad-tail
  size `B + 1` gives `∀ a, X a < T`.
- `forall_lt_threshold_of_budgetedMoment_and_badPropagates`: relation-level propagation is enough
  to provide that minimum bad-tail size.
- `averageMoment_budget_allows_propagating_cluster_spike`: a full cluster spike is compatible with
  the same average-moment budget when the budget can pay for it.
- `budgetedPropagationMomentGate`: the two-sided consumer/obstruction package.

## Consequence for #464

The issue #464 floor problem repeatedly produces distributional or averaged vertical-Sato-Tate
statements. Those are not yet worst-case statements. Markov can turn a moment into a tail count,
but the MCA/list-decoding floor needs a pointwise control of the worst frequency / worst far-line
offset.

This gate says the missing ingredient is not another finite Markov manipulation. It is a real
anti-spike theorem for the Gauss-period / Paley-spectrum family:

> one bad frequency above the prize threshold must force a propagated cluster of many bad
> frequencies.

No such propagation theorem is proved here.  The file makes the obligation explicit and supplies a
refutation target: a singleton or small-cluster bad tail would kill any proposed propagation law.

## What New Math Would Look Like

The missing input must be structural, not another Markov inequality.  A successful route would prove
something like:

```text
if |eta_b| crosses the prize threshold, then at least B + 1 related frequencies also cross it,
```

for a relation intrinsic to the dyadic Paley / Gauss-period spectrum, and with `B + 1` large enough
to beat the available moment budget.  Equivalently, it must rule out the cluster-spike obstruction
for the actual arithmetic family.

Without that anti-spike theorem, a moment estimate remains a budgeted tail-count estimate.  It does
not become the pointwise worst-frequency statement consumed by the delta-star floor.
