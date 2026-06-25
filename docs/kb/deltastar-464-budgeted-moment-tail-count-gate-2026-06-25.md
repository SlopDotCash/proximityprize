# Issue #464: budgeted moment tail-count gate

Date: 2026-06-25.

Status: **last-mile consumer/obstruction**, not a delta-star proof.

## Inputs Checked

- Live issue #464, whose remaining open target is still the smooth-domain proximity-gap floor.
- `_MomentTailRateGate.lean`: the atom-zero average-moment consumer and one-spike obstruction.
- `_VerticalTailSupConsumer.lean`: the atom-scale vertical tail-mass consumer.
- `_PropagationTailGate.lean`: the separate structural route where one bad atom forces a larger
  cluster.

## Verdict

A moment or average-moment bound does not become a worst-case bound just because the downstream
consumer permits a nonzero bad-scalar budget `B`.  The finite last mile only shifts the atom-scale
threshold from one bad atom to `B + 1` bad atoms:

```text
#atoms * A < (B + 1) * T^k
```

is enough to prove at most `B` atoms have score at least `T`.

Equivalently, for quotient-size `N`, a Markov/moment route that wants a `B`-bad-scalar conclusion
must prove

```text
N * A / T^k < B + 1.
```

The `B = 0` case recovers the earlier atom-zero moment gate.

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_BudgetedMomentTailCountGate.lean
```

defines the weak upper-tail count

```lean
weakTailCount (X : α -> ℝ) (T : ℝ) : ℕ
```

as the number of atoms with `T <= X a`.

This file proves:

- `weakTailCount_mul_threshold_pow_le_powMomentSum`: the weak tail contributes at least
  `weakTailCount * T^k` to the unnormalized moment.
- `weakTailCount_le_of_averageMoment_card_mul_lt_budget`: an average moment budget gives a
  `≤ B` tail count only below the `B + 1` atom scale.
- `averageMoment_budget_allows_cluster_spike`: if the budget can pay for a cluster of `B + 1`
  atoms, a finite cluster spike satisfies the same average-moment budget while violating the
  `≤ B` conclusion.
- `budgetedMomentTailCountGate`: the two-sided consumer/obstruction package.

## Consequence for #464

This closes another tempting relaxation of the moment route.  Allowing finitely many bad scalars,
as happens in MCA/list-decoding style reductions, does not remove the rate requirement.  It
replaces the one-atom gate by the explicit `B + 1` atom gate.

The obstruction theorem is deliberately finite: if a cluster of `B + 1` atoms can sit at score
`S >= T` while satisfying

```text
((B + 1) * S^k) / N <= A,
```

then the same average-moment budget is compatible with more than `B` threshold atoms.  Thus a
positive-proportion relaxation must show tail mass below `(B + 1) / N`, not merely a nontrivial
tail saving.

This is compatible with the propagation-tail gate: the only way to improve the threshold is a real
anti-spike/propagation theorem that forces every bad atom to drag a larger cluster with it.

## What New Math Would Look Like

A proof route using this gate needs one of two inputs:

- a genuinely strong high-moment or exponential-tail estimate satisfying
  `N * A < (B + 1) * T^k`; or
- a structural anti-clustering theorem that rules out the finite cluster-spike model before the
  moment consumer is applied.

Without one of those inputs, the budgeted version of Markov's inequality is still an atom-scale
argument, only with `B + 1` atoms replacing one atom.
