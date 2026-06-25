# Issue #464: Wasserstein outlier-amplitude gate

Date: 2026-06-25.

Status: **finite last-mile obstruction**, not a delta-star proof.

## Inputs Checked

- Live issue #464, where the floor is a worst-case Gauss-period / far-line incidence bound.
- `_WassersteinAtomScaleBarrier.lean` and `_WassersteinSmoothingAtomGate.lean`, which record the
  atom-mass obstruction for distributional smoothing.
- The recent budgeted moment and propagation gates, which show the same finite last-mile pattern
  for moment tails.

## Verdict

Wasserstein/effective-equidistribution input has a second finite last-mile obstruction beyond
tail mass.  A `W1`-style average transport error can hide one outlier whose height is the atom
count times the average error.

The Lean gate proves:

```text
#atoms * W < T
```

is enough to convert a nonnegative mean-transport-to-zero bound `mean(X) <= W` into the pointwise
bound `X a < T` for every atom.

The obstruction is sharp.  A one-outlier profile of height `H` has average transport exactly

```text
H / #atoms.
```

So whenever `H <= #atoms * W`, a profile with one atom above threshold is still compatible with
the same average transport budget.

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WassersteinOutlierAmplitudeGate.lean
```

defines

```lean
meanTransportToZero (X : α -> ℝ) : ℝ
```

as the uniform average of nonnegative scores.  It proves:

- `forall_lt_of_meanTransport_card_mul_lt`: if `#α * W < T`, then
  `meanTransportToZero X <= W` implies `∀ a, X a < T`.
- `meanTransport_oneOutlier`: a one-outlier profile of height `H` has mean transport `H / #α`.
- `meanTransport_budget_allows_oneOutlier_of_height_le_card_mul`: if `H <= #α * W` and `H > T`,
  the average budget permits a threshold violation.
- `wassersteinOutlierAmplitudeGate`: the two-sided consumer/obstruction package.

## Consequence for #464

This is the finite reason a KU/Katz/Wasserstein route cannot stop at a bulk distributional
convergence rate.  The prize asks for the worst Gauss period / worst far-line offset.  A W1 theorem
that moves only the empirical distribution can miss one exceptional frequency unless its error is
small enough after multiplication by the quotient atom count.

This does not refute Wasserstein machinery as a language for vertical Sato-Tate.  It states the
rate it must deliver before it can imply the Paley/far-line worst-case bound.

## What New Math Would Look Like

The missing input must beat the outlier-amplitude scale:

```text
#quotient-atoms * W < prize threshold.
```

Alternatively, a proof must add structure showing that Wasserstein transport cannot concentrate on
one exceptional frequency for the actual Paley/Gauss-period family.  That would be an anti-outlier
theorem, not a generic property of `W1` distance.

Until one of those inputs is supplied, a bulk transport estimate remains compatible with a single
bad frequency of height `#atoms * W`.
