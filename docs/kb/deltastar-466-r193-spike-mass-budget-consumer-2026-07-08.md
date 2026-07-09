# δ* #466 — spike-mass budget consumer (2026-07-08)

## Hypothesis

R192 split the R190 weighted budget into bulk and spike parts.  R193 sharpens
the spike side:

```text
SpikeWeightedBudget Θ δ K = K * Σ_{θ∈Θ} δ θ.
```

So the R189 spike budget is no longer a separate weighted-sum obligation.  It
is the scalar staircase-mass bound

```text
2 * Σ_{θ∈Θ} δ θ ≤ Bspike |s|.
```

This is the Lean-facing form of the R191 observation that the spike cost is
controlled by `exp(max(X)/4) / M`.

## Lean artifact

File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R193SpikeMassBudgetConsumer.lean`.

Main theorem:

```text
BulkWeightedBudget ≤ Bbulk |s|
Kspike * StaircaseMass ≤ Bspike |s|
Bbulk + Bspike ≤ 2
BulkPlusSpikesGridTail
staircase dominates exp(t/4)
------------------------------------------------
DyadicQuarterMGFBound
```

Specialized R189 theorem:

```text
2 * StaircaseMass Θ δ ≤ Bspike |s|
```

for the `(3/5)` bulk and two-spike constants.

## Verification

```text
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R192BulkSpikeBudgetSplit
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R193SpikeMassBudgetConsumer.lean
```

R193 passed the fast Lean check in 6 seconds.

## Verdict

The spike part of the quarter-MGF route is now reduced to a scalar mass/max
certificate.  The remaining analytic work is concentrated on:

1. proving the dyadic bulk-plus-two survival law;
2. proving the bulk geometric budget;
3. proving a logarithmic max/staircase-mass bound.
