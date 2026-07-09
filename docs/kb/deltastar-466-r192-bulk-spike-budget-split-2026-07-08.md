# δ* #466 — bulk/spike budget split consumer (2026-07-08)

## Hypothesis

R191 showed that the R190 weighted budget naturally decomposes into:

```text
bulk weighted sum + spike weighted sum.
```

The infinite half-grid bulk constant for the R189 constants is about
`1.600428922910`, leaving the spike term as the clean remaining budget.

## Lean artifact

File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R192BulkSpikeBudgetSplit.lean`.

New definitions:

```lean
def BulkWeightedBudget ...
def SpikeWeightedBudget ...
```

Main theorem:

```text
BulkWeightedBudget ≤ Bbulk |s|
SpikeWeightedBudget ≤ Bspike |s|
Bbulk + Bspike ≤ 2
BulkPlusSpikesGridTail
staircase dominates exp(t/4)
------------------------------------------------
DyadicQuarterMGFBound
```

There is also a specialization to the R189 constants `(3/5)` and `2`.

## Verification

```text
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R190BulkPlusSpikesQuarterMGF
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R192BulkSpikeBudgetSplit.lean
```

R192 passed the fast Lean check in 6 seconds.

## Verdict

The quarter-MGF proof path is now split into three small targets:

1. the dyadic bulk-plus-two survival law;
2. a pure bulk geometric-series budget;
3. a spike/max budget, likely controlled by a logarithmic max bound.

This is a sharper attack surface than the original raw `MGF(1/4) ≤ 2`
residual.
