# δ* #466 — bulk-plus-spikes quarter-MGF consumer (2026-07-08)

## Hypothesis

R189 found the current best empirical tail target:

```text
N(T) ≤ (3/5) M exp(-T/2) + 2.
```

R190 turns that target into a Lean consumer for the named R188 residual
`DyadicQuarterMGFBound`.

## Lean artifact

File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R190BulkPlusSpikesQuarterMGF.lean`.

New residual:

```lean
def BulkPlusSpikesGridTail {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (Θ : Finset ℝ) (Cbulk Kspike : ℝ) : Prop :=
  ∀ θ ∈ Θ,
    ((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤
      Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike
```

Main consumer:

```text
staircase dominates exp(t/4)
BulkPlusSpikesGridTail s t Θ (3/5) 2
weighted envelope budget ≤ 2 |s|
------------------------------------------------
DyadicQuarterMGFBound s t
```

## Verification

```text
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R188QuarterMGFTowerConsumer
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R190BulkPlusSpikesQuarterMGF.lean
```

R190 passed the fast Lean check in 6 seconds and printed the expected axiom
audit.

## Verdict

The quarter-MGF route is now factored into two explicit proof obligations:

1. prove the dyadic bulk-plus-two survival law on the chosen half-grid;
2. discharge the pure finite weighted-budget inequality.

Together they imply `DyadicQuarterMGFBound`, which feeds R188/R185/R168 and
then the existing S11 prize bridge.
