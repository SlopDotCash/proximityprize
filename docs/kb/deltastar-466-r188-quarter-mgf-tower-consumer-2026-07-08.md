# δ* #466 — quarter-MGF tower consumer (2026-07-08)

## Hypothesis

R186 identified the clean empirical child residual

```text
(1/M) Σ_i exp(X_i / 4) ≤ 2.
```

R185 already proved that two such child-side budgets imply the AM-GM paired
product budget for the dyadic tower.

## Lean artifact

File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R188QuarterMGFTowerConsumer.lean`.

New named residual:

```lean
def DyadicQuarterMGFBound {ι : Type*} (s : Finset ι) (t : ι → ℝ) : Prop :=
  MGFBound s t 2 (1 / 4)
```

New consumer:

```text
parent_i ≤ left_i + right_i
DyadicQuarterMGFBound left
DyadicQuarterMGFBound right
------------------------------------------------
DyadicTailMGFBound parent
```

The file also exposes `prize_sq_of_child_quarterMGF`, which keeps the quarter
MGF hypotheses directly in the final prize-square theorem statement while
reusing the audited R168/S11 bridge.

## Verification

```text
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R168DyadicTailEnvelopeConsumer
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R188QuarterMGFTowerConsumer.lean
```

The R188 check passed in 6 seconds and printed only the standard axiom audit
dependencies.

## Verdict

The active analytic target is now a named Lean residual:

```text
DyadicQuarterMGFBound s t
```

for actual dyadic Gauss-period child spectra.  Proving it uniformly closes the
R185 tower step and feeds the R168/S11 prize route.
