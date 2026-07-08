# R228: natural quotient tail law endpoint

Issue: #466. Date: 2026-07-08.

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R228NaturalQuotientTailLawEndpoint.lean`
names the exact all-threshold natural quotient-orbit tail law:

```text
#{Q : theta <= qSq(Q)}
  <= (3/5) * (#(b != 0) / |G|) * exp(-theta/2) + 2.
```

It then proves two bookkeeping facts:

- `quotientGridTail_of_naturalTailLaw`: the all-threshold law immediately
  supplies the finite `QuotientNormalizedSqGridTail` certificate consumed by
  R227.
- `prize_sq_of_gauss_natural_quotient_tailLaw`: with R225/R226/R227, that
  tail law is now a direct input to the composed prize-square endpoint.

## Honest status

This does not prove the analytic tail law. It removes an adapter layer and
pinpoints the remaining content in the same form tested by
`scripts/probes/probe_r228_natural_quotient_tail_sweep.py`.

The current chain is:

```text
NaturalQuotientTailLaw
  -> QuotientNormalizedSqGridTail
  -> natural quotient envelope endpoint
  -> Gauss quotient-tail endpoint
  -> scaled-spike/nonprincipal prize-square endpoint.
```

So the next non-bookkeeping target is still the quotient-orbit survival bound
itself, not another raw-frequency counting lift.

## Verification

```text
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R227NaturalQuotientEnvelopePrizeEndpoint
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R228NaturalQuotientTailLawEndpoint.lean
```

R227 built successfully. R228 passed `pg-iterate`.
