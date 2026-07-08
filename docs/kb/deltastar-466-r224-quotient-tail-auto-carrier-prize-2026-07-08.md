# R224: quotient-tail scaled-spike endpoint with automatic carrier positivity

Date: 2026-07-08

Artifacts:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R223QuotientTailToScaledSpikePrize.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R224QuotientTailAutoCarrierPrize.lean`

## Result

R224 packages the quotient-tail route into the corrected raw scaled-spike prize
endpoint without exposing the artificial carrier-positivity hypothesis.

The new theorem

```text
prize_sq_of_quotient_threeFifths_plus_two_tail_autoCarrier
```

keeps the real inputs explicit:

- an abstract quotient survival certificate,
- a raw-to-quotient counting lift,
- the scalar comparison from the quotient envelope to the raw
  `(3/5, 2 * |G|)` envelope,
- the finite staircase and weighted grid budget,
- and the downstream moment bridge.

It supplies

```text
0 < ((nonzeroFreqs (F := F)).card : ℝ)
```

internally via R221.

## Verification

Dependency build for the quotient bridge:

```bash
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223QuotientTailToScaledSpikePrize
```

Fast lane:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R224QuotientTailAutoCarrierPrize.lean
```

Status: passed.

## Prize status

This is still conditional progress.  It improves the quotient-tail interface to
the corrected scaled-spike route, but it does not prove the quotient survival
certificate or the raw-to-quotient counting lift.
