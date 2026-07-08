# R223: scaled-spike endpoint with automatic carrier positivity

Date: 2026-07-08

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R223ScaledSpikeAutoCarrierEndpoint.lean`

## Result

R223 composes the two latest endpoint cleanups:

- R222: the raw nonzero-frequency spike route must use the quotient-safe scaled
  spike allowance `+ 2 * |G|`, not the refuted literal raw `+2`.
- R221: the nonzero-frequency carrier is automatically nonempty, since it
  contains `1`.

The new theorem

```text
prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail_autoCarrier
```

therefore exposes the corrected raw `(3/5, 2 * |G|)` grid-tail endpoint without
requiring downstream users to pass

```text
hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ)
```

as an explicit hypothesis.

## Verification

Fast lane:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R223ScaledSpikeAutoCarrierEndpoint.lean
```

Status: passed.

## Prize status

This is conditional progress.  It removes one artificial public assumption from
the corrected scaled-spike route, but it does not prove the analytic survival
tail, DC-energy bound, or downstream moment bridge needed to close the prize.
