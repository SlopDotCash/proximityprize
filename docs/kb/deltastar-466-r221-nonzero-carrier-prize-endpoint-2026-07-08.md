# R221: nonzero carrier positivity for the variance-scale endpoint

Date: 2026-07-08

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R221NonzeroCarrierPrizeEndpoint.lean`

## Result

R221 removes the explicit carrier-positivity assumption from the R220 conditional prize
endpoint.

The file proves:

- `one_mem_nonzeroFreqs`: the frequency `1` belongs to `nonzeroFreqs`.
- `nonzeroFreqs_card_pos_real`: consequently
  `0 < ((nonzeroFreqs (F := F)).card : ℝ)`.
- `prize_sq_of_dcOptimized_variance_scale_autoCarrier`: the R220 squared prize
  endpoint with carrier positivity supplied internally.

The resulting theorem keeps the meaningful mathematical assumptions from R220:

- primitive additive character,
- `DCEnergyBound G k`,
- `k ≥ log |F|`,
- variance scale
  `2 * exp 1 * |G| * k ≤ (4 * log 2) * σ^2`,
- nonzero disjoint dilation witness,
- positive `σ`,
- and the downstream moment bridge.

The artificial hypothesis
`0 < ((nonzeroFreqs (F := F)).card : ℝ)` is no longer part of the public
endpoint.

## Verification

Fast lane:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R221NonzeroCarrierPrizeEndpoint.lean
```

Status: passed.

## Prize status

This is still conditional progress, not a complete proximity-prize proof. The
remaining named assumptions are the DC-energy estimate at the desired scale and
the downstream moment bridge.
