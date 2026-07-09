# R222: nonzero scaled-spike prize endpoint

Date: 2026-07-08

## Result

Added a raw-frequency-safe endpoint for the current nonzero survival-grid route:

- `ArkLib.Data.CodingTheory.ProximityGap.Frontier._R222NonzeroScaledSpikeToPrizeEndpoint`
- theorem:
  `prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail`

The theorem specializes the R219 half-rate bulk-plus-spikes consumer to

```text
#{b ≠ 0 : θ ≤ ‖η_G(b)‖² / σ²}
  ≤ (3/5) * #(b ≠ 0) * exp(-θ/2) + 2 * |G|.
```

Together with the matching weighted grid budget, this proves the same R168/S11
nonprincipal prize-square bound.

## Why this replaces the literal raw `+2` endpoint

R220 compared quotient-coset spike budgets with raw nonzero-frequency spike
budgets.  The stress row `(n=64, p=7937)` refuted the literal raw `+2` tail
allowance, while the quotient `+2` and the raw scaled allowance both passed the
tested rows.  The corrected raw carrier therefore records the spike budget as
`2 * |G|`.

This file does not assert the analytic tail.  It provides the formal endpoint
that a quotient-to-raw lift, or an intrinsically raw proof with scaled spikes,
must feed.

## Verification

Focused dependency refresh:

```bash
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R219NonzeroBulkSpikesToPrizeEndpoint
```

Focused Lean check:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R222NonzeroScaledSpikeToPrizeEndpoint.lean
```

Result:

```text
'ArkLib.ProximityGap.Frontier.R222NonzeroScaledSpikeToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail' depends on axioms: [propext,
OK (30s)
```
