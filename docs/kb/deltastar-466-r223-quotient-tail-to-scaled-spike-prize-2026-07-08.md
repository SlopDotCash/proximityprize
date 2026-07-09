# R223: quotient tail to scaled-spike prize endpoint

Date: 2026-07-08

## Result

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R223QuotientTailToScaledSpikePrize.lean`

The file introduces the quotient-tail interface that matches the R220 raw-vs-quotient
measurement:

- `QuotientNormalizedSqGridTail Q qSq Θ Bq`
- `RawNonzeroTailLeCosetScale ψ G σ Q qSq Θ`
- `nonzeroNormalizedSqGridTail_threeFifths_scaledTwo_of_quotient`
- `prize_sq_of_quotient_threeFifths_plus_two_tail`

The bridge is intentionally exact.  If a quotient carrier has a grid tail bound
`Bq`, if the raw nonzero tail count is at most `|G|` times the quotient tail
count, and if `|G| * Bq` fits under the corrected raw envelope

```text
(3/5) * #(b ≠ 0) * exp(-θ/2) + 2 * |G|,
```

then the R222 scaled-spike prize endpoint applies.

## Why this matters

Most probes compute one value per `μ_n`-coset because `η_b` is constant along
cosets.  R220 showed that literal raw `+2` is false, while quotient `+2` and raw
scaled `+2*|G|` survive the tested rows.  R223 is the formal bridge shape needed
to turn future quotient-coset analytic evidence into the raw R222 theorem.

It does not prove the quotient partition or the analytic quotient tail.  Those
remain the live mathematical obligations.

## Verification

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R223QuotientTailToScaledSpikePrize.lean
```

Result:

```text
'ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize.nonzeroNormalizedSqGridTail_threeFifths_scaledTwo_of_quotient' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize.prize_sq_of_quotient_threeFifths_plus_two_tail' depends on axioms: [propext,
OK (17s)
```
