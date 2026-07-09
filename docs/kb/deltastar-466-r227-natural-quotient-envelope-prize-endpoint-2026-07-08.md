# R227: natural quotient envelope prize endpoint

Date: 2026-07-08

## Result

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R227NaturalQuotientEnvelopePrizeEndpoint.lean`

Main declarations:

- `NaturalQuotientEnvelope`
- `naturalQuotientEnvelope_scale_le_raw`
- `prize_sq_of_gauss_natural_quotient_tail`

The natural quotient-orbit envelope is

```text
(3/5) * (#(b ≠ 0) / |G|) * exp(-θ/2) + 2.
```

R227 proves that multiplying this by `|G|` gives the corrected raw-frequency
envelope

```text
(3/5) * #(b ≠ 0) * exp(-θ/2) + 2 * |G|.
```

It then wraps R226 so the public endpoint no longer needs a separate
`hScale` arithmetic premise.

## Remaining mathematical content

After R223-R227, the quotient-tail route is reduced to the natural analytic
claim:

```text
#{quotient orbits O : θ ≤ qSq(O)}
  ≤ (3/5) * (#(b ≠ 0) / |G|) * exp(-θ/2) + 2.
```

plus the existing staircase, weighted-grid, and moment bridge assumptions.
The raw-vs-quotient multiplicity and the envelope scaling are now Lean-clean
bookkeeping.

## Verification

Dependency build:

```bash
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R226GaussQuotientTailPrizeEndpoint
```

Focused check:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R227NaturalQuotientEnvelopePrizeEndpoint.lean
```

Result:

```text
'ArkLib.ProximityGap.Frontier.R227NaturalQuotientEnvelopePrizeEndpoint.naturalQuotientEnvelope_scale_le_raw' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R227NaturalQuotientEnvelopePrizeEndpoint.prize_sq_of_gauss_natural_quotient_tail' depends on axioms: [propext,
OK (20s)
```
