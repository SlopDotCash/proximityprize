# R226: Gauss quotient-tail prize endpoint

Date: 2026-07-08

## Result

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R226GaussQuotientTailPrizeEndpoint.lean`

Main theorem:

- `prize_sq_of_gauss_quotient_threeFifths_plus_two_tail`

This composes:

- R223: quotient-tail certificate to scaled-spike raw endpoint,
- R224: raw-to-quotient orbit multiplicity lift,
- R225: Gauss-period superlevel stability from coset invariance.

The theorem removes the abstract `RawNonzeroTailLeCosetScale` premise from the
public prize endpoint.  For a finite multiplicative subgroup `G`, it is enough
to provide:

1. a quotient-orbit score `qSq`,
2. dominance of raw survivors by that quotient score,
3. a quotient grid-tail bound,
4. the scaled envelope inequality,
5. the existing staircase, weighted-grid, and moment bridge hypotheses.

Then the R168/S11 nonprincipal prize-square bound follows.

## Remaining mathematical content

The raw-to-quotient multiplicity correction and Gauss coset stability are now
formal bookkeeping.  The surviving analytic target is the quotient-orbit tail:

```text
#{orbits O : θ ≤ qSq(O)}
  ≤ Bq(θ),
```

with a `Bq` whose scaled form fits under

```text
(3/5) * #(b ≠ 0) * exp(-θ/2) + 2 * |G|.
```

This is the clean target suggested by the R220 quotient-vs-raw probe.

## Verification

Dependency build:

```bash
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R225GaussOrbitTailLift
```

Focused check:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R226GaussQuotientTailPrizeEndpoint.lean
```

Result:

```text
'ArkLib.ProximityGap.Frontier.R226GaussQuotientTailPrizeEndpoint.prize_sq_of_gauss_quotient_threeFifths_plus_two_tail' depends on axioms: [propext,
OK (41s)
```
