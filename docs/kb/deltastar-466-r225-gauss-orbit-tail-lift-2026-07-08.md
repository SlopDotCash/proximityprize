# R225: Gauss orbit-tail lift

Date: 2026-07-08

## Result

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225GaussOrbitTailLift.lean`

The file proves that the stability hypothesis in R224 is automatic for the
actual Gauss-period spectrum.  If `G` is a finite multiplicative subgroup and
`u ∈ G`, then multiplication by `u` permutes `G`, so

```text
η_G(u*b) = η_G(b).
```

Consequently every normalized-square superlevel set is stable under the
frequency action by `G`.

Main declarations:

- `mulClosed_of_finSubgroup`
- `normalizedSq_superlevel_stable_of_finSubgroup`
- `rawNonzeroTailLeCosetScale_of_gauss_orbit_score`

## Effect on the R220-R224 route

R224 required stable raw superlevel sets to prove the raw-to-quotient
multiplicity lift.  R225 supplies that stability for Gauss periods.  The
remaining analytic obligations are now:

1. choose a quotient score `qSq` that dominates each raw survivor on its orbit,
2. prove the quotient grid tail bound,
3. verify the scaled envelope inequality consumed by R223/R222.

The raw `+2` to raw `+2*|G|` correction is therefore fully accounted for by
formal orbit bookkeeping plus Gauss-period coset invariance.

## Verification

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225GaussOrbitTailLift.lean
```

Result:

```text
'ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift.mulClosed_of_finSubgroup' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift.normalizedSq_superlevel_stable_of_finSubgroup' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift.rawNonzeroTailLeCosetScale_of_gauss_orbit_score' depends on axioms: [propext,
OK (22s)
```
