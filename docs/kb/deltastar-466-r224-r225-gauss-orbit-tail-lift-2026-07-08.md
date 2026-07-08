# R224/R225: Gauss orbit tail lift to quotient certificates

Date: 2026-07-08

Artifacts:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R224OrbitTailLiftToQuotientTail.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225GaussOrbitTailLift.lean`

## Result

R224 and R225 close the structural part of the quotient-tail interface used by
R224 `QuotientTailAutoCarrierPrize`.

R224 proves the abstract counting lift:

```text
raw nonzero tail count <= |G| * quotient survivor count
```

provided the raw superlevel sets are stable under multiplication by `G` and the
quotient score dominates every raw survivor on its orbit.

R225 proves the actual Gauss-period stability needed for that lift.  If `G` is a
finite multiplicative subgroup and `u ∈ G`, then multiplication by `u` permutes
`G`, so

```text
η_G(u * b) = η_G(b)
```

and the normalized-square superlevel sets are stable on multiplicative
`G`-orbits.

The final R225 theorem

```text
rawNonzeroTailLeCosetScale_of_gauss_orbit_score
```

turns a quotient-orbit score domination hypothesis into the exact
`RawNonzeroTailLeCosetScale` input consumed by the quotient-tail prize endpoint.

## Verification

Fast lanes:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R224OrbitTailLiftToQuotientTail.lean
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225GaussOrbitTailLift.lean
```

Status: passed.

## Prize status

This is structural progress, not an analytic tail proof.  The remaining content
is the quotient-orbit survival bound itself: bounding the number of orbits whose
Gauss-period normalized square exceeds the above-band threshold.
