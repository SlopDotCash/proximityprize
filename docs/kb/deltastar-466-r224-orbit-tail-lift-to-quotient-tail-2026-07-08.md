# R224: orbit-tail lift to quotient tail

Date: 2026-07-08

## Result

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R224OrbitTailLiftToQuotientTail.lean`

The new theorem is:

- `rawNonzeroTailLeCosetScale_of_orbit_superlevels`

It proves the `RawNonzeroTailLeCosetScale` hypothesis consumed by R223 from a
standard finite-subgroup orbit partition.  Concretely, for the quotient carrier

```text
nonzeroOrbitCarrier G = image (b ↦ G · b) over b ≠ 0,
```

if every normalized-square superlevel set is stable under multiplication by
`G`, and if the quotient score `qSq (G · b)` dominates each raw survivor, then

```text
#{raw nonzero survivors at θ}
  ≤ |G| * #{quotient-orbit survivors at θ}.
```

This is the formal R220 multiplicity correction: the factor `|G|` is not an
extra analytic loss; it is the exact orbit size of the raw frequency carrier.

## Remaining mathematical content

R224 does not prove the quotient tail itself.  It reduces the next analytic
obligation to:

1. prove normalized-square superlevel stability under the actual `μ_n` action,
2. choose a quotient score constant on or dominating raw orbit representatives,
3. prove the quotient grid tail bound that R223 scales into the R222 prize
   endpoint.

## Verification

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R224OrbitTailLiftToQuotientTail.lean
```

Result:

```text
'ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail.rawNonzeroTailLeCosetScale_of_orbit_superlevels' depends on axioms: [propext,
OK (20s)
```
