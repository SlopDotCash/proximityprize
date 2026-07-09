# #466 R304: orbit Chebyshev consumes the DC-energy wall

Date: 2026-07-09

## What landed

`Frontier/_R304OrbitChebyshevDCEnergyConsumer.lean` composes the R303
depth-uniform orbit Chebyshev theorem with R240's constant-`K`
`DCEnergyBoundWithConstant` interface.

The main theorem is:

```text
orbit_count_chebyshev_of_dcEnergyBoundWithConstant
```

If a depth-`r` constant-`K` DC-energy bound holds, then every pairwise
`G`-inequivalent family `R` of nonzero frequencies with
`|d_r(b)| >= T` satisfies:

```text
|R| * |G| * T^2
  <= q^2 * K^r * (2r-1)!! * |G|^r.
```

It also exposes wall, bounded-depth, and ceiling-depth consumers:

```text
orbit_count_chebyshev_of_dcEnergyWallWithConstant
orbit_count_chebyshev_of_dcEnergyWallWithConstantUpTo
orbit_count_chebyshev_of_dcEnergyCeilWallWithConstant
```

## Meaning

This is not a new analytic estimate.  It is the checked downstream consumer:
any future proof of the DC-subtracted Wick wall immediately gives a large-orbit
count with the `/|G|` orbit saving at arbitrary depth, including the
moment-optimal ceiling depth.

## Validation

Passed:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R304OrbitChebyshevDCEnergyConsumer.lean
```
