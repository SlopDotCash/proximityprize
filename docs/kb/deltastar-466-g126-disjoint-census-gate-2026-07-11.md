# Issue #466/#505 G126: the disjoint-census gate

Date: 2026-07-11 (UTC)

Routes G125's isolation through G96's weld into the production prize hypothesis.

## Result (`Frontier/_G126DisjointCensusGate.lean`, axiom-clean, 0 sorryAx)

- `descentOverhead G r`: the explicit ℕ overhead
  `Σ_{s<r} (r)_{r−s}²·#G^{r−s}·E_s(G)`.
- `dcEnergyBound_of_disjoint_census`:
  `q·(depthFiber G r r + descentOverhead G r) ≤ q·(2r−1)!!·#G^r + #G^(2r)`
  implies `DCEnergyBound G r`.

`DCEnergyBound` at any prime is now consumable from a single census statement about
fully-disjoint equal-sum pairs; the descent overhead is a concrete number computable from
lower-rung energies. Post-counterexample this is the correct per-prime gate shape.

## Honest scope

The census hypothesis at production scale IS the wall. CORE remains OPEN.
