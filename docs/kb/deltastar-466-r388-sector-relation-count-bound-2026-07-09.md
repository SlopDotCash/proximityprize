# #466 R388 — the first quantitative sector bound: sector mass ≤ #relations × char-0 energy

## What landed (axiom-clean, real locked build 3330 jobs)

`Frontier/_R388SectorRelationCountBound.lean`, on top of the r387 sector partition:

- **`sectorRelations g n m r s`**: the realized vanishing differences of support exactly `s`;
- **`fiberMass_le_shadowEnergy`**: the collision mass carried by ONE fixed relation `z` is
  at most `shadowEnergy n m r` — pairs in the fiber are determined by either endpoint, and
  `2·NR(v)·NR(v−z) ≤ NR(v)² + NR(v−z)²` folds the fiber into two squared marginals, each a
  sub-sum of the char-0 energy;
- **`sectorMass_le_card_mul_shadowEnergy`**:
  `sectorMass s ≤ #sectorRelations(s) · shadowEnergy`;
- **`collisionMass_le_relCount_mul_shadowEnergy`**: summing the r387 partition,
  `shadowCollisionMass ≤ (Σ_s #sectorRelations(s)) · shadowEnergy`.

## What this changes

The analytic unknown of the whole moment route (the collision mass = the r331 scalar `S`)
is now bounded by a pure COUNT of realized vanishing sparse relations, times an exactly
computable char-0 constant. Chained through r331, the depth-`r` level-set count needs only
`#sectorRelations(s)` bounds — and counting vanishing sparse cyclotomic relations at a prime
is exactly what the FS annihilator/resultant-height ledger does (each relation forces
`p | Norm(z)`, `|Norm(z)| ≤ (2r)^{φ(n)}`-scale, so relation counts trade against
divisor-counting on norm heights, sector by sector, with the r371/r372 rotation-orbit law
quantizing which relations travel together).

Formal chain now: prize wall → collision mass (r312) → sector split (r387) →
**relation counts (r388)** → norm-divisor counting (FS ledger) — with each arrow
machine-checked and only the last object open at prize scale.

## Honest caveat

The fiber bound costs a factor `shadowEnergy` (Wick-scale) per relation, which is lossy
when relation fibers are thin; it is the UNION-BOUND weld, not the sharp one. Sharpening to
per-fiber mass `M(z)` (the census invariant) stays available via r313's local load. The
wall — bounding relation counts uniformly to `r ≈ ln q` at `n = 2³⁰` — remains open.
CORE OPEN, ON-BGK.
