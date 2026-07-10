# G78: weighted-relation embedding rigidity — the single-embedding qualifier in #505 has zero slack (2026-07-10)

Status: axiom-clean rigidity pin landed; CORE (#505 cross-orbit bound) remains OPEN.

## Claim

For any exponent `a` coprime to `n` (with the standard frame `orderOf g = n`, `n = 2m`,
`g^m = -1`), the entire weighted signed relation structure is **literally identical** at the
primitive embedding `g ↦ g^a`:

- `powerRootSet (g^a) n = powerRootSet g n` (set-level: unit dilation permutes residues mod `n`);
- `shadowCollisionMass (g^a) n m r = shadowCollisionMass g n m r`;
- `relationAnomaly (g^a) n m r = relationAnomaly g n m r`;
- `signedShadowPairDiscrepancy (g^a) n m r = signedShadowPairDiscrepancy g n m r`;
- `DCEnergyBound (powerRootSet (g^a) n) r ↔ DCEnergyBound (powerRootSet g n) r`;
- any G75-shaped budget inequality holds at `g^a` iff it holds at `g`.

## Mechanism

`powerRootSet` is an image over all residues; dilation by a unit mod `n` is a bijection on
residues, so the finset is unchanged. R312's exact subtraction identity
`shadowCollisionMass = rEnergy(powerRootSet) − shadowEnergy` expresses the weighted collision
mass through the power-root **set** and embedding-free char-0 shadow data only, so equality is
inherited by `relationAnomaly` (R366) and the signed pair form (R367). Frame transport is
elementary: `a` coprime to even `n` is odd, so `(g^a)^m = (-1)^a = -1`, and
`orderOf (g^a) = n / gcd(n,a) = n`.

## Placement relative to #505's closed refinements

- OC equidistribution pinned the **unweighted** marginal counts at every embedding and honestly
  recorded that the weighted mass was out of scope. G78 closes that seam: the **full
  NR-weighted signed mass** is embedding-rigid, not merely the marginal census.
- R384's abstract no-gain audit consumed a uniform-centered-load *hypothesis* across
  generators; G78 discharges it unconditionally at the concrete relation structure.
- Consequence for admissible routes: no primitive embedding of the same subgroup is easier
  than another. Any single-embedding first-incidence route automatically works at the Galois
  average, which G75 calibrates exactly to `DCEnergyBound`. The open content of #505 is
  confirmed to live entirely in the embedding-independent weighted cross-orbit mass.

## Honest scope

Rigidity/no-slack localization only — no bound on `relationAnomaly` is proved or implied.
This complements (does not overlap) G77's first-incidence/excess-multiplicity decomposition.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G78WeightedRelationEmbeddingRigidity.lean`
  (imports R366 + R367 only; axiom audit `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`; checked with `scripts/pg-iterate.sh`).
