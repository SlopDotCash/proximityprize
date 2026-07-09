# #466 R308 — the depth-uniform shadow dichotomy: E_r = char-0 shadow energy + collision mass, machine-checked at every depth

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R308DepthUniformShadowFloor.lean`
(axiom-clean). Generalizes r306/r307 from triples to `r`-tuples uniformly:

- `gsumR_eq_evalVec_tupleVec`: the field-level `r`-sum factors through the exact `ℤ[ζ]`
  shadow (`Φ_n = x^m+1` signed basis, coordinates bounded by `r`);
- `repRF_eq_sum_NR`: depth-`r` representation counts = pushforward of the char-0
  `r`-histogram;
- `shadowR_energy_le_depthR_energy`: the depth-`r` char-0 floor, every field, every `g`
  with `g^m = −1`, every `r`;
- `depthR_energy_eq_of_shadow_injective`: shadow injectivity at depth `r` ⟹ exact char-0
  energy (zero collision mass).

## The formal isolation of the core

For every depth `r` simultaneously, machine-checked:

```text
E_r(p, n)  =  (char-0 shadow energy at depth r)  +  (collision mass ≥ 0)
```

- The char-0 term is pure combinatorics (the #464 char-0 chain bounds it by Wick).
- The collision mass at depth `r` counts pairs of distinct height-≤`r` vectors in
  `ℤ^{n/2}` that collide under evaluation mod p — equivalently, SPARSE (support ≤ 2r)
  SMALL-HEIGHT (coords ≤ 2r) vanishing relations of n-th roots of unity mod p, weighted by
  the census pair-mass M(z).
- The prize wall, in this frame: show the collision mass stays sub-Wick to `r ≈ ln q` at
  `n = 2³⁰` for the chosen prime family — i.e. the chosen p admits no heavy sparse
  small-height cyclotomic relation web. This matches the dossier's "short ±1-relations of
  `2^μ`-th roots mod the prize prime" formulation of face 3, now with BOTH directions of
  the reduction machine-checked and the weight (M(z)) exactly identified.

## Honesty note

No wall contact: the isolation is exact but the collision-mass control at prize scale is
the same open Paley/BGK object. What is new: the frame is now END-TO-END formal (floor +
equality + census invariant), so any future sparse-relation non-existence result for a
concrete prime family plugs into Lean theorems that already exist, at every depth at once.
CORE OPEN, ON-BGK.
