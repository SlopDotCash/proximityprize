# Face 1 Johnson Cap: CellPackageSupply Cannot Enter the Prize Window

**Date:** 2026-06-27  
**Issue:** #464 / #334 successor  
**Angle:** BCIKS20 section-production / `CellPackageSupply` as a character-sum-free floor route  
**Verdict:** clean no-go for this shortcut. Face 1 bypasses the Paley/BGK character-sum wall only in the
Johnson regime; it does not give an outright deployed `delta*` pin.

## Result

The new frontier brick
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/Face1JohnsonRadiusCap.lean` proves, in pure real
arithmetic, that the Guruswami-Sudan / BCIKS20 radius

```text
gs_johnson k n m = 1 - sqrt(k/n) - sqrt(k/n)/(2m)
```

is strictly below both:

- the Johnson edge `1 - sqrt(k/n)` for every finite multiplicity `m > 0`;
- the capacity edge `1 - k/n` for every nondegenerate rate `0 < k/n < 1`.

Checked theorems:

- `ArkLib.ProximityGap.Frontier.Face1JohnsonCap.gs_johnson_lt_capacity`
- `ArkLib.ProximityGap.Frontier.Face1JohnsonCap.gs_johnson_lt_one_sub_sqrt_rho`
- `ArkLib.ProximityGap.Frontier.Face1JohnsonCap.face1_radius_below_prize_window`

## Consequence

`CellPackageSupply` remains a valuable unblocked formalization target: it is combinatorial,
character-sum-free, and plugs into the existing Johnson-lane consumer chain. But even a complete
discharge only certifies goodness for radii below `gs_johnson`, whose supremum is the Johnson edge.
The deployed prize window is strictly above that edge, so this route cannot prove the desired
interior lower bracket without adding a genuinely beyond-Johnson list-decoding or incidence input.

This separates two facts that were easy to conflate:

- below Johnson, BCIKS20/Face 1 is a true Paley bypass;
- above Johnson, the open core returns as the same worst-case incidence/list-size wall tracked in
  the #464 dossier.

## Verification

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/Face1JohnsonRadiusCap.lean
```

Result: `OK (86s)`, axiom audit only reported the expected proof-irrelevance/classical axioms.
