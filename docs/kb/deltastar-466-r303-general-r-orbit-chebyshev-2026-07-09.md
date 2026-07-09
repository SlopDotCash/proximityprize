# #466 R303 — depth-uniform orbit Chebyshev: the r300 machinery at every moment depth r

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R303GeneralROrbitChebyshev.lean`
(real locked build 3324 jobs, all 5 theorems axiom-clean
`[propext, Classical.choice, Quot.sound]`).

R300 gave the multi-orbit transversal bound + orbit-level Chebyshev at depth 3. The moment
tower consumes depths up to `r ≈ ln q`, so the machinery must be depth-uniform. Building on
R240's general `repR` / `variance_identity`:

- **`repR_smul`**: `repR G r (a·c) = repR G r c` for `a ∈ G`, EVERY depth `r`
  (coordinatewise reindex `v ↦ a⁻¹·v` of the `Fin r → G` cube);
- **`deviationR_smul`, `sum_deviationR_zero`**: the depth-`r` deviation
  `dᵣ(c) = q·repR(c) − |G|^r` is `G`-invariant and mean-zero;
- **`deficit_ge_orbit_family`**: `|G|·Σ_{b∈R} dᵣ(b)² ≤ Σ_c dᵣ(c)²` for any pairwise
  `G`-inequivalent family `R` of nonzero frequencies;
- **`orbit_count_chebyshev(_energy)`**: `|R|·|G|·T² ≤ q·(q·Eᵣ − |G|^{2r})` when every
  `b ∈ R` has `|dᵣ(b)| ≥ T`.

## Why it matters / why it does not close anything

This completes the structural normalization arc (r55–r57 depth-3 → r300 families → r303
all depths): the moment→level-set step of the moment method now exists machine-checked, at
every depth simultaneously, WITH the `/|G|` orbit saving. Any future sub-Wick bound on the
DC-subtracted `r`-energy — at whatever depth the tower is entered — converts directly into
a count of large-period orbits via one theorem application. The wall itself (uniform sub-Wick
`Eᵣ` control to `r ≈ ln q` at `n = 2^30`) is untouched — still the open Paley/BGK object.
CORE OPEN, ON-BGK.

Arc: r55 (variance) → r56 (invariance) → r57 (single orbit) → r300 (families, depth 3) →
**r303 (depth-uniform)**.
