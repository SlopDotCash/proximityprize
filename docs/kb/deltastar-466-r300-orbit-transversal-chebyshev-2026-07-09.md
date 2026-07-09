# #466 R300 — multi-orbit transversal bound + orbit-level Chebyshev (depth-3 variance arc)

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R300OrbitTransversalDeficit.lean`
(real locked build 3344 jobs, all 3 theorems axiom-clean
`[propext, Classical.choice, Quot.sound]`).

Strengthens the r57 single-orbit capstone (`deficit_ge_orbit`) to FAMILIES of orbits, and
extracts the moment→level-set step with the `/|G|` saving:

- **`deficit_ge_orbit_family`**: for a multiplicative subgroup `G ⊆ F^×` and any finite set
  `R` of nonzero frequencies pairwise `G`-inequivalent (no `b' = a·b`, `a ∈ G`),

  ```text
  |G| · Σ_{b∈R} d(b)²  ≤  Σ_c d(c)²        (d(c) = q·rep3(c) − |G|³)
  ```

  The orbits `G·b` are pairwise disjoint (free action, cancel through `a'⁻¹·a ∈ G`), each of
  exact size `|G|`, and `d` is constant on each (r56 invariance).

- **`orbit_count_chebyshev`**: if additionally every `b ∈ R` has `|d(b)| ≥ T`, then
  `|R| · |G| · T² ≤ Σ_c d(c)²` — i.e. at most `(Σ d²)/(|G|·T²)` orbits carry a `T`-large
  period deviation.

- **`orbit_count_chebyshev_energy`**: substituting the r55 `variance_identity`,
  `|R| · |G| · T² ≤ q·(q·E₃ − |G|⁶)` — the level-set count of large Gauss periods pays only
  the DC-subtracted depth-3 energy over the `(q−1)/|G|` effective degrees of freedom.

## Why it matters / why it does not close anything

This is the standard second step of the moment method, machine-checked WITH the orbit
saving that a naive per-point Chebyshev over `F` loses (factor `|G| = n`). It converts any
future sub-Wick bound on `q·E₃ − |G|⁶` directly into a count of large-period orbits — the
consumer shape the depth-3 arc (r53–r57) was normalizing toward. It does NOT touch the wall:
the deficit itself at prize depth is still the open Paley/BGK object. CORE OPEN, ON-BGK.

## Toolchain-drift repair (operational note)

The R55/R56/R57 oleans on this checkout were toolchain-drifted (stored terms referenced
removed Mathlib instance names, e.g. `instDistribOfSemiring`; any `rw`/`unfold` through them
failed with unknown-constant errors). Fixed by rebuilding the three modules from source via
`./scripts/lake-locked.sh build` — sources compile clean under the current toolchain. The new
file also carries local re-derivations `rep3_smul_local`/`deviation_smul_local` (harmless
duplication, kept for robustness against future drift of those oleans).

Completes: r55 (variance reformulation) → r56 (G-invariance) → r57 (single orbit) →
**r300 (transversal families + Chebyshev)**.
