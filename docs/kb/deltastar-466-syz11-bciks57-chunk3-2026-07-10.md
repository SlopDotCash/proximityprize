# SYZ11: BCIKS20 Claim 5.7 program — Chunk 3 (grading + Y-root) + composition assembly (2026-07-10)

## What landed

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ11BCIKS57Chunk3.lean`
(namespace `BCIKS20.CellPencilJohnson.SYZ11`), axiom-clean.

Continues the SYZ10 chunk plan discharging the strictly-smaller Johnson-lane residual
`CellPackageSupplyDiscLocus` (`Frontier/_SYZ8CellPackageSupply.lean`). This file:

1. Defines the five chunk-output interface structures partitioning the `DiscLocusCellData`
   fields, each parameterized by the prior chunk's output so they compose:
   `PlaceCurveSupply` (C2), `GradedYRootSupply` (C3, `extends PlaceCurveSupply`),
   `DiscBudgetSupply` (C4), `MatchingFoldSupply` (C5), `HeavyPinSupply` (C6).
2. Proves `gradedYRootSupply_of_placeCurve` — the genuine C3 §5 weighted-degree grading.
3. Proves `discLocusCellData_of_supplies` and `discLocusCellData_of_placeCurve` — the C6
   assembly: the entire per-cell disc-locus package is now a machine-checked composition of
   the five named interfaces.

## C3's genuine content = the grading only

`gradedYRootSupply_of_placeCurve` proves, for real:
- `D := max (totalDegree H) (max H.natDegree (max (totalDegree R(x₀,·))
   (sup_{j∈supp R} (degreeX(R.coeff j)+j))))`
- `hD : totalDegree H ≤ D`, `hdHD : H.natDegree ≤ D`,
  `hD_Rx0 : totalDegree R(x₀,·) ≤ D`, `hRgrade : ∀ j, degreeX(R.coeff j) ≤ D − j`
  (via `Finset.le_sup` on the support; the off-support case uses `degreeX 0 = 0`).

## Boundary shift (honest)

The SYZ10 plan tentatively put the γ-series polynomial witness `Ppoly, hrepG`, the per-`z`
rational-root section `root`, the `Y`-root divisor `w, hwdeg, hwdvd`, and `hd2` (`2 ≤ natDegreeY R`)
in C3. These are NOT grading bookkeeping — they are the genuine BCIKS §5 Hensel-lift /
branch-selection mathematics (`gammaGenuine` is `(𝕃 H)⟦X⟧`-valued; its genuineness/finiteness
and the divisor `(X − C w) ∣ R` are not one-session gaps). They are **shifted into
`PlaceCurveSupply`** (C2's obligations) as named fields, so `gradedYRootSupply_of_placeCurve`
genuinely proves the grading and passes branch data through unchanged. No new mathematics is
claimed for the branch data.

## Now machine-checked composition

`discLocusCellData_of_placeCurve : PlaceCurveSupply → DiscBudgetSupply → MatchingFoldSupply
→ HeavyPinSupply → DiscLocusCellData` (running C3's derivation internally). Every field of
`DiscLocusCellData` is sourced from exactly one chunk output.

## Remaining open Props (named fields, per chunk)

- **C2 `PlaceCurveSupply`** (incl. boundary-shifted C3 branch data): produce `H` irreducible
  monic pos-degree + `x₀` + `Hypotheses`; plus `hd2`, `root` (rational root ∀ z), `Ppoly/hrepG`
  (γ genuine = polynomial), `w/hwdeg/hwdvd` (Y-root divisor). — genuine open AG.
- **C4 `DiscBudgetSupply`**: `disc` nonzero with base+separability certs over its locus and the
  degree budget `hbig`. — the nonvanishing half is open.
- **C5 `MatchingFoldSupply`**: matching sets folding through `w` with the killBudget count. — open.
- **C6 `HeavyPinSupply`**: heavy set `S₀` in the locus with `max Bw 1 < |S₀|`. — open counting.

C1 (surface existence) LANDED in SYZ10. C3 grading + full composition assembly LANDED here.
Genuine open mathematics = C2 (place-curve/branch) and the C4 disc nonvanishing.

## Axiom audit

`#print axioms` on `gradedYRootSupply_of_placeCurve`, `discLocusCellData_of_supplies`,
`discLocusCellData_of_placeCurve`: `[propext, Classical.choice, Quot.sound]` — clean.
