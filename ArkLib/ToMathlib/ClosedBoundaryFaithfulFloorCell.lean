/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BoundaryThresholdFloorCell
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryLatticeThresholdLeaf
import ArkLib.ToMathlib.FaithfulFrontierComposition

/-!
# The closed-radius boundary, fed by the faithful §5 producer (post-O76/O79 assembly)

After O76 (`BoundaryCardStrictInteriorRefutation`: both *nonemptiness* leaves of the boundary
quantization split are FALSE — kernel-checked witnesses) and O79
(`BoundaryThresholdFloorCell`: the corrected monotone-`ε` floor-cell transport), the honest
closed-boundary route for the [BCIKS20] Theorem 1.5 curve keystone is:

* **non-lattice boundary** (`deg·n` not a perfect square): the full
  `δ_ε_correlatedAgreementCurves` statement at ONE strict floor-matched radius `δ'' < 1 − √ρ`
  transports to the closed boundary with `ε = errorBound δ' > 0`
  (`correlatedAgreementCurves_boundary_of_floorCell_mono`);
* **lattice boundary** (`deg·n` a perfect square, `δ·n ∈ ℕ`): no floor-matched strict radius
  exists, and the leaf is the quantitative-threshold surface of
  `BoundaryLatticeThresholdLeaf` whose single open input is the §5 extraction
  `LatticeCoeffPolyExtraction` at the endpoint.

**The new fact this file exploits**: the strict-radius §5 producer interface is now fully
proven-shaped — the faithful chain
(`FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict`,
and behind it the whole `FaithfulFrontierData` composition) turns a per-`(u, P)`
`CurveFamilyData` producer at ANY strict radius into the full §5 statement at that radius.  So
the "one strict radius per floor cell" input of the corrected route can be fed by the faithful
front door.  This file performs exactly that composition:

```
CurveFamilyProducer k deg domain δ''                      (the faithful §5 producer, strict δ'')
  ──correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict──►
δ_ε_correlatedAgreementCurves at δ'' with ε = errorBound δ''
  ──correlatedAgreementCurves_boundary_of_floorCell_mono (O79: monotone-ε cell transport)──►
δ_ε_correlatedAgreementCurves at the closed boundary δ with ε = errorBound δ'
```

## What is proved here

* `CurveFamilyProducer` / `FaithfulFrontierProducer` — the named per-`(u, P, δ)` producer
  interfaces (exactly the `hInput` shapes of the faithful front doors).
* `errorBound_pos_of_lt_sqrtBoundary` — strict radii have genuinely positive `errorBound`
  (via `DivergenceOfSets.errorBound_ge_const`), so the corrected boundary export is never
  vacuous, unlike the refuted `errorBound (1 − √ρ) = 0` shape.
* `correlatedAgreementCurves_boundary_of_curveFamilyProducer_cell` — **the core composite**: a
  faithful producer at a single cell radius `δ'' ≤ δ' < 1 − √ρ`, floors matched
  `⌊δ''·n⌋ = ⌊δ'·n⌋ = ⌊δ·n⌋`, yields the closed-boundary keystone statement at `δ` with
  `ε = errorBound δ'` — for every floor-matched intermediate `δ'`.
* `correlatedAgreementCurves_boundary_of_curveFamilyProducer` (`δ'' = δ'` form) and
  `correlatedAgreementCurves_boundary_of_faithfulFrontierProducer_cell` (the same export from
  the deeper `FaithfulFrontierData` producer).
* `correlatedAgreementCurves_boundary_nonLattice_of_cellSupply` — at a non-lattice closed
  boundary a floor-matched strict radius always exists
  (`exists_lt_floor_eq_of_floor_lt`), so a producer supply on the cell yields the boundary
  export outright (existential `δ'`).
* `correlatedAgreementCurves_closedBoundary_assembly` — **the closed-boundary keystone
  assembly**: at `δ = 1 − √ρ`, a chosen-cell faithful producer (demanded only on the
  non-lattice branch) plus the lattice-guarded `LatticeCoeffPolyExtraction` (demanded only on
  the genuinely-square branch) yield a strictly positive `ε` with
  `δ_ε_correlatedAgreementCurves` at the closed boundary.
* `correlatedAgreementCurves_closed_assembly` — the full closed-radius form `δ ≤ 1 − √ρ`
  (strict interior served by the producer at `δ` itself).

## The residual map after this file

The closed-radius keystone now rests on exactly:

1. the faithful per-`(u, P)` §5 producer `CurveFamilyProducer` at one strict radius per floor
   cell (suppliable by the faithful chain: `FaithfulFrontierData` and its proven composition);
2. **the genuinely-square lattice branch** — `LatticeCoeffPolyExtraction` at the endpoint
   (`BoundaryLatticeThresholdLeaf`), guarded by `⌊δ·n⌋ = δ·n`: the ONE boundary-specific named
   residual.  It is genuinely open: the quantitative threshold alone is refuted as a lattice
   hypothesis (probe counterexample over `GF(11)`, recorded in `BoundaryLatticeThresholdLeaf`).

The witness namespace instantiates the core composite and the full closed-boundary assembly at
the O76 witness point (`ZMod 5`, `n = 4`, `deg = 2`, `k = 1`, non-lattice `deg·n = 8`): the
producer at the cell radius `δ'' = 1/4` is inhabited (vacuously — the Johnson-side hypothesis
`(1 − ρ)/2 < 1/4` fails *exactly* there, the same caveat as `RemainingCoreWitness`), the
lattice guard is discharged by the kernel-checked non-lattice fact `boundary_floor_lt`, and
the assembly fires end-to-end, certifying that no hypothesis of this file is unsatisfiable.
The exported boundary statement at the witness (`ε = errorBound (7/25)`) is the
probe-verified content of `scripts/probes/probe_boundary_threshold_floorcell.py`
(390,625-stack census, 0 violations).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (list-decoding agreement chain), §6.2 (closed Johnson boundary at `1 − √ρ`).
-/

namespace ArkLib

namespace ClosedBoundaryFaithfulFloorCell

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The named producer interfaces (the `hInput` shapes of the faithful front doors) -/

/-- **The faithful per-`(u, P)` §5 producer at radius `δ`** — exactly the `hInput` shape of
`FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict`:
for every stack above the §5 probability threshold, in the strict Johnson window, every good
per-`z` decoding lies on a polynomial curve (`CurveFamilyData`).  This is the BCIKS20 Prop-5.5
output shape, satisfiable for honest decoded families. -/
abbrev CurveFamilyProducer (k deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0) : Type :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
      FaithfulCurveExtraction.CurveFamilyData
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P

/-- **The faithful-frontier per-`(u, P)` producer at radius `δ`** — the `hInput` shape of
`FaithfulFrontier.correlatedAgreement_affine_curves_of_faithful_frontier`: the same interface,
but producing the deeper `FaithfulFrontierData` bundle (graded GS factor bundle, §6 counting,
truncation tail, per-place readings), from which `CurveFamilyData` is PROVEN
(`curveFamilyData_of_faithfulFrontier`). -/
abbrev FaithfulFrontierProducer (k deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0) : Type :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
      FaithfulFrontier.FaithfulFrontierData
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P

/-- A frontier producer lowers to a curve-family producer through the PROVEN composition
`FaithfulFrontier.curveFamilyData_of_faithfulFrontier`. -/
noncomputable def CurveFamilyProducer.ofFrontier {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hProd : FaithfulFrontierProducer k deg domain δ) :
    CurveFamilyProducer k deg domain δ :=
  fun hk u hprob hJ hsqrt P hP =>
    FaithfulFrontier.curveFamilyData_of_faithfulFrontier (hProd hk u hprob hJ hsqrt P hP)

/-! ## Strict radii have genuinely positive `errorBound` -/

omit [DecidableEq F] in
/-- **Strict radii are never vacuous**: below the Johnson boundary, `errorBound` is at least
`n/q > 0` (`DivergenceOfSets.errorBound_ge_const`).  This is the quantitative content of the
corrected boundary export `ε = errorBound δ' > 0`, in contrast with the refuted boundary shape
`errorBound (1 − √ρ) = 0` (`BoundaryDischarge.errorBound_eq_zero_at_boundary`). -/
theorem errorBound_pos_of_lt_sqrtBoundary {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg) (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    0 < errorBound δ deg domain := by
  have hcardι : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hcardF : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos (α := F)
  exact lt_of_lt_of_le (div_pos hcardι hcardF)
    (DivergenceOfSets.errorBound_ge_const (deg := deg) (domain := domain) hdeg hδ)

/-! ## The core composite: faithful producer at one cell radius ⟹ closed-boundary export -/

/-- **THE COMPOSITE.**  A faithful per-`(u, P)` §5 producer at a single floor-cell radius
`δ'' ≤ δ' < 1 − √ρ`, with floors matched `⌊δ''·n⌋ = ⌊δ'·n⌋ = ⌊δ·n⌋`, yields the
closed-boundary curve keystone at `δ` with `ε = errorBound δ'` — for every floor-matched
intermediate `δ'`.  This is the strict faithful front door
(`correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict`) composed with the O79
monotone-`ε` floor-cell transport (`correlatedAgreementCurves_boundary_of_floorCell_mono`):
the strict-radius input of the corrected boundary route, fed by the faithful chain. -/
theorem correlatedAgreementCurves_boundary_of_curveFamilyProducer_cell
    {k deg : ℕ} {domain : ι ↪ F} {δ δ' δ'' : ℝ≥0} [NeZero deg]
    (hle : δ'' ≤ δ')
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor'' : Nat.floor (δ'' * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι))
    (hfloor' : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hProd : CurveFamilyProducer k deg domain δ'') :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := errorBound δ' deg domain) :=
  BoundaryThresholdFloorCell.correlatedAgreementCurves_boundary_of_floorCell_mono
    (Nat.pos_of_neZero deg) hle hδ' hfloor'' hfloor'
    (FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict
      (k := k) (deg := deg) (domain := domain) (δ := δ'')
      (lt_of_le_of_lt hle hδ') hProd)

/-- The single-radius form of the composite (`δ'' = δ'`): a faithful producer at one
floor-matched strict radius `δ'` yields the closed-boundary keystone at `δ` with
`ε = errorBound δ'`.  Taking `δ' = δ` (floors `rfl`) recovers the strict front door itself. -/
theorem correlatedAgreementCurves_boundary_of_curveFamilyProducer
    {k deg : ℕ} {domain : ι ↪ F} {δ δ' : ℝ≥0} [NeZero deg]
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hProd : CurveFamilyProducer k deg domain δ') :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := errorBound δ' deg domain) :=
  correlatedAgreementCurves_boundary_of_curveFamilyProducer_cell
    le_rfl hδ' rfl hfloor hProd

/-- The composite from the deeper faithful-frontier producer: the `FaithfulFrontierData`
bundle at one cell radius yields the closed-boundary keystone export. -/
theorem correlatedAgreementCurves_boundary_of_faithfulFrontierProducer_cell
    {k deg : ℕ} {domain : ι ↪ F} {δ δ' δ'' : ℝ≥0} [NeZero deg]
    (hle : δ'' ≤ δ')
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor'' : Nat.floor (δ'' * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι))
    (hfloor' : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hProd : FaithfulFrontierProducer k deg domain δ'') :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := errorBound δ' deg domain) :=
  correlatedAgreementCurves_boundary_of_curveFamilyProducer_cell
    hle hδ' hfloor'' hfloor' (CurveFamilyProducer.ofFrontier hProd)

/-! ## The non-lattice closed boundary from a producer supply on the cell -/

/-- **Non-lattice front door.**  At a closed radius `δ ≤ 1 − √ρ` whose distance scale is not a
`1/n`-lattice point (`⌊δ·n⌋ < δ·n`), a floor-matched strict sub-radius always exists
(`exists_lt_floor_eq_of_floor_lt`), so a faithful producer supply on the floor cell yields the
boundary export outright: some floor-matched `δ' < δ` carries the keystone statement at `δ`
with `ε = errorBound δ' > 0`. -/
theorem correlatedAgreementCurves_boundary_nonLattice_of_cellSupply
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hNotLattice : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) < δ * Fintype.card ι)
    (hSupply : ∀ δ' : ℝ≥0, δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      CurveFamilyProducer k deg domain δ') :
    ∃ δ' : ℝ≥0, δ' < δ ∧
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) ∧
      δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
        (ε := errorBound δ' deg domain) := by
  obtain ⟨δ', hδ'lt, hδ'floor⟩ :=
    ArkLib.BoundaryCardResidual.exists_lt_floor_eq_of_floor_lt
      (Fintype.card ι) Fintype.card_pos hNotLattice
  exact ⟨δ', hδ'lt, hδ'floor,
    correlatedAgreementCurves_boundary_of_curveFamilyProducer
      (lt_of_lt_of_le hδ'lt hδ) hδ'floor (hSupply δ' hδ'lt hδ'floor)⟩

/-! ## The closed-radius assemblies: faithful producers + the square-lattice residual -/

/-- **The closed-boundary keystone assembly.**  At the closed Johnson boundary
`δ = 1 − √ρ`, the curve keystone holds with a strictly positive error parameter, from exactly
the two post-O76/O79 leaves:

* `hCell` — on the **non-lattice** branch, a chosen floor-matched strict radius `δ'` with a
  faithful per-`(u, P)` §5 producer there (the proven-shaped faithful-chain interface; the
  branch hypothesis `⌊δ·n⌋ < δ·n` certifies such a radius exists);
* `hLat` — on the **genuinely-square lattice** branch (`⌊δ·n⌋ = δ·n`, i.e. `deg·n` a perfect
  square), the §5 extraction `LatticeCoeffPolyExtraction` at the endpoint — the ONE remaining
  boundary-specific named residual.

The non-lattice branch exports `ε = errorBound δ' > 0`; the lattice branch exports
`ε = (n+1)/|F| > 0`.  Neither is the refuted vacuous `errorBound (1 − √ρ) = 0` shape. -/
theorem correlatedAgreementCurves_closedBoundary_assembly
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] (hk : 0 < k)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hCell : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) < δ * Fintype.card ι →
      Σ' (δ' : ℝ≥0) (_ : δ' < δ)
        (_ : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι)),
        CurveFamilyProducer k deg domain δ')
    (hLat : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι →
      BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction
        (k := k) (deg := deg) (domain := domain) δ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (ε := ε) := by
  rcases lt_or_eq_of_le (Nat.floor_le (zero_le (δ * Fintype.card ι))) with hlt | heq
  · obtain ⟨δ', hδ'lt, hδ'floor, hProd⟩ := hCell hlt
    have hδ'b : δ' < 1 - ReedSolomon.sqrtRate deg domain :=
      lt_of_lt_of_le hδ'lt hδeq.le
    exact ⟨errorBound δ' deg domain,
      errorBound_pos_of_lt_sqrtBoundary (Nat.pos_of_neZero deg) hδ'b,
      correlatedAgreementCurves_boundary_of_curveFamilyProducer hδ'b hδ'floor hProd⟩
  · exact ⟨BoundaryLatticeThresholdLeaf.latticeThresholdEps ι F,
      BoundaryLatticeThresholdLeaf.latticeThresholdEps_pos,
      BoundaryLatticeThresholdLeaf.correlatedAgreementCurves_of_latticeExtraction
        hk (hLat heq)⟩

/-- **The full closed-radius keystone assembly** (`δ ≤ 1 − √ρ`).  The curve keystone with a
strictly positive error parameter, from per-`(u, P, δ')` faithful producers plus the
genuinely-square lattice residual:

* strict interior `δ < 1 − √ρ`: the faithful producer at `δ` itself
  (`ε = errorBound δ > 0`);
* non-lattice boundary: a chosen-cell faithful producer (`ε = errorBound δ' > 0`);
* square-lattice boundary: `LatticeCoeffPolyExtraction` (`ε = (n+1)/|F| > 0`) — the one named
  residual. -/
theorem correlatedAgreementCurves_closed_assembly
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] (hk : 0 < k)
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrict : δ < 1 - ReedSolomon.sqrtRate deg domain →
      CurveFamilyProducer k deg domain δ)
    (hCell : δ = 1 - ReedSolomon.sqrtRate deg domain →
      (Nat.floor (δ * Fintype.card ι) : ℝ≥0) < δ * Fintype.card ι →
      Σ' (δ' : ℝ≥0) (_ : δ' < δ)
        (_ : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι)),
        CurveFamilyProducer k deg domain δ')
    (hLat : δ = 1 - ReedSolomon.sqrtRate deg domain →
      (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι →
      BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction
        (k := k) (deg := deg) (domain := domain) δ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (ε := ε) := by
  rcases lt_or_eq_of_le hδ with hstrict | hbound
  · exact ⟨errorBound δ deg domain,
      errorBound_pos_of_lt_sqrtBoundary (Nat.pos_of_neZero deg) hstrict,
      correlatedAgreementCurves_boundary_of_curveFamilyProducer hstrict rfl
        (hStrict hstrict)⟩
  · exact correlatedAgreementCurves_closedBoundary_assembly hk hbound
      (hCell hbound) (hLat hbound)

end ClosedBoundaryFaithfulFloorCell

/-! ## Satisfiability witness — the O76 point, end-to-end through the new assembly

At the O76 witness (`ι = Fin 4`, `F = ZMod 5`, `deg = 2`, `k = 1`, non-lattice boundary
`δ = 1 − √(1/2)`, `deg·n = 8` non-square): the faithful producer at the cell radius
`δ'' = 1/4` is inhabited — *vacuously*, because the Johnson-side hypothesis
`(1 − ρ)/2 < 1/4` fails exactly (`(1 − 1/2)/2 = 1/4`), the same honest caveat as
`RemainingCoreWitness` — and the lattice guard is discharged by the kernel-checked
non-lattice fact `boundary_floor_lt`.  The full hypothesis spine of the closed-boundary
assembly is therefore simultaneously satisfiable, and its unconditional export at the witness
is the probe-verified boundary statement (`ε = errorBound (7/25)`,
390,625-stack census, 0 violations). -/

namespace ClosedBoundaryFaithfulFloorCellWitness

open ArkLib.BoundaryCardResidualRefutation ArkLib.BoundaryCardStrictInteriorRefutation
  ArkLib.BoundaryThresholdFloorCellWitness ArkLib.ClosedBoundaryFaithfulFloorCell
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The witness Reed–Solomon code has rate exactly `1/2` (`dim 2`, length `4`). -/
theorem rate_eq_half :
    (LinearCode.rate (ReedSolomon.code domain 2) : ℝ≥0) = 1 / 2 := by
  have h := ReedSolomon.rateOfLinearCode_eq_div' (n := 2) (α := domain)
    (by norm_num [I])
  rw [h]
  have hcard : (Fintype.card I : ℚ≥0) = 4 := by norm_num [I]
  rw [hcard]
  norm_num

/-- At the cell radius `δ'' = 1/4` the Johnson-side hypothesis fails *exactly*:
`(1 − ρ)/2 = (1 − 1/2)/2 = 1/4`.  This is what makes the witness producer inhabitable
(vacuously) at toy size; the genuine §5 content is a large-`q` phenomenon. -/
theorem not_johnson_at_quarter :
    ¬ ((1 - (LinearCode.rate (ReedSolomon.code domain 2) : ℝ≥0)) / 2
      < (1 / 4 : ℝ≥0)) := by
  rw [rate_eq_half,
    show (1 : ℝ≥0) - 1 / 2 = 1 / 2 by
      rw [tsub_eq_iff_eq_add_of_le (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]; norm_num]
  norm_num

/-- The faithful producer interface is inhabited at the witness cell radius `δ'' = 1/4`. -/
def producerQuarter : CurveFamilyProducer 1 2 domain (1 / 4 : ℝ≥0) :=
  fun _hk _u _hprob hJ _hsqrt _P _hP => absurd hJ not_johnson_at_quarter

/-- **The core composite fires at the witness**: the closed-boundary keystone export with
`ε = errorBound (7/25)` from the faithful producer at the single cell radius `1/4`, across the
chain `1/4 ≤ 7/25 < 1 − √(1/2)` (the UDR→Johnson seam). -/
theorem boundary_export_from_faithful_producer :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := I)
      (C := (ReedSolomon.code domain 2 : Set (I → F)))
      (δ := 1 - ReedSolomon.sqrtRate 2 domain)
      (ε := errorBound (7 / 25 : ℝ≥0) 2 domain) :=
  correlatedAgreementCurves_boundary_of_curveFamilyProducer_cell
    (by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 4)
        (by norm_num : (0 : ℝ≥0) < 25)]
      norm_num)
    sevenDivTwentyFive_lt_boundary
    (by rw [quarter_floor_eq_one, floor_sevenDivTwentyFive_eq_one])
    (by rw [floor_sevenDivTwentyFive_eq_one, boundary_floor_eq_one])
    producerQuarter

/-- **The full closed-boundary assembly fires at the witness**: a strictly positive `ε` with
the keystone statement at the closed boundary, with the cell leaf served by `producerQuarter`
and the lattice guard discharged by the kernel-checked non-lattice fact
(`boundary_floor_lt`). -/
theorem closedBoundary_assembly_fires :
    ∃ ε : ℝ≥0, 0 < ε ∧
      δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := I)
        (C := (ReedSolomon.code domain 2 : Set (I → F)))
        (δ := 1 - ReedSolomon.sqrtRate 2 domain) (ε := ε) :=
  correlatedAgreementCurves_closedBoundary_assembly Nat.one_pos rfl
    (fun _ => ⟨1 / 4, quarter_lt_boundary, floor_quarter_eq_floor_boundary,
      producerQuarter⟩)
    (fun heq => absurd heq (ne_of_lt boundary_floor_lt))

end ClosedBoundaryFaithfulFloorCellWitness

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.ClosedBoundaryFaithfulFloorCell.CurveFamilyProducer.ofFrontier
#print axioms ArkLib.ClosedBoundaryFaithfulFloorCell.errorBound_pos_of_lt_sqrtBoundary
#print axioms
  ArkLib.ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_boundary_of_curveFamilyProducer_cell
#print axioms
  ArkLib.ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_boundary_of_curveFamilyProducer
#print axioms
  ArkLib.ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_boundary_of_faithfulFrontierProducer_cell
#print axioms
  ArkLib.ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_boundary_nonLattice_of_cellSupply
#print axioms
  ArkLib.ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_closedBoundary_assembly
#print axioms ArkLib.ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_closed_assembly
#print axioms ArkLib.ClosedBoundaryFaithfulFloorCellWitness.rate_eq_half
#print axioms ArkLib.ClosedBoundaryFaithfulFloorCellWitness.not_johnson_at_quarter
#print axioms ArkLib.ClosedBoundaryFaithfulFloorCellWitness.producerQuarter
#print axioms
  ArkLib.ClosedBoundaryFaithfulFloorCellWitness.boundary_export_from_faithful_producer
#print axioms ArkLib.ClosedBoundaryFaithfulFloorCellWitness.closedBoundary_assembly_fires
