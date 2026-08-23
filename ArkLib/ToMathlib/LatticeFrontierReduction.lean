/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaw
-/
import ArkLib.ToMathlib.UnifiedExtractionTarget
import ArkLib.ToMathlib.ClosedBoundaryFaithfulFloorCell

/-!
# The lattice leaf, one layer deeper: `LatticeCoeffPolyExtraction` from the faithful frontier

After O76/O79, the closed-boundary keystone assembly
(`ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_closedBoundary_assembly`) rests on
two branch residuals:

* **non-lattice branch** — a floor-matched cell-radius `CurveFamilyProducer`, which already
  lowers through the PROVEN frontier composition
  (`CurveFamilyProducer.ofFrontier` ∘ `FaithfulFrontier.curveFamilyData_of_faithfulFrontier`)
  to the structured `FaithfulFrontierData` bundle;
* **square-lattice branch** — the bare extraction Prop
  `BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction` (`∃ B` coefficient polynomials),
  which had **no** frontier-level reduction: the strict-Johnson producer interfaces are
  unusable at the exact endpoint `δ = 1 − √ρ` (their `δ < 1 − √ρ` guard is false there), so
  the lattice leaf was stuck one abstraction layer above the rest of the chain.

This file supplies that missing layer.  `CountFrontierProducer` is the count-triggered
(`k < |good|`, no Johnson-window guards — the same trigger as
`UnifiedExtractionTarget.UnifiedProducer`) per-`(u, P)` producer of the *frontier bundle*
`FaithfulFrontier.FaithfulFrontierData`.  Through the proven composition
`curveFamilyData_of_faithfulFrontier` it discharges `UnifiedProducer`, hence (via the proven
`latticeCoeffPolyExtraction_of_producer`) the lattice extraction residual, hence the corrected
lattice-leaf surface `BoundaryCardLatticeThresholdResidual` — and the closed-boundary keystone
assembly can now consume **frontier producers on both branches**
(`correlatedAgreementCurves_closedBoundary_assembly_of_frontier`).

The reduction is strict progress in the same sense as the cell-radius lane: the residual
surface moves from an opaque `∃ B` interpolation statement to the structured
`FaithfulFrontierData` whose every field is a recognized BCIKS20 §5/§6 ingredient with its own
named production lane (graded GS bundle — (iii)–(v) proven by re-grading; `MonicHighYResidual`
— now boundary-pinned by `MonicResidualBoundary`; the §6 counting inequality; the matching
window; the truncation tail; the per-place readings).  Nothing is discharged vacuously: the
producer hypothesis is `Type`-valued data, exactly like the in-tree `hCell` branch.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib

namespace LatticeFrontierReduction

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The count-triggered faithful-frontier producer.**  For every stack whose good set
exceeds the bare count trigger `k` (the weakest trigger any consumer supplies — in particular
implied by the lattice threshold count `(n+1)·k < |good|`), and every admissible per-`z`
decoding `P`, a faithful frontier bundle.  Unlike `FaithfulFrontierProducer` this carries
**no** strict-Johnson guards, so it is *consumable at the exact closed boundary endpoint*
`δ = 1 − √ρ`, where the guarded producers are vacuously unusable. -/
def CountFrontierProducer (k deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0) : Type :=
  ∀ u : WordStack F (Fin (k + 1)) ι,
    k < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
      FaithfulFrontier.FaithfulFrontierData
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P

/-- A count-triggered frontier producer discharges the unified production target, through the
PROVEN frontier composition `FaithfulFrontier.curveFamilyData_of_faithfulFrontier`. -/
theorem unifiedProducer_of_countFrontier {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hProd : CountFrontierProducer (F := F) k deg domain δ) :
    UnifiedExtractionTarget.UnifiedProducer (k := k) (deg := deg) (ι := ι) (F := F)
      domain δ :=
  fun u hcount P hP =>
    ⟨FaithfulFrontier.curveFamilyData_of_faithfulFrontier (hProd u hcount P hP)⟩

/-- **The lattice extraction residual from the frontier (the new reduction layer).**  The
square-lattice branch's `LatticeCoeffPolyExtraction` — previously the bare `∃ B` endpoint
residual — now reduces to count-triggered frontier production, the same structured surface as
the rest of the faithful chain. -/
theorem latticeCoeffPolyExtraction_of_countFrontier {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hProd : CountFrontierProducer (F := F) k deg domain δ) :
    ArkLib.BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction
      (k := k) (deg := deg) domain δ :=
  UnifiedExtractionTarget.latticeCoeffPolyExtraction_of_producer
    (unifiedProducer_of_countFrontier hProd)

/-- **The corrected lattice-leaf surface from the frontier.**  Chains the new layer into the
O76-corrected lattice leaf: a count-triggered frontier producer discharges the quantitative
threshold residual `BoundaryCardLatticeThresholdResidual` outright. -/
theorem boundaryCardLatticeThresholdResidual_of_countFrontier
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hProd : CountFrontierProducer (F := F) k deg domain δ) :
    ArkLib.BoundaryLatticeThresholdLeaf.BoundaryCardLatticeThresholdResidual
      (k := k) (deg := deg) domain δ :=
  ArkLib.BoundaryLatticeThresholdLeaf.boundaryCardLatticeThresholdResidual_of_extraction
    (latticeCoeffPolyExtraction_of_countFrontier hProd)

/-- **The closed-boundary keystone assembly, frontier producers on both branches.**  The
keystone `δ_ε_correlatedAgreementCurves` with strictly positive error at the closed Johnson
boundary `δ = 1 − √ρ`, from:

* `hCell` (non-lattice branch): a floor-matched cell-radius *guarded* frontier producer
  (lowered by the proven `CurveFamilyProducer.ofFrontier`);
* `hLat` (square-lattice branch): a count-triggered frontier producer at `δ` itself (lowered
  by the new `latticeCoeffPolyExtraction_of_countFrontier`).

Both branch residuals now live on the **same** structured `FaithfulFrontierData` surface; the
bare `∃ B` lattice extraction no longer appears as a separate residual shape. -/
theorem correlatedAgreementCurves_closedBoundary_assembly_of_frontier
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] (hk : 0 < k)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hCell : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) < δ * Fintype.card ι →
      Σ' (δ' : ℝ≥0) (_ : δ' < δ)
        (_ : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι)),
        ClosedBoundaryFaithfulFloorCell.FaithfulFrontierProducer k deg domain δ')
    (hLat : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι →
      CountFrontierProducer (F := F) k deg domain δ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (ε := ε) := by
  refine ClosedBoundaryFaithfulFloorCell.correlatedAgreementCurves_closedBoundary_assembly
    hk hδeq (fun h => ?_) (fun h => latticeCoeffPolyExtraction_of_countFrontier (hLat h))
  obtain ⟨δ', h1, h2, p⟩ := hCell h
  exact ⟨δ', h1, h2, ClosedBoundaryFaithfulFloorCell.CurveFamilyProducer.ofFrontier p⟩

end LatticeFrontierReduction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.LatticeFrontierReduction.CountFrontierProducer
#print axioms ArkLib.LatticeFrontierReduction.unifiedProducer_of_countFrontier
#print axioms ArkLib.LatticeFrontierReduction.latticeCoeffPolyExtraction_of_countFrontier
#print axioms ArkLib.LatticeFrontierReduction.boundaryCardLatticeThresholdResidual_of_countFrontier
#print axioms ArkLib.LatticeFrontierReduction.correlatedAgreementCurves_closedBoundary_assembly_of_frontier
