/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeReceivedJetColumns
import ArkLib.Research.ProximityGap.Frontier.IntrinsicReceivedSections

/-! # Original selected sections in the scalar coefficient chart -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeSelectedSectionChart

open Finset Polynomial IntrinsicReceivedSections JetMultiplierGraph
open SecondPrimeCoordinateWeight WeightedSylvesterDegree
variable {K : Type} [Field K]

/-- The genuine scalar/value triangle remains the height of scalar coefficients after swapping
the coordinate and scalar axes. -/
theorem original_scalar_bound (f : Surface K) {m : ℕ} (hf : TotalDegreeLe f m) :
    ScalarValueBound (f.map Bivariate.swap.toRingHom) m := by
  intro k l hne
  simp only [coeff_map] at hne ⊢
  have fk : f.coeff k ≠ 0 := fun hz => hne (by simp [hz])
  have h := hf k fk
  have hl : ((Bivariate.swap (f.coeff k)).coeff l).natDegree ≤ (f.coeff k).natDegree := by
    rw [← Bivariate.natDegreeY, ← Bivariate.degreeX_swap]
    apply Finset.le_sup (f := fun i => ((Bivariate.swap (f.coeff k)).coeff i).natDegree)
    exact mem_support_iff.mpr hne
  exact le_trans (Nat.add_le_add_right hl k) h

/-- The scalar specialization in the intrinsic interpolation theorem is exactly the original
selected-polynomial evaluation, for every scalar and every candidate. -/
theorem section_identity (f : Surface K) (z : K) (q : K[X]) :
    (mapPlane (evalRingHom z) (f.map Bivariate.swap.toRingHom)).eval q =
      f.eval₂ (evalRingHom (C z)) q := by
  rw [← eval_map]
  congr 1
  apply Polynomial.ext
  intro i
  simp only [mapPlane, coeff_map, coe_mapRingHom, coe_evalRingHom]
  rw [← Bivariate.evalX_eq_map]
  exact (Bivariate.evalY_eq_evalX_swap z (f.coeff i)).symm

#print axioms original_scalar_bound
#print axioms section_identity
end ArkLib.ProximityGap.Frontier.SecondPrimeSelectedSectionChart
