/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R368SignedDifferenceFiberDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R321ShadowAutocorrelationDoubling

/-!
# R369: every signed difference fiber is a doubled walk endpoint

R321 proved autocorrelation doubling only for finite-field kernel relations because its consumer
was raw collision mass.  The combinatorial identity is field-independent.  This file extends it
to every nonzero characteristic-zero shadow difference, including the negative terms required by
R368's centered discrepancy.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R369SignedDifferenceMassDoubling

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling
open ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy
open ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition

/-- Every member of the all-difference set is genuinely nonzero. -/
theorem ne_zero_of_mem_allShadowDifferences
    (n m r : ℕ) {d : Fin m → ℤ} (hd : d ∈ allShadowDifferences n m r) : d ≠ 0 := by
  classical
  rw [allShadowDifferences, Finset.mem_image] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
  intro hzero
  apply hne
  funext j
  have hj := congrFun hzero j
  simp only [shadowDifference, Pi.zero_apply, sub_eq_zero] at hj
  exact hj.symm

/-- **Field-independent mass doubling.** Every nonzero difference fiber has exactly the
characteristic-zero doubled-walk endpoint mass. -/
theorem allShadowDifferenceMass_eq_NR_double
    (m r : ℕ) {d : Fin m → ℤ} (hdne : d ≠ 0) :
    allShadowDifferenceMass (2 * m) m r d = NR (2 * m) m (r + r) d := by
  classical
  rw [← tuplePairDifferenceCount_eq_NR]
  rw [tuplePairDifferenceCount_eq_sum_keyPairs]
  unfold allShadowDifferenceMass
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
  constructor
  · rintro ⟨⟨hp1, hp2, hne⟩, hdiff⟩
    exact ⟨⟨hp1, hp2⟩, hdiff⟩
  · rintro ⟨⟨hp1, hp2⟩, hdiff⟩
    have hne : p.1 ≠ p.2 := by
      intro heq
      apply hdne
      rw [← hdiff]
      funext j
      change p.2 j - p.1 j = 0
      rw [heq]
      simp
    exact ⟨⟨hp1, hp2, hne⟩, hdiff⟩

/-- R368 rewritten entirely as a signed doubled-walk endpoint sum. -/
theorem signedShadowPairDiscrepancy_eq_sum_NR_double
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) :
    signedShadowPairDiscrepancy g (2 * m) m r =
      ∑ d ∈ allShadowDifferences (2 * m) m r,
        (NR (2 * m) m (r + r) d : ℝ) * differenceDiscrepancyCoeff g m d := by
  rw [signedShadowPairDiscrepancy_eq_sum_differenceMass]
  apply Finset.sum_congr rfl
  intro d hd
  rw [allShadowDifferenceMass_eq_NR_double m r
    (ne_zero_of_mem_allShadowDifferences (2 * m) m r hd)]

end ArkLib.ProximityGap.Frontier.R369SignedDifferenceMassDoubling

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R369SignedDifferenceMassDoubling.allShadowDifferenceMass_eq_NR_double
#print axioms
  ArkLib.ProximityGap.Frontier.R369SignedDifferenceMassDoubling.signedShadowPairDiscrepancy_eq_sum_NR_double
