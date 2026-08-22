/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R314KernelRelationMassDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS3AnnihilatorHeightBound

/-!
# LANE B2 (#466 round 315): bounded kernel relations own divisible resultants

R314 turns every contribution to the finite-field energy surplus into a nonzero integer
vector `d`, of height at most `2r`, in the kernel of evaluation at `g`.  This file forms

```text
P_d(X) = sum_{j<m} d_j X^j
```

and welds it to FS3.  At the dyadic shape `m=2^k`, every realized relation owns a nonzero
integer annihilator of explicit height, divisible by the field characteristic.

Issue #466, round 315, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound

/-- Integer polynomial represented by a shadow-difference coefficient vector. -/
noncomputable def relationPoly {m : ℕ} (d : Fin m → ℤ) : ℤ[X] :=
  ∑ j : Fin m, C (d j) * X ^ (j : ℕ)

/-- Coefficient recovery inside the represented range. -/
theorem relationPoly_coeff_fin {m : ℕ} (d : Fin m → ℤ) (j : Fin m) :
    (relationPoly d).coeff (j : ℕ) = d j := by
  classical
  rw [relationPoly, finset_sum_coeff, Finset.sum_eq_single j]
  · simp [coeff_C_mul, coeff_X_pow]
  · intro i _ hij
    have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h.symm)
    simp [coeff_C_mul, coeff_X_pow, hne]
  · exact fun hj => absurd (Finset.mem_univ j) hj

/-- Coefficients beyond the represented range vanish. -/
theorem relationPoly_coeff_eq_zero_of_le {m i : ℕ} (d : Fin m → ℤ) (hi : m ≤ i) :
    (relationPoly d).coeff i = 0 := by
  classical
  rw [relationPoly, finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  have hne : i ≠ (j : ℕ) := by omega
  simp [coeff_C_mul, coeff_X_pow, hne]

/-- A nonzero coefficient vector gives a nonzero represented polynomial. -/
theorem relationPoly_ne_zero {m : ℕ} {d : Fin m → ℤ} (hd : d ≠ 0) :
    relationPoly d ≠ 0 := by
  intro hzero
  apply hd
  funext j
  have hcoeff := relationPoly_coeff_fin d j
  rw [hzero, coeff_zero] at hcoeff
  exact hcoeff.symm

/-- The represented polynomial has degree strictly below the vector length. -/
theorem relationPoly_natDegree_lt {m : ℕ} (hm : 0 < m) (d : Fin m → ℤ) :
    (relationPoly d).natDegree < m := by
  classical
  unfold relationPoly
  refine lt_of_le_of_lt (natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_lt]
  refine ⟨hm, ?_⟩
  intro j _
  calc
    (C (d j) * X ^ (j : ℕ)).natDegree
        ≤ (C (d j)).natDegree + (X ^ (j : ℕ)).natDegree := natDegree_mul_le
    _ ≤ 0 + (j : ℕ) := by
      gcongr
      · exact (natDegree_C _).le
      · exact natDegree_X_pow_le _
    _ < m := by simpa using j.isLt

/-- Polynomial evaluation agrees with the shadow evaluation map. -/
theorem aeval_relationPoly {F : Type*} [Field F] (g : F) {m : ℕ} (d : Fin m → ℤ) :
    aeval g (relationPoly d) = evalVec g m d := by
  classical
  unfold relationPoly evalVec
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp

/-- A coordinate height bound transfers to every polynomial coefficient. -/
theorem relationPoly_coeff_abs_le {m B : ℕ} {d : Fin m → ℤ}
    (hd : ∀ j, |d j| ≤ (B : ℤ)) (i : ℕ) :
    |(relationPoly d).coeff i| ≤ (B : ℤ) := by
  by_cases hi : i < m
  · let j : Fin m := ⟨i, hi⟩
    simpa [j, relationPoly_coeff_fin d j] using hd j
  · rw [relationPoly_coeff_eq_zero_of_le d (by omega)]
    simp

/-- **RESULTANT WELD.**  At `m=2^k`, every realized R314 kernel relation has a nonzero
annihilator `N`, with the FS3 explicit dyadic height, and the characteristic `p` divides
`N`.  The parameter `b` only needs to satisfy `2r <= 2^b`. -/
theorem kernelRelation_annihilator_exists
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [CharP F p] (g : F) (n k r b : ℕ)
    (hg : g ^ (2 ^ k) = -1) (h2r : 2 * r ≤ 2 ^ b)
    {d : Fin (2 ^ k) → ℤ}
    (hd : d ∈ shadowKernelRelations g n (2 ^ k) r) :
    ∃ N : ℕ, N ≠ 0 ∧ N ≤ 2 ^ ((k + 1 + b) * 2 ^ (k + 1)) ∧ p ∣ N := by
  have hdstruct := shadowKernelRelation_ne_zero_and_evalVec_eq_zero
    g n (2 ^ k) r hd
  have hdheight := shadowKernelRelation_abs_le_two_mul_r
    g n (2 ^ k) r hd
  have hcoeff : ∀ i, |(relationPoly d).coeff i| ≤ (2 ^ b : ℤ) := by
    apply relationPoly_coeff_abs_le
    intro j
    have h2rZ : ((2 * r : ℕ) : ℤ) ≤ ((2 ^ b : ℕ) : ℤ) := by exact_mod_cast h2r
    exact le_trans (hdheight j) h2rZ
  obtain ⟨N, hN0, hNheight, hdiv⟩ :=
    pattern_annihilator_exists_with_height
      (relationPoly_ne_zero hdstruct.1)
      (relationPoly_natDegree_lt (by positivity) d) hcoeff
  refine ⟨N, hN0, hNheight, ?_⟩
  exact hdiv F inferInstance p inferInstance g hg
    (by rw [aeval_relationPoly, hdstruct.2])

end ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld.relationPoly_coeff_fin
#print axioms
  ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld.aeval_relationPoly
#print axioms
  ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld.kernelRelation_annihilator_exists
