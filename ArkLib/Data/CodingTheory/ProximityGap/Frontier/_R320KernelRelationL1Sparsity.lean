/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R315KernelRelationResultantWeld

/-!
# LANE B2 (#466 round 320): realized kernel relations have `L1 <= 2r`

R314 records the coordinate-height bound `|d_j| <= 2r`.  The relation is much sparser:
each depth-`r` shadow is a sum of `r` signed basis vectors, so the difference of two shadows
has total integer `L1` mass at most `2r`, independently of the cyclotomic degree `m`.

This file proves that sharp bound and the resulting support bound `support(d) <= 2r` for every
realized finite-field collision relation.  These are the inputs needed by sparse-resultant
and inverse Littlewood--Offord attacks on the fixed prize prime.

Issue #466, round 320, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R320KernelRelationL1Sparsity

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Integer `L1` mass of a shadow vector. -/
def shadowL1 {m : ℕ} (v : Fin m → ℤ) : ℕ :=
  ∑ j : Fin m, (v j).natAbs

/-- Support of a shadow vector. -/
def shadowSupport {m : ℕ} (v : Fin m → ℤ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => v j ≠ 0)

/-- A single folded root index contributes `L1` mass at most one. -/
theorem shadowL1_vecOf_le_one {n m : ℕ} (hn : n = 2 * m) (a : Fin n) :
    shadowL1 (vecOf n m a) ≤ 1 := by
  unfold shadowL1
  have ha : (a : ℕ) < 2 * m := by omega
  have hpt : ∀ j : Fin m, (vecOf n m a j).natAbs
      ≤ (if (a : ℕ) = (j : ℕ) then 1 else 0)
        + (if (a : ℕ) = (j : ℕ) + m then 1 else 0) := by
    intro j
    unfold vecOf
    split <;> split <;> simp
  calc
    (∑ j : Fin m, (vecOf n m a j).natAbs)
        ≤ ∑ j : Fin m, ((if (a : ℕ) = (j : ℕ) then 1 else 0)
          + (if (a : ℕ) = (j : ℕ) + m then 1 else 0)) :=
      Finset.sum_le_sum (fun j _ => hpt j)
    _ ≤ 1 := by
      rw [Finset.sum_add_distrib]
      by_cases hcase : (a : ℕ) < m
      · let j0 : Fin m := ⟨(a : ℕ), hcase⟩
        have h1 : ∑ j : Fin m, (if (a : ℕ) = (j : ℕ) then 1 else 0) = 1 := by
          rw [Finset.sum_eq_single j0]
          · simp [j0]
          · intro j _ hj
            have hne : (a : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext (by simpa [j0] using h.symm))
            simp [hne]
          · simp
        have h2 : ∑ j : Fin m,
            (if (a : ℕ) = (j : ℕ) + m then 1 else 0) = 0 :=
          Finset.sum_eq_zero (fun j _ => if_neg (by omega))
        rw [h1, h2]
      · have ham : (a : ℕ) - m < m := by omega
        let j0 : Fin m := ⟨(a : ℕ) - m, ham⟩
        have h1 : ∑ j : Fin m, (if (a : ℕ) = (j : ℕ) then 1 else 0) = 0 :=
          Finset.sum_eq_zero (fun j _ => if_neg (by omega))
        have h2 : ∑ j : Fin m,
            (if (a : ℕ) = (j : ℕ) + m then 1 else 0) = 1 := by
          rw [Finset.sum_eq_single j0]
          · simp [j0]
            omega
          · intro j _ hj
            have hne : (a : ℕ) ≠ (j : ℕ) + m := by
              intro h
              apply hj
              ext
              simp only [j0, Fin.val_mk]
              omega
            simp [hne]
          · simp
        rw [h1, h2]

/-- A depth-`r` shadow has total `L1` mass at most `r`. -/
theorem shadowL1_tupleVec_le_r (n m r : ℕ) (hn : n = 2 * m)
    (t : Fin r → Fin n) :
    shadowL1 (tupleVec n m r t) ≤ r := by
  unfold shadowL1 tupleVec
  calc
    (∑ j : Fin m, (∑ i : Fin r, vecOf n m (t i) j).natAbs)
        ≤ ∑ j : Fin m, ∑ i : Fin r, (vecOf n m (t i) j).natAbs :=
      Finset.sum_le_sum (fun j _ => Int.natAbs_sum_le _ _)
    _ = ∑ i : Fin r, ∑ j : Fin m, (vecOf n m (t i) j).natAbs := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _i : Fin r, 1 :=
      Finset.sum_le_sum (fun i _ => shadowL1_vecOf_le_one hn (t i))
    _ = r := by simp

/-- Difference of two depth-`r` shadows has total `L1` mass at most `2r`. -/
theorem shadowL1_difference_le_two_mul_r (n m r : ℕ) (hn : n = 2 * m)
    (t u : Fin r → Fin n) :
    shadowL1 (shadowDifference (tupleVec n m r t, tupleVec n m r u)) ≤ 2 * r := by
  unfold shadowL1 shadowDifference
  calc
    (∑ j : Fin m, (tupleVec n m r u j - tupleVec n m r t j).natAbs)
        ≤ ∑ j : Fin m,
            ((tupleVec n m r u j).natAbs + (tupleVec n m r t j).natAbs) :=
      Finset.sum_le_sum (fun j _ => Int.natAbs_sub_le _ _)
    _ = shadowL1 (tupleVec n m r u) + shadowL1 (tupleVec n m r t) := by
      rw [Finset.sum_add_distrib]
      rfl
    _ ≤ r + r := add_le_add
      (shadowL1_tupleVec_le_r n m r hn u)
      (shadowL1_tupleVec_le_r n m r hn t)
    _ = 2 * r := by omega

/-- **Sharp realized-relation sparsity:** every R314 kernel relation has `L1 <= 2r`. -/
theorem shadowKernelRelation_l1_le_two_mul_r
    (g : F) (n m r : ℕ) (hn : n = 2 * m) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g n m r) :
    shadowL1 d ≤ 2 * r := by
  classical
  rw [shadowKernelRelations, Finset.mem_image] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  have hoff := (Finset.mem_filter.mp hp).1
  have hp1 : p.1 ∈ keysR n m r := (Finset.mem_offDiag.mp hoff).1
  have hp2 : p.2 ∈ keysR n m r := (Finset.mem_offDiag.mp hoff).2.1
  rw [keysR, Finset.mem_image] at hp1 hp2
  obtain ⟨t, _ht, ht⟩ := hp1
  obtain ⟨u, _hu, hu⟩ := hp2
  simpa [shadowDifference, ht, hu] using
    shadowL1_difference_le_two_mul_r n m r hn t u

/-- Support cardinality is bounded by integer `L1` mass. -/
theorem shadowSupport_card_le_l1 {m : ℕ} (v : Fin m → ℤ) :
    (shadowSupport v).card ≤ shadowL1 v := by
  unfold shadowSupport shadowL1
  calc
    (Finset.univ.filter (fun j : Fin m => v j ≠ 0)).card
        = ∑ j ∈ Finset.univ.filter (fun j : Fin m => v j ≠ 0), 1 := by simp
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m => v j ≠ 0), (v j).natAbs := by
      exact Finset.sum_le_sum (fun j hj => Int.natAbs_pos.mpr (Finset.mem_filter.mp hj).2)
    _ ≤ ∑ j : Fin m, (v j).natAbs := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Every realized kernel relation is supported on at most `2r` coordinates. -/
theorem shadowKernelRelation_support_card_le_two_mul_r
    (g : F) (n m r : ℕ) (hn : n = 2 * m) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g n m r) :
    (shadowSupport d).card ≤ 2 * r :=
  le_trans (shadowSupport_card_le_l1 d)
    (shadowKernelRelation_l1_le_two_mul_r g n m r hn hd)

/-- The represented relation polynomial has exactly the same coefficient `L1` mass as its
vector on the degree-`<m` range. -/
theorem relationPoly_l1_eq_shadowL1 {m : ℕ} (d : Fin m → ℤ) :
    (∑ i ∈ Finset.range m, ((relationPoly d).coeff i).natAbs) = shadowL1 d := by
  rw [shadowL1, Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  let j : Fin m := ⟨i, Finset.mem_range.mp hi⟩
  have hcoeff := relationPoly_coeff_fin d j
  simpa [j, Finset.mem_range.mp hi] using congrArg Int.natAbs hcoeff

/-- Polynomial-facing form of the sharp sparsity theorem. -/
theorem realized_relationPoly_l1_le_two_mul_r
    (g : F) (n m r : ℕ) (hn : n = 2 * m) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g n m r) :
    (∑ i ∈ Finset.range m, ((relationPoly d).coeff i).natAbs) ≤ 2 * r := by
  rw [relationPoly_l1_eq_shadowL1]
  exact shadowKernelRelation_l1_le_two_mul_r g n m r hn hd

end ArkLib.ProximityGap.Frontier.R320KernelRelationL1Sparsity

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R320KernelRelationL1Sparsity.shadowL1_tupleVec_le_r
#print axioms
  ArkLib.ProximityGap.Frontier.R320KernelRelationL1Sparsity.shadowKernelRelation_l1_le_two_mul_r
#print axioms
  ArkLib.ProximityGap.Frontier.R320KernelRelationL1Sparsity.shadowKernelRelation_support_card_le_two_mul_r
#print axioms
  ArkLib.ProximityGap.Frontier.R320KernelRelationL1Sparsity.realized_relationPoly_l1_le_two_mul_r
