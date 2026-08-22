/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLateNewtonTwoColourPhysicalBridge

/-!
# Johnson mark-boundary variance and its kernel

The physical cancellation in `_BGKLateNewtonTwoColourPhysicalBridge` leaves

* a fresh marked point adjoining an `r`-subset (the fresh part of `U1`), and
* a repeated marked point inside an `(r-1)`-subset (the repeated part of `U2`).

After insertion/erasure these are pointed Boolean-slice layers.  The elementary Johnson
``forget the mark'' operator on one subset fibre is the rank-one map

`f : marks -> R  |->  (i |-> sum_j f(j))`.

This file computes that local up--down spectrum exactly.  The constant mark direction has
eigenvalue `k`, while every zero-sum mark direction has eigenvalue zero.  The exact variance
identity is

`2*k*sum_i f_i^2 = 2*(sum_i f_i)^2 + sum_(i,j) (f_i-f_j)^2`.

Thus forgetting the mark controls only the trivial Johnson component.  There is no finite
inequality bounding the complete pointed energy by the forgotten energy: the vector `(1,-1)` is
an explicit kernel witness.  Consequently the ordinary unpointed slice spectrum alone cannot
prove the production `10.5/12.5` dominant-pair caps.  A successful use of the physical bridge must
also control the phase-dependent marked component created by the repeated weight-three residual.

This is a boundary-operator no-go, not a refutation of production-specific subgroup arithmetic or
of a refined pointed/coloured association scheme.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKLateNewtonJohnsonBoundaryNoGo

open ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance
open ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge

section LocalMarkBoundary

variable {I : Type*} [Fintype I]

/-- Forget the marked coordinate. -/
noncomputable def forgetMark (f : I -> Real) : Real := ∑ i, f i

/-- The local Johnson up--down Gram operator: forget the mark and lift back constantly. -/
noncomputable def markUpDown (f : I -> Real) : I -> Real :=
  fun _ => forgetMark f

/-- Complete pointed energy on one subset fibre. -/
noncomputable def pointedMarkEnergy (f : I -> Real) : Real := ∑ i, f i ^ 2

/-- Energy visible after forgetting the mark. -/
noncomputable def forgottenMarkEnergy (f : I -> Real) : Real := forgetMark f ^ 2

/-- Pairwise mark variation, the component deleted by mark-forgetting. -/
noncomputable def pairwiseMarkVariation (f : I -> Real) : Real :=
  ∑ i, ∑ j, (f i - f j) ^ 2

/-- Exact local Efron--Stein/Johnson variance identity. -/
theorem twice_card_mul_pointedEnergy_eq_forgotten_add_pairwise
    (f : I -> Real) :
    2 * Fintype.card I * pointedMarkEnergy f =
      2 * forgottenMarkEnergy f + pairwiseMarkVariation f := by
  classical
  unfold pointedMarkEnergy forgottenMarkEnergy pairwiseMarkVariation forgetMark
  calc
    2 * (Fintype.card I : Real) * ∑ i, f i ^ 2 =
        2 * (∑ i, f i) ^ 2 +
          (2 * (Fintype.card I : Real) * ∑ i, f i ^ 2 -
            2 * (∑ i, f i) ^ 2) := by ring
    _ = 2 * (∑ i, f i) ^ 2 +
        ∑ i, ∑ j, (f i - f j) ^ 2 := by
      congr 1
      calc
        2 * (Fintype.card I : Real) * ∑ i, f i ^ 2 -
            2 * (∑ i, f i) ^ 2 =
            ∑ i, ∑ j, (f i ^ 2 + f j ^ 2 - 2 * f i * f j) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
        _ = ∑ i, ∑ j, (f i - f j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          ring

/-- Constant mark vectors are the sole visible local eigendirection, with eigenvalue `|I|`. -/
theorem markUpDown_const (c : Real) :
    markUpDown (fun _ : I => c) = fun _ => (Fintype.card I : Real) * c := by
  funext i
  simp [markUpDown, forgetMark]

/-- Every zero-sum marked direction is killed by the local up--down operator. -/
theorem markUpDown_eq_zero_of_forgetMark_eq_zero (f : I -> Real)
    (hf : forgetMark f = 0) :
    markUpDown f = 0 := by
  funext i
  simp [markUpDown, hf]

end LocalMarkBoundary

/-! ## The actual fresh/repeated packet as pointed slice layers -/

section PhysicalPointedLayer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Inserting the fresh mark is exactly the Boolean-slice up map into the pointed next layer. -/
def freshPointedUpEquiv (G : Finset F) (r : Nat) :
    FreshMarkedJoin G r ≃ RepeatedMarkedJoin G (r + 1) := by
  simpa using (repeatedFreshEquiv G (Nat.succ_pos r)).symm

/-- The fresh-`U1` phase after insertion forgets the mark and reads only the containing subset. -/
noncomputable def pointedSubsetSumPhase (G : Finset F) (r : Nat)
    (z : RepeatedMarkedJoin G (r + 1)) : F :=
  ∑ x ∈ z.1.2.1, x.1

/-- The fresh weight-three phase has a mark-dependent `2*x` twist beyond the containing subset
sum. -/
noncomputable def pointedTripleTwistPhase (G : Finset F) (r : Nat)
    (z : RepeatedMarkedJoin G (r + 1)) : F :=
  (∑ x ∈ z.1.2.1, x.1) + 2 * z.1.1.1

/-- Fresh weight one lies entirely in the mark-forgotten Johnson component. -/
theorem freshOnePhase_under_pointedUp (G : Finset F) (r : Nat)
    (z : FreshMarkedJoin G r) :
    pointedSubsetSumPhase G r (freshPointedUpEquiv G r z) =
      freshOnePhase G r z := by
  classical
  unfold freshPointedUpEquiv pointedSubsetSumPhase freshOnePhase
  change (∑ x ∈ insert z.1.1 z.1.2.1, x.1) =
    newtonJoinPhase G 1 r z.1
  rw [Finset.sum_insert z.2]
  unfold newtonJoinPhase
  push_cast
  ring

/-- Fresh weight three is the same pointed up map followed by the nontrivial mark twist. -/
theorem freshThreePhase_under_pointedUp (G : Finset F) (r : Nat)
    (z : FreshMarkedJoin G r) :
    pointedTripleTwistPhase G r (freshPointedUpEquiv G r z) =
      newtonJoinPhase G 3 r z.1 := by
  classical
  unfold freshPointedUpEquiv pointedTripleTwistPhase
  change (∑ x ∈ insert z.1.1 z.1.2.1, x.1) + 2 * z.1.1.1 =
    newtonJoinPhase G 3 r z.1
  rw [Finset.sum_insert z.2]
  unfold newtonJoinPhase
  push_cast
  ring

/-- The exact physical bridge therefore compares an unmarked pointed layer at depth `r+1` with
a mark-twisted pointed layer at depth `r-1`. -/
theorem twoColourPhysicalProfile_eq_pointedBoundaryDifference
    (G : Finset F) {r : Nat} (hr : 1 < r) (y : F) :
    twoColourPhysicalProfile G r y =
      (phaseFiberCount (fun z : FreshMarkedJoin G r =>
          pointedSubsetSumPhase G r (freshPointedUpEquiv G r z)) y : Int) -
        phaseFiberCount (fun z : FreshMarkedJoin G (r - 2) =>
          pointedTripleTwistPhase G (r - 2) (freshPointedUpEquiv G (r - 2) z)) y := by
  rw [twoColourPhysicalProfile_eq_freshOne_sub_freshThree G hr y]
  congr 1
  · apply congrArg (fun phi => (phaseFiberCount phi y : Int))
    funext z
    exact (freshOnePhase_under_pointedUp G r z).symm
  · apply congrArg (fun phi => (phaseFiberCount phi y : Int))
    funext z
    unfold freshThreePhase
    exact (freshThreePhase_under_pointedUp G (r - 2) z).symm

end PhysicalPointedLayer

/-! ## Explicit kernel and no finite comparison -/

/-- The smallest nontrivial standard mark direction. -/
def alternatingTwoMarks : Fin 2 -> Real := ![1, -1]

theorem alternatingTwoMarks_forget : forgetMark alternatingTwoMarks = 0 := by
  norm_num [forgetMark, alternatingTwoMarks, Fin.sum_univ_succ]

theorem alternatingTwoMarks_energy : pointedMarkEnergy alternatingTwoMarks = 2 := by
  norm_num [pointedMarkEnergy, alternatingTwoMarks, Fin.sum_univ_succ]

theorem alternatingTwoMarks_pairwiseVariation :
    pairwiseMarkVariation alternatingTwoMarks = 8 := by
  norm_num [pairwiseMarkVariation, alternatingTwoMarks, Fin.sum_univ_succ]

theorem alternatingTwoMarks_in_upDown_kernel :
    markUpDown alternatingTwoMarks = 0 :=
  markUpDown_eq_zero_of_forgetMark_eq_zero _ alternatingTwoMarks_forget

/-- **No-go.**  No finite scalar can control full pointed energy using only the unpointed
mark-forgetting projection. -/
theorem no_pointedEnergy_le_scalar_forgottenEnergy (C : Real) :
    ¬ (forall f : Fin 2 -> Real,
      pointedMarkEnergy f <= C * forgottenMarkEnergy f) := by
  intro h
  have hw := h alternatingTwoMarks
  rw [alternatingTwoMarks_energy] at hw
  norm_num [forgottenMarkEnergy, alternatingTwoMarks_forget] at hw

/-- In particular neither late production scalar can arise from this projection alone. -/
theorem productionCaps_not_from_markForgetting :
    (¬ (forall f : Fin 2 -> Real,
      pointedMarkEnergy f <= (21 / 2 : Real) * forgottenMarkEnergy f)) /\
    (¬ (forall f : Fin 2 -> Real,
      pointedMarkEnergy f <= (25 / 2 : Real) * forgottenMarkEnergy f)) := by
  exact ⟨no_pointedEnergy_le_scalar_forgottenEnergy _,
    no_pointedEnergy_le_scalar_forgottenEnergy _⟩

/-! ## Axiom audit -/

#print axioms twice_card_mul_pointedEnergy_eq_forgotten_add_pairwise
#print axioms markUpDown_const
#print axioms markUpDown_eq_zero_of_forgetMark_eq_zero
#print axioms freshOnePhase_under_pointedUp
#print axioms freshThreePhase_under_pointedUp
#print axioms twoColourPhysicalProfile_eq_pointedBoundaryDifference
#print axioms alternatingTwoMarks_in_upDown_kernel
#print axioms no_pointedEnergy_le_scalar_forgottenEnergy
#print axioms productionCaps_not_from_markForgetting

end ArkLib.ProximityGap.Frontier.BGKLateNewtonJohnsonBoundaryNoGo
