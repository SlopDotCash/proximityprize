/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPredecessorGenericSplit
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveWorstCaseIncidence
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilSymmetry

/-!
# Projective structured split at the P1 rate-quarter predecessor

The generic predecessor split only uses the direction row.  Projective
equivariance makes the localization substantially sharper.

At the P1 predecessor, a row is called near when it agrees with a codeword on
more than `A1star = 327272220` coordinates.  Equivalently, its quotient class
has a representative supported on at most `746469603` coordinates.  Decoupled
Johnson bounds a stack with a far direction by `909522485` bad scalars.  After
one projective slot is added, this is still

```text
909522486 < N = 1073741824.
```

Consequently every stack whose affine bad count exceeds `N` satisfies two
strict structural conditions:

* its two quotient rows are linearly independent; and
* **every nonzero linear combination of its rows is near the code**.

The second statement follows by rebasing an arbitrary nonzero combination as
the direction row.  The full projective bad-slot count is invariant under this
row mix, while it differs from the affine count by at most one.  Thus any far
projective direction would force the original affine count below `N`.

This bypasses source-pencil extraction entirely.  The remaining residual is a
rank-two quotient pencil all of whose projective points have a sparse coset
representative, a smaller coefficient-rank / interpolation target than the
one-sided `PredecessorStructuredFloorResidual`.

No residual is discharged here.  All proofs are axiom-clean and `sorry`-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000
set_option maxRecDepth 500000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveStructuredSplit

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.DecoupledJohnson
open ArkLib.ProximityGap.MCAFloorFactorization
open ProximityGap.MCAProjectiveEquivariance
open ProximityGap.ProjectiveWorstCaseIncidence
open ProximityGap.WBPencil
open P1RateQuarterScaleArithmetic
open P1RateQuarterPredecessorGenericSplit

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Exact row-nearness interface -/

/-- The exact decoupled-Johnson count in the P1 far branch. -/
abbrev farCount : Nat := 909522485

/-- The far count after allowing the one projective slot outside an affine chart. -/
abbrev projectiveFarCount : Nat := farCount + 1

/-- Maximum support of the sparse coset representative supplied by strict
`A1star`-nearness. -/
abbrev maxStructuredSupport : Nat := N - (A1star + 1)

theorem maxStructuredSupport_eq : maxStructuredSupport = 746469603 := by
  norm_num [maxStructuredSupport, N, A1star]

theorem projectiveFarCount_eq : projectiveFarCount = 909522486 := by
  rfl

theorem projectiveFarCount_lt_N : projectiveFarCount < N := by
  norm_num [projectiveFarCount, farCount, N]

/-- A row is in the structured regime when some codeword agrees with it on
strictly more than `A1star` coordinates. -/
def PredecessorRowNear (dom : Fin N ↪ F) (v : Fin N → F) : Prop :=
  ∃ c ∈ predecessorCode dom,
    A1star < (Finset.univ.filter (fun i ↦ c i = v i)).card

/-- The support/agreement partition for a codeword translate. -/
theorem support_card_add_agreement_card (u c : Fin N → F) :
    (Finset.univ.filter (fun i ↦ (u - c) i ≠ 0)).card +
      (Finset.univ.filter (fun i ↦ c i = u i)).card = N := by
  have hsupp :
      Finset.univ.filter (fun i ↦ (u - c) i ≠ 0) =
        Finset.univ.filter (fun i ↦ ¬ c i = u i) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, Pi.sub_apply]
    constructor
    · intro hne hcu
      exact hne (by rw [hcu]; simp)
    · intro hne hzero
      exact hne (sub_eq_zero.mp hzero).symm
  rw [hsupp]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (p := fun i ↦ c i = u i)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- Strict nearness is exactly the existence of a coset representative with
support at most `746469603`. -/
theorem rowNear_iff_exists_support_le (dom : Fin N ↪ F) (v : Fin N → F) :
    PredecessorRowNear dom v ↔
      ∃ c ∈ predecessorCode dom,
        (Finset.univ.filter (fun i ↦ (v - c) i ≠ 0)).card ≤
          maxStructuredSupport := by
  constructor
  · rintro ⟨c, hc, hagree⟩
    refine ⟨c, hc, ?_⟩
    have hpartition := support_card_add_agreement_card v c
    norm_num [maxStructuredSupport, N, A1star] at *
    omega
  · rintro ⟨c, hc, hsupp⟩
    refine ⟨c, hc, ?_⟩
    have hpartition := support_card_add_agreement_card v c
    norm_num [maxStructuredSupport, N, A1star] at *
    omega

/-! ## One-row and two-row localization -/

/-- The exact far branch, restated as a standalone P1 theorem. -/
theorem badCount_le_farCount_of_not_rowNear
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hfar : ¬ PredecessorRowNear dom u₁) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ farCount := by
  have hA : ∀ c ∈ predecessorCode dom,
      (Finset.univ.filter (fun i ↦ c i = u₁ i)).card ≤ A1star := by
    intro c hc
    by_contra hnot
    exact hfar ⟨c, hc, Nat.lt_of_not_ge hnot⟩
  have hbound := mca_badScalars_card_le_div
    (predecessorCode dom) predecessorDelta u₀ u₁
    predecessorThreshold A1star
    (by rw [Fintype.card_fin, agreement_mass_eq_predecessorThreshold])
    hA
    (by simpa only [Fintype.card_fin] using decoupled_gap)
  simpa only [badCount, Fintype.card_fin, far_term_eq, farCount] using hbound

/-- Every affine bad-scalar count is bounded by its projective slot count. -/
theorem badCount_le_badSlotCount
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤
      badSlotCount (F := F) (predecessorCode dom : Set (Fin N → F))
        predecessorDelta u₀ u₁ := by
  rw [badSlotCount_eq_affine_add_infty]
  simp only [badCount]
  omega

/-- A rank-at-most-one quotient pencil has at most one affine bad scalar. -/
theorem badCount_le_one_of_rowsDependentModCode
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hdep : RowsDependentModCode (predecessorCode dom) u₀ u₁) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ 1 := by
  exact (badCount_le_badSlotCount dom u₀ u₁).trans
    (ProjectiveWorstCaseIncidence.badSlotCount_le_one_of_rowsDependentModCode
      (predecessorCode dom) predecessorDelta u₀ u₁ hdep)

/-- If an invertible row mix has a far direction row, the original affine
count is at most the far affine count plus the one missing projective slot. -/
theorem badCount_le_projectiveFarCount_of_rowMix_far
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    {a b c d : F} (hdet : a * d - b * c ≠ 0)
    (hfar : ¬ PredecessorRowNear dom (c • u₀ + d • u₁)) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤
      projectiveFarCount := by
  have hnewAffine := badCount_le_farCount_of_not_rowNear dom
    (a • u₀ + b • u₁) (c • u₀ + d • u₁) hfar
  have hnewProjective :
      badSlotCount (F := F) (predecessorCode dom : Set (Fin N → F)) predecessorDelta
          (a • u₀ + b • u₁) (c • u₀ + d • u₁) ≤
        projectiveFarCount := by
    calc
      badSlotCount (F := F) (predecessorCode dom : Set (Fin N → F)) predecessorDelta
          (a • u₀ + b • u₁) (c • u₀ + d • u₁)
          ≤ badCount (predecessorCode dom) predecessorDelta
              (a • u₀ + b • u₁) (c • u₀ + d • u₁) + 1 := by
            rw [badSlotCount_eq_affine_add_infty]
            simp only [badCount]
            split <;> omega
      _ ≤ farCount + 1 := Nat.add_le_add_right hnewAffine 1
      _ = projectiveFarCount := rfl
  calc
    badCount (predecessorCode dom) predecessorDelta u₀ u₁
        ≤ badSlotCount (F := F) (predecessorCode dom : Set (Fin N → F))
            predecessorDelta u₀ u₁ := badCount_le_badSlotCount dom u₀ u₁
    _ = badSlotCount (F := F) (predecessorCode dom : Set (Fin N → F)) predecessorDelta
          (a • u₀ + b • u₁) (c • u₀ + d • u₁) :=
        (badSlotCount_row_mix (predecessorCode dom) hdet predecessorDelta u₀ u₁).symm
    _ ≤ projectiveFarCount := hnewProjective

/-- If either original row is far, the affine count is already strictly below
`N`.  This is the two-row strengthening of the one-sided floor split. -/
theorem badCount_le_projectiveFarCount_of_not_both_rows_near
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hnot : ¬ (PredecessorRowNear dom u₀ ∧ PredecessorRowNear dom u₁)) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤
      projectiveFarCount := by
  by_cases h₁ : PredecessorRowNear dom u₁
  · have h₀ : ¬ PredecessorRowNear dom u₀ := fun h ↦ hnot ⟨h, h₁⟩
    have hswap := badScalars_card_swap_le
      (predecessorCode dom) predecessorDelta u₀ u₁
    have hfar := badCount_le_farCount_of_not_rowNear dom u₁ u₀ h₀
    have hswap' :
        badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤
          badCount (predecessorCode dom) predecessorDelta u₁ u₀ + 1 := by
      simpa only [badCount] using hswap
    have hfarPlus :
        badCount (predecessorCode dom) predecessorDelta u₁ u₀ + 1 ≤
          projectiveFarCount := by
      exact Nat.add_le_add_right hfar 1
    exact hswap'.trans hfarPlus
  · have hfar := badCount_le_farCount_of_not_rowNear dom u₀ u₁ h₁
    have hfar_le : farCount ≤ projectiveFarCount := by
      norm_num [projectiveFarCount, farCount]
    exact hfar.trans hfar_le

/-- Any over-budget stack has both original rows in the near regime. -/
theorem both_rows_near_of_N_lt_badCount
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hover : N < badCount (predecessorCode dom) predecessorDelta u₀ u₁) :
    PredecessorRowNear dom u₀ ∧ PredecessorRowNear dom u₁ := by
  by_contra hnot
  have hcap := badCount_le_projectiveFarCount_of_not_both_rows_near dom u₀ u₁ hnot
  exact (Nat.not_lt_of_ge (hcap.trans projectiveFarCount_lt_N.le)) hover

/-! ## The projective structured split -/

/-- Every nonzero projective combination of the two rows is in the near-code
regime. -/
def PredecessorProjectivelyNear
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) : Prop :=
  ∀ a b : F, (a ≠ 0 ∨ b ≠ 0) →
    PredecessorRowNear dom (a • u₀ + b • u₁)

/-- An over-budget stack is near in every projective direction. -/
theorem projectivelyNear_of_N_lt_badCount
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hover : N < badCount (predecessorCode dom) predecessorDelta u₀ u₁) :
    PredecessorProjectivelyNear dom u₀ u₁ := by
  intro a b hab
  by_contra hfar
  have hcap :
      badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤
        projectiveFarCount := by
    by_cases hb : b = 0
    · subst b
      have ha : a ≠ 0 := by simpa using hab
      apply badCount_le_projectiveFarCount_of_rowMix_far dom u₀ u₁
          (a := 0) (b := 1) (c := a) (d := 0)
      · simpa using ha
      · simpa using hfar
    · apply badCount_le_projectiveFarCount_of_rowMix_far dom u₀ u₁
          (a := 1) (b := 0) (c := a) (d := b)
      · simpa using hb
      · exact hfar
  exact (Nat.not_lt_of_ge (hcap.trans projectiveFarCount_lt_N.le)) hover

/-- An over-budget stack is a genuine rank-two pencil in the quotient. -/
theorem rowsIndependentModCode_of_N_lt_badCount
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hover : N < badCount (predecessorCode dom) predecessorDelta u₀ u₁) :
    RowsIndependentModCode (predecessorCode dom) u₀ u₁ := by
  intro hdep
  have hcap := badCount_le_one_of_rowsDependentModCode dom u₀ u₁ hdep
  have hN : 1 ≤ N := by norm_num [N]
  exact (Nat.not_lt_of_ge (hcap.trans hN)) hover

/-- The exact reduced class left by projective decoupled Johnson. -/
def PredecessorProjectivelyStructuredRankTwo
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) : Prop :=
  RowsIndependentModCode (predecessorCode dom) u₀ u₁ ∧
    PredecessorProjectivelyNear dom u₀ u₁

/-- Every over-budget stack belongs to the reduced rank-two projectively-near
class. -/
theorem projectivelyStructuredRankTwo_of_N_lt_badCount
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hover : N < badCount (predecessorCode dom) predecessorDelta u₀ u₁) :
    PredecessorProjectivelyStructuredRankTwo dom u₀ u₁ :=
  ⟨rowsIndependentModCode_of_N_lt_badCount dom u₀ u₁ hover,
    projectivelyNear_of_N_lt_badCount dom u₀ u₁ hover⟩

/-- Projective nearness supplies the exact sparse representative for every
nonzero row combination. -/
theorem projectivelyNear_exists_support_le
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hnear : PredecessorProjectivelyNear dom u₀ u₁)
    (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ c ∈ predecessorCode dom,
      (Finset.univ.filter
        (fun i ↦ ((a • u₀ + b • u₁) - c) i ≠ 0)).card ≤
          maxStructuredSupport :=
  (rowNear_iff_exists_support_le dom _).mp (hnear a b hab)

/-! ## A smaller residual interface -/

/-- The remaining coefficient-rank/interpolation obligation: only genuine
rank-two quotient pencils that are near in every projective direction need to
be bounded. -/
def ProjectivelyStructuredFloorResidual (dom : Fin N ↪ F) : Prop :=
  ∀ u₀ u₁ : Fin N → F,
    PredecessorProjectivelyStructuredRankTwo dom u₀ u₁ →
      badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ N

/-- The reduced residual gives the uniform predecessor count. -/
theorem all_badCount_le_N_of_projectivelyStructuredFloor
    (dom : Fin N ↪ F) (hres : ProjectivelyStructuredFloorResidual dom)
    (u₀ u₁ : Fin N → F) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ N := by
  by_contra hnot
  have hover : N < badCount (predecessorCode dom) predecessorDelta u₀ u₁ :=
    Nat.lt_of_not_ge hnot
  exact hnot (hres u₀ u₁
    (projectivelyStructuredRankTwo_of_N_lt_badCount dom u₀ u₁ hover))

/-- In particular, the reduced projective residual discharges the original
one-sided structured-floor residual. -/
theorem predecessorStructuredFloorResidual_of_projectivelyStructured
    (dom : Fin N ↪ F) (hres : ProjectivelyStructuredFloorResidual dom) :
    PredecessorStructuredFloorResidual dom := by
  unfold PredecessorStructuredFloorResidual StructuredFloorBound
  intro u₀ u₁ _hnear
  exact all_badCount_le_N_of_projectivelyStructuredFloor dom hres u₀ u₁

/-- The reduced residual is logically equivalent to the uniform count target,
but quantifies only over the projectively structured rank-two class. -/
theorem projectivelyStructuredFloorResidual_iff_uniform_badCount
    (dom : Fin N ↪ F) :
    ProjectivelyStructuredFloorResidual dom ↔
      ∀ u₀ u₁ : Fin N → F,
        badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ N := by
  constructor
  · exact all_badCount_le_N_of_projectivelyStructuredFloor dom
  · intro hall u₀ u₁ _hstructured
    exact hall u₀ u₁

end ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveStructuredSplit

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveStructuredSplit
#print axioms rowNear_iff_exists_support_le
#print axioms badCount_le_farCount_of_not_rowNear
#print axioms badCount_le_one_of_rowsDependentModCode
#print axioms badCount_le_projectiveFarCount_of_rowMix_far
#print axioms projectivelyNear_of_N_lt_badCount
#print axioms rowsIndependentModCode_of_N_lt_badCount
#print axioms projectivelyStructuredRankTwo_of_N_lt_badCount
#print axioms predecessorStructuredFloorResidual_of_projectivelyStructured
