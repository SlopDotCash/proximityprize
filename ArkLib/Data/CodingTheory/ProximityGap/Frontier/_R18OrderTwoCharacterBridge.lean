/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18FourthMomentTwist
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18QuadraticCurveBridge

/-!
# Round 18: connecting the quartic `MulChar` input to the quadratic curve-count bridge

`_R18FourthMomentTwist` phrases the remaining Weil input as a complex multiplicative-character
complete sum `quadTerm`.  `_R18QuadraticCurveBridge` phrases the Hasse input as a real quadratic
character sum over the quartic root product.  This file supplies the exact algebraic adapter
between those two surfaces.

The hypotheses are intentionally local:

* `hconj : conj(χ a) = χ a`, the order-two / real-valued condition needed to remove conjugates;
* `hχR : χ a = χR a`, a real representative satisfying the quadratic fiber law.

The next target is to discharge those hypotheses from `orderOf χ = 2` and the standard quadratic
character construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

namespace QCB
abbrev quarticRootProduct :=
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.quarticRootProduct (F := F)
abbrev QuadraticFiberLaw :=
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.QuadraticFiberLaw (F := F)
abbrev QuarticDoubleCoverCountInput :=
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.QuarticDoubleCoverCountInput (F := F)
end QCB

namespace FMT
abbrev QuarticWeilInput :=
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput (F := F)
abbrev IsDegenerate :=
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.IsDegenerate (F := F)
end FMT

/-- An order-two complex multiplicative character is fixed by complex conjugation pointwise. -/
theorem conj_apply_of_sq_eq_one (χ : MulChar F ℂ) (hsq : χ ^ 2 = 1) (a : F) :
    conj' (χ a) = χ a := by
  have hinv : χ⁻¹ = χ := by
    calc χ⁻¹ = χ⁻¹ * 1 := by rw [mul_one]
      _ = χ⁻¹ * (χ ^ 2) := by rw [hsq]
      _ = χ := by rw [pow_two, inv_mul_cancel_left]
  rw [show conj' (χ a) = star (χ a) from rfl, MulChar.star_apply', hinv]

/-- If the character is conjugation-invariant, the R18 quadruple sum is the character sum of the
quartic root product. -/
theorem quadTerm_eq_complex_quartic_sum
    (χ : MulChar F ℂ) (z : (F × F) × (F × F))
    (hconj : ∀ a : F, conj' (χ a) = χ a) :
    ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.quadTerm χ z
      = ∑ s : F, χ (QCB.quarticRootProduct z s) := by
  classical
  unfold ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.quadTerm
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hconj (s - z.2.1), hconj (s - z.2.2)]
  change χ (s - z.1.1) * χ (s - z.1.2) * (χ (s - z.2.1) * χ (s - z.2.2))
      = χ ((s - z.1.1) * (s - z.1.2) * ((s - z.2.1) * (s - z.2.2)))
  rw [map_mul, map_mul, map_mul]

/-- Compatibility with a real quadratic representative turns the complex quartic sum into the
complexification of the real quartic sum. -/
theorem complex_quartic_sum_eq_ofReal
    (χ : MulChar F ℂ) (χR : F → ℝ) (z : (F × F) × (F × F))
    (hχR : ∀ a : F, χ a = (χR a : ℂ)) :
    ∑ s : F, χ (QCB.quarticRootProduct z s)
      = ((∑ s : F, χR (QCB.quarticRootProduct z s) : ℝ) : ℂ) := by
  classical
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun s _ => hχR (QCB.quarticRootProduct z s)

/-- A Hasse-style point-count input for the real quadratic representative implies the complex
`quadTerm` bound consumed by `_R18FourthMomentTwist`. -/
theorem norm_quadTerm_le_of_quarticDoubleCoverCountInput
    (χ : MulChar F ℂ) (χR : F → ℝ) (z : (F × F) × (F × F))
    (hconj : ∀ a : F, conj' (χ a) = χ a)
    (hχR : ∀ a : F, χ a = (χR a : ℂ))
    (hfiber : QCB.QuadraticFiberLaw χR)
    (hHasse : QCB.QuarticDoubleCoverCountInput z) :
    ‖ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.quadTerm χ z‖
      ≤ 3 * Real.sqrt (Fintype.card F : ℝ) := by
  rw [quadTerm_eq_complex_quartic_sum χ z hconj, complex_quartic_sum_eq_ofReal χ χR z hχR,
    Complex.norm_real]
  exact
    ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.norm_sum_quadraticChar_quarticRootProduct_le_three_sqrt
      hfiber z hHasse

/-- Same bound with the conjugation-invariance hypothesis discharged by `χ ^ 2 = 1`. -/
theorem norm_quadTerm_le_of_orderTwo_quarticDoubleCoverCountInput
    (χ : MulChar F ℂ) (χR : F → ℝ) (z : (F × F) × (F × F))
    (hsq : χ ^ 2 = 1)
    (hχR : ∀ a : F, χ a = (χR a : ℂ))
    (hfiber : QCB.QuadraticFiberLaw χR)
    (hHasse : QCB.QuarticDoubleCoverCountInput z) :
    ‖ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.quadTerm χ z‖
      ≤ 3 * Real.sqrt (Fintype.card F : ℝ) :=
  norm_quadTerm_le_of_quarticDoubleCoverCountInput χ χR z
    (conj_apply_of_sq_eq_one χ hsq) hχR hfiber hHasse

/-- Produces the `QuarticWeilInput` interface from point-count/Hasse inputs for every
nondegenerate quartic double cover over `G⁴`. -/
theorem quarticWeilInput_of_orderTwo_doubleCoverInputs
    (χ : MulChar F ℂ) (χR : F → ℝ) (G : Finset F)
    (hsq : χ ^ 2 = 1)
    (hχR : ∀ a : F, χ a = (χR a : ℂ))
    (hfiber : QCB.QuadraticFiberLaw χR)
    (hHasse :
      ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ FMT.IsDegenerate z →
        QCB.QuarticDoubleCoverCountInput z) :
    FMT.QuarticWeilInput χ G := by
  intro z hz hnondeg
  exact norm_quadTerm_le_of_orderTwo_quarticDoubleCoverCountInput
    χ χR z hsq hχR hfiber (hHasse z hz hnondeg)

/-- Fourth-moment bound for an order-two character, with the per-quadruple input now phrased as a
quartic double-cover point-count/Hasse estimate. -/
theorem fourthMoment_le_of_orderTwo_doubleCoverInputs
    (χ : MulChar F ℂ) (χR : F → ℝ) (G : Finset F)
    (hsq : χ ^ 2 = 1)
    (hχR : ∀ a : F, χ a = (χR a : ℂ))
    (hfiber : QCB.QuadraticFiberLaw χR)
    (hHasse :
      ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ FMT.IsDegenerate z →
        QCB.QuarticDoubleCoverCountInput z)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F,
        ‖ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ G s‖ ^ 4
      ≤ 6 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) :=
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMoment_le_of_quarticWeilInput
    χ G (quarticWeilInput_of_orderTwo_doubleCoverInputs χ χR G hsq hχR hfiber hHasse) hp

/-- Family-level adapter into `FourthMomentTwistBound` with the Weil input phrased as
order-two real-quadratic double-cover estimates for every character in `X`. -/
theorem fourthMomentTwistBound_of_orderTwo_doubleCoverInputs
    (G : Finset F) (X : Finset (MulChar F ℂ)) (χR : MulChar F ℂ → F → ℝ)
    (hsq : ∀ χ ∈ X, χ ^ 2 = 1)
    (hχR : ∀ χ ∈ X, ∀ a : F, χ a = (χR χ a : ℂ))
    (hfiber : ∀ χ ∈ X, QCB.QuadraticFiberLaw (χR χ))
    (hHasse :
      ∀ χ ∈ X, ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ FMT.IsDegenerate z →
        QCB.QuarticDoubleCoverCountInput z)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X 6 :=
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentTwistBound_of_quarticWeilInput
    G X
    (fun χ hχ =>
      quarticWeilInput_of_orderTwo_doubleCoverInputs χ (χR χ) G (hsq χ hχ)
        (hχR χ hχ) (hfiber χ hχ) (hHasse χ hχ))
    hp

end ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.conj_apply_of_sq_eq_one
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.quadTerm_eq_complex_quartic_sum
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.complex_quartic_sum_eq_ofReal
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.norm_quadTerm_le_of_quarticDoubleCoverCountInput
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.norm_quadTerm_le_of_orderTwo_quarticDoubleCoverCountInput
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.quarticWeilInput_of_orderTwo_doubleCoverInputs
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.fourthMoment_le_of_orderTwo_doubleCoverInputs
#print axioms
  ArkLib.ProximityGap.Frontier.R18OrderTwoCharacterBridge.fourthMomentTwistBound_of_orderTwo_doubleCoverInputs
