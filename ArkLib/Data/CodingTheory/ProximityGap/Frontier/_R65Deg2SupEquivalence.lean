/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18Deg2FaceConverse

/-!
# LANE B2 (#466 round 65): sup-bound equivalence for the deg-2 face

Rounds 17--18 prove the exact quadratic-character bridge and its pointwise converse.  This file
packages the corresponding off-diagonal sup-norm statements: a shifted-Legendre bound for
`W(s) = ∑ y∈G, χ(s-y)` gives an incidence bound for the QR face, and an incidence bound gives
back a shifted-Legendre bound with the exact algebraic loss.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence

open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R18Deg2FaceConverse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Off-diagonal sup control of the shifted quadratic-character sum. -/
def ShiftedLegendreSupBound (χ : F → ℝ) (G : Finset F) (A : ℝ) : Prop :=
  ∀ s : F, s ∉ G → |Wsum χ G s| ≤ A

/-- Off-diagonal sup control of an incidence field.  The QR face is obtained by taking
`H = QRset χ`; keeping `H` explicit avoids fragile decidable-instance choices. -/
def IncidenceSupBound (ψ : AddChar F ℂ) (G H : Finset F) (B : ℝ) : Prop :=
  ∀ s : F, s ∉ G → ‖incidenceSum ψ G H s‖ ≤ B

/-- Forward deg-2 sup bridge: shifted-Legendre cancellation gives QR-incidence cancellation. -/
theorem degTwoIncidenceSupBound_of_shiftedLegendreSupBound
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A) :
    IncidenceSupBound ψ G (QRset χ)
      ((G.card : ℝ) / 2 + (Real.sqrt (Fintype.card F : ℝ) * A) / 2) := by
  intro s hs
  have hbr := bridge hχ hψ G s
  rw [if_neg hs] at hbr
  have hgnorm : ‖gSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
    have h2 := norm_gSum_sq hχ hψ
    have hsqrt : ‖gSum χ ψ‖ = Real.sqrt (‖gSum χ ψ‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    rw [hsqrt, h2]
  have hnorm :
      ‖((-(G.card : ℂ)) + gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ)) / 2‖
        ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * |Wsum χ G s|) / 2 := by
    rw [norm_div, Complex.norm_ofNat]
    have hnum :
        ‖(-(G.card : ℂ)) + gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ)‖
          ≤ (G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * |Wsum χ G s| := by
      calc
        ‖(-(G.card : ℂ)) + gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ)‖
            ≤ ‖(-(G.card : ℂ))‖ + ‖gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ)‖ :=
              norm_add_le _ _
        _ = (G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * |Wsum χ G s| := by
              have hreal : ‖Wsum χ G s‖ = |Wsum χ G s| := by
                exact Real.norm_eq_abs (Wsum χ G s)
              rw [norm_neg, Complex.norm_natCast, norm_mul, hgnorm, Complex.norm_real, hreal]
    exact div_le_div_of_nonneg_right hnum (by norm_num)
  calc
    ‖incidenceSum ψ G (QRset χ) s‖
        = ‖((-(G.card : ℂ)) + gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ)) / 2‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using congrArg norm hbr
    _ ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * |Wsum χ G s|) / 2 := hnorm
    _ ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2 := by
          have hmul :
              Real.sqrt (Fintype.card F : ℝ) * |Wsum χ G s|
                ≤ Real.sqrt (Fintype.card F : ℝ) * A :=
            mul_le_mul_of_nonneg_left (hW s hs) (Real.sqrt_nonneg _)
          have hnum :
              (G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * |Wsum χ G s|
                ≤ (G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A := by
            nlinarith
          exact div_le_div_of_nonneg_right hnum (by norm_num)
    _ = (G.card : ℝ) / 2 + (Real.sqrt (Fintype.card F : ℝ) * A) / 2 := by ring

/-- Converse deg-2 sup bridge: QR-incidence cancellation gives shifted-Legendre cancellation. -/
theorem shiftedLegendreSupBound_of_degTwoIncidenceSupBound
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {B : ℝ}
    (hI : IncidenceSupBound ψ G (QRset χ) B)
    (hq1 : 1 ≤ (Fintype.card F : ℝ)) :
    ShiftedLegendreSupBound χ G
      ((2 * B + (G.card : ℝ)) / Real.sqrt (Fintype.card F : ℝ)) := by
  intro s hs
  have hpoint := abs_W_le_of_incidence hχ hψ G hs hq1
  exact hpoint.trans
    (by
      have hmul :
          2 * ‖incidenceSum ψ G (QRset χ) s‖ ≤ 2 * B :=
        mul_le_mul_of_nonneg_left (hI s hs) (by norm_num)
      have hnum :
          2 * ‖incidenceSum ψ G (QRset χ) s‖ + (G.card : ℝ)
            ≤ 2 * B + (G.card : ℝ) := by
        nlinarith
      exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _))

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence.ShiftedLegendreSupBound
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence.IncidenceSupBound
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence.degTwoIncidenceSupBound_of_shiftedLegendreSupBound
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence.shiftedLegendreSupBound_of_degTwoIncidenceSupBound

end ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
