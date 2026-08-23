/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R38SexticVarietyInput

/-!
# LANE B2 (#466 round 49): zero-lag sextic diagonal from pointwise envelopes

Round 38 splits the final sextic input into:

* nonzero-lag sextic variety cancellation,
* an explicit `t = 0` zero-lag budget.

This brick discharges the last item from elementary pointwise envelopes.  If all triple twisted
weights are bounded by `T`, and the zero-twist character weight `λ_0` is bounded by `L`, then the
zero-lag slice of the R37 complete sum is at most `|G| · q · T² · L`.  Combined with the R38
consumer, this gives the all-lag `SexticCorrelationBound` under a single `max` budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R49SexticZeroLagEnvelope

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The `t = 0` sextic complete sum is controlled by pointwise envelopes for the two triple
weights and for `λ_0`. -/
theorem sextic_zeroLag_bound_of_tripleEnvelope
    {T L : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ a b : ZMod m, ∀ z : F, ‖tripleTwistWeight χ lam a b z‖ ≤ T)
    (hL : ∀ w : F, ‖lam 0 w‖ ≤ L)
    (a b a' b' : ZMod m) :
    ‖∑ u ∈ G, ∑ w : F,
        tripleTwistWeight χ lam a b (u * w)
          * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) * (T ^ 2 * L)) := by
  classical
  have hterm : ∀ u ∈ G, ∀ w : F,
      ‖tripleTwistWeight χ lam a b (u * w)
          * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖
        ≤ T ^ 2 * L := by
    intro u _hu w
    rw [norm_mul, norm_mul]
    have hstar :
        ‖(starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w)‖
          = ‖tripleTwistWeight χ lam a' b' w‖ := by
      simp
    rw [hstar]
    have hmul :
        ‖tripleTwistWeight χ lam a b (u * w)‖
            * ‖tripleTwistWeight χ lam a' b' w‖
          ≤ T * T :=
      mul_le_mul
        (hT a b (u * w))
        (hT a' b' w)
        (norm_nonneg _)
        hT0
    have hmulL :
        ‖tripleTwistWeight χ lam a b (u * w)‖
            * ‖tripleTwistWeight χ lam a' b' w‖ * ‖lam 0 w‖
          ≤ (T * T) * L :=
      mul_le_mul hmul (hL w) (norm_nonneg _) (mul_nonneg hT0 hT0)
    exact hmulL.trans_eq (by ring)
  calc
    ‖∑ u ∈ G, ∑ w : F,
        tripleTwistWeight χ lam a b (u * w)
          * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖
        ≤ ∑ u ∈ G, ‖∑ w : F,
            tripleTwistWeight χ lam a b (u * w)
              * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ _u ∈ G, (Fintype.card F : ℝ) * (T ^ 2 * L) := by
          refine Finset.sum_le_sum (fun u hu => ?_)
          calc
            ‖∑ w : F,
                tripleTwistWeight χ lam a b (u * w)
                  * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖
                ≤ ∑ w : F,
                    ‖tripleTwistWeight χ lam a b (u * w)
                      * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖ :=
                  norm_sum_le _ _
            _ ≤ ∑ _w : F, T ^ 2 * L :=
                  Finset.sum_le_sum (fun w _ => hterm u hu w)
            _ = (Fintype.card F : ℝ) * (T ^ 2 * L) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
                  simp
    _ = (G.card : ℝ) * ((Fintype.card F : ℝ) * (T ^ 2 * L)) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- The R38 consumer with the zero-lag slice supplied by pointwise envelopes and a
single maximum budget. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_envelopes
    {C T L B : ℝ} (hT0 : 0 ≤ T)
    (hweil : SexticVarietyInput χ lam G C)
    (hT : ∀ a b : ZMod m, ∀ z : F, ‖tripleTwistWeight χ lam a b z‖ ≤ T)
    (hL : ∀ w : F, ‖lam 0 w‖ ≤ L)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ) * (T ^ 2 * L))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_zeroLag hweil
    (fun a b a' b' =>
      (sextic_zeroLag_bound_of_tripleEnvelope
        (χ := χ) (lam := lam) (G := G) hT0 hT hL a b a' b').trans
        ((le_max_right _ _).trans hbudget))
    ((le_max_left _ _).trans hbudget)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R49SexticZeroLagEnvelope.sextic_zeroLag_bound_of_tripleEnvelope
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R49SexticZeroLagEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_envelopes

end ArkLib.ProximityGap.Frontier.R49SexticZeroLagEnvelope
