/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry

/-!
# Rate-quarter cross-core scalar identity

A coordinate on the joint core of one decoded polynomial line, but only a
fresh agreement coordinate for a point on another line, reads off that
point's scalar from the difference of the two line pairs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCrossCoreScalar

variable {I F : Type} [Fintype I]
variable [Field F] [DecidableEq F]

/-- **Local cross-core scalar identity.** Let `ci=(ai,ri)` and `cj=(aj,rj)`
be decoded polynomial lines. If `x` is on the joint core of `cj`, a point of
scalar `gamma` on `ci` agrees at `x`, and `x` is not on the joint core of
`ci`, then the slope difference is nonzero at `x` and

`gamma = -(ai-aj)(x) / (ri-rj)(x)`.
-/
theorem slope_diff_ne_zero_and_scalar_eq_of_cross_core
    (dom : I ↪ F) (u0 u1 : I → F)
    (ci cj : F[X] × F[X]) {x : I} {gamma : F}
    (hcorej : x ∈ jointCore dom u0 u1 cj.1 cj.2)
    (hagree : x ∈ fullAgreement dom u0 u1 gamma
      (ci.1 + C gamma * ci.2))
    (hnotcorei : x ∉ jointCore dom u0 u1 ci.1 ci.2) :
    (ci.2 - cj.2).eval (dom x) ≠ 0 ∧
      gamma = -((ci.1 - cj.1).eval (dom x)) /
        ((ci.2 - cj.2).eval (dom x)) := by
  have hcorej' :
      cj.1.eval (dom x) = u0 x ∧ cj.2.eval (dom x) = u1 x := by
    simpa only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and] using hcorej
  have hagree' :
      ci.1.eval (dom x) + gamma * ci.2.eval (dom x) =
        u0 x + gamma * u1 x := by
    simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ, true_and,
      eval_add, eval_mul, eval_C] using hagree
  have hcross :
      ci.1.eval (dom x) + gamma * ci.2.eval (dom x) =
        cj.1.eval (dom x) + gamma * cj.2.eval (dom x) := by
    calc
      ci.1.eval (dom x) + gamma * ci.2.eval (dom x) =
          u0 x + gamma * u1 x := hagree'
      _ = cj.1.eval (dom x) + gamma * cj.2.eval (dom x) := by
        rw [hcorej'.1, hcorej'.2]
  have hrelation :
      (ci.1 - cj.1).eval (dom x) +
          gamma * (ci.2 - cj.2).eval (dom x) = 0 := by
    simp only [eval_sub]
    apply sub_eq_zero.mp
    calc
      (ci.1.eval (dom x) - cj.1.eval (dom x) +
          gamma * (ci.2.eval (dom x) - cj.2.eval (dom x))) - 0 =
        (ci.1.eval (dom x) + gamma * ci.2.eval (dom x)) -
          (cj.1.eval (dom x) + gamma * cj.2.eval (dom x)) := by ring
      _ = 0 := sub_eq_zero.mpr hcross
  have hslope : (ci.2 - cj.2).eval (dom x) ≠ 0 := by
    intro hslopeZero
    have hinterceptZero : (ci.1 - cj.1).eval (dom x) = 0 := by
      simpa only [hslopeZero, mul_zero, add_zero] using hrelation
    apply hnotcorei
    simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · calc
        ci.1.eval (dom x) = cj.1.eval (dom x) := by
          exact sub_eq_zero.mp (by simpa only [eval_sub] using hinterceptZero)
        _ = u0 x := hcorej'.1
    · calc
        ci.2.eval (dom x) = cj.2.eval (dom x) := by
          exact sub_eq_zero.mp (by simpa only [eval_sub] using hslopeZero)
        _ = u1 x := hcorej'.2
  refine ⟨hslope, ?_⟩
  apply (eq_div_iff hslope).mpr
  exact eq_neg_of_add_eq_zero_right hrelation

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCrossCoreScalar

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCrossCoreScalar.slope_diff_ne_zero_and_scalar_eq_of_cross_core
