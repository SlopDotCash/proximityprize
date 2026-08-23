/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeGlobal

/-!
# BCIKS20 Appendix A.4 — monic W-free endpoint consumers

`P2MonicWfreeGlobal.lean` packages the all-order W-free target left after the monic hypothesis
removes the `W`-power obstruction. This file routes that target into the existing P2 endpoint
reductions: truncated-defect cancellation, assembled-root vanishing, the repaired lift identity,
and the packaged `P2_closed` statement.

The W-free equations themselves remain the hard content. These wrappers only say that, once those
equations are supplied under `H.leadingCoeff = 1`, all downstream P2 endpoints consume them
without unpacking the intermediate `RestrictedFaaDiBrunoMatch` proposition.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- A single fixed-order W-free equation implies the corresponding truncated-defect
cancellation under monic `H`. -/
theorem trunc_defect_cancel_assembled_at_of_WfreeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree :
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = 0 :=
  trunc_defect_cancel_assembled_at H x₀ R hHyp t
    (RestrictedFaaDiBrunoMatchAt.of_WfreeForm H x₀ R hHyp t hlc hWfree)

/-- A single fixed-order W-free equation implies the corresponding assembled-root coefficient
vanishing under monic `H`. -/
theorem coeff_succ_eval_βHenselAssembled_of_WfreeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree :
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_βHenselAssembled_of_restrictedMatchAt H x₀ R hHyp t
    (RestrictedFaaDiBrunoMatchAt.of_WfreeForm H x₀ R hHyp t hlc hWfree)

/-- The global W-free predicate implies every truncated-defect cancellation under monic `H`. -/
theorem trunc_defect_cancel_assembled_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = 0 :=
  trunc_defect_cancel_assembled H x₀ R hHyp
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree) t

/-- The global W-free predicate implies every assembled-root successor coefficient vanishes under
monic `H`. -/
theorem coeff_succ_eval_βHenselAssembled_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_βHenselAssembled_of_WfreeForm H x₀ R hHyp t hlc (hWfree t)

/-- The global W-free predicate gives the assembled-series root statement under monic `H`. -/
theorem assembledSeries_isRoot_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  assembledSeries_isRoot_of_match H x₀ R hHyp
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)

/-- The global W-free predicate gives the repaired `βHensel` lift identity under monic `H`. -/
theorem βHensel_lift_identity_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  βHensel_lift_identity_of_match H x₀ R hHyp
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree) t

/-- The global W-free predicate closes the packaged P2 endpoint under monic `H`. -/
theorem P2_closed_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed H x₀ R hHyp
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)

end BCIKS20.HenselNumerator

set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_at_of_WfreeForm
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_WfreeForm
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_of_WfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.assembledSeries_isRoot_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_lift_identity_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.P2_closed_of_WfreeMatch
