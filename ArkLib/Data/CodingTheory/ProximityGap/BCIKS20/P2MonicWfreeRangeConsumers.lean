/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeConsumers
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeRange

/-!
# BCIKS20 Appendix A.4 — range-indexed W-free endpoint consumers

`P2MonicWfreeRange.lean` names the range-indexed W-free target obtained after the outer
Faà-di-Bruno reindex.  This file routes that same target into the existing P2 endpoint reductions:
truncated-defect cancellation, assembled-root vanishing, the repaired `βHensel` lift identity, and
the packaged `P2_closed` statement.

The range-indexed equations remain the hard content.  These wrappers only make the downstream
P2 consumers accept the range-indexed target directly, without first manually converting it back
to `RestrictedFaaDiBrunoWfreeMatch` or `RestrictedFaaDiBrunoMatch`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Build the carved all-order P2 residual from the global range-indexed W-free target under
monic `H`. -/
theorem RestrictedFaaDiBrunoMatch.of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

/-- Build the legacy successor-sum residual from the global range-indexed W-free target under
monic `H`. -/
theorem FaaDiBrunoSuccSumZeroResidual.of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  FaaDiBrunoSuccSumZeroResidual.of_WfreeMatch H x₀ R hHyp hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

/-- A single fixed-order range-indexed W-free equation implies the corresponding
truncated-defect cancellation under monic `H`. -/
theorem trunc_defect_cancel_assembled_at_of_rangeWfreeMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = 0 :=
  trunc_defect_cancel_assembled_at H x₀ R hHyp t
    (RestrictedFaaDiBrunoMatchAt.of_rangeWfreeMatchAt H x₀ R hHyp t hlc hrange)

/-- A single fixed-order range-indexed W-free equation implies the corresponding assembled-root
coefficient vanishing under monic `H`. -/
theorem coeff_succ_eval_βHenselAssembled_of_rangeWfreeMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_βHenselAssembled_of_restrictedMatchAt H x₀ R hHyp t
    (RestrictedFaaDiBrunoMatchAt.of_rangeWfreeMatchAt H x₀ R hHyp t hlc hrange)

/-- The global range-indexed W-free predicate implies every truncated-defect cancellation under
monic `H`. -/
theorem trunc_defect_cancel_assembled_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = 0 :=
  trunc_defect_cancel_assembled_at_of_rangeWfreeMatchAt H x₀ R hHyp t hlc (hrange t)

/-- The global range-indexed W-free predicate implies every assembled-root successor coefficient
vanishes under monic `H`. -/
theorem coeff_succ_eval_βHenselAssembled_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_βHenselAssembled_of_rangeWfreeMatchAt H x₀ R hHyp t hlc (hrange t)

/-- The global range-indexed W-free predicate gives the assembled-series root statement under
monic `H`. -/
theorem assembledSeries_isRoot_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  assembledSeries_isRoot_of_WfreeMatch H x₀ R hHyp hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

/-- The global range-indexed W-free predicate gives the repaired `βHensel` lift identity under
monic `H`. -/
theorem βHensel_lift_identity_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  βHensel_lift_identity_of_WfreeMatch H x₀ R hHyp hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange) t

/-- The global range-indexed W-free predicate closes the packaged P2 endpoint under monic `H`. -/
theorem P2_closed_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed_of_WfreeMatch H x₀ R hHyp hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

end BCIKS20.HenselNumerator

set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch.of_rangeWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.FaaDiBrunoSuccSumZeroResidual.of_rangeWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_at_of_rangeWfreeMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_rangeWfreeMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_of_rangeWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.assembledSeries_isRoot_of_rangeWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.βHensel_lift_identity_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.P2_closed_of_rangeWfreeMatch
