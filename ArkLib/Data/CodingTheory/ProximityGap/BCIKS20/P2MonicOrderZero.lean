/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — monic order-zero consumer endpoints

`RestrictedFaaDiBrunoExtract.lean` proves that the carved order-zero P2 residual closes when
`H.leadingCoeff = 1`.  This small companion exposes the downstream order-zero consequences that
callers otherwise have to recover by composing that monic residual through the partition,
reabsorption, coefficient-extraction, and assembled-root APIs by hand.

This file is intentionally order-zero only.  The all-order monic story still leaves the ξ-telescope
and the Faà-di-Bruno combinatorial bijection as the real STEP-8 obstructions.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Monic order-zero closure, projected to the raw surviving power-sum/recursion equality. -/
theorem zeroPowerSum_eq_recursion_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 :=
  zeroPowerSum_eq_recursion_of_partitionMatchAt_zero H x₀ R hHyp
    (restrictedPartitionMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-- Monic order-zero closure, projected to the surviving power-sum/single-`B_coeff` equality. -/
theorem zeroPowerSum_eq_singleBcoeff_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  zeroPowerSum_eq_singleBcoeff_of_partitionMatchAt_zero H x₀ R hHyp
    (restrictedPartitionMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-- Monic order-zero closure, projected to the canonical single-`B_coeff` endpoint. -/
theorem zeroPowerSum_eq_single_B_coeff_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  zeroPowerSum_eq_single_B_coeff_of_partitionMatchAt_zero H x₀ R hHyp
    (restrictedPartitionMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-- Monic order-zero closure, projected to the reabsorbed root-vs-uncleared numerator endpoint. -/
theorem hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hlc : H.leadingCoeff = 1) :
    hasseEvalAtRoot H x₀ R 1 0 =
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree :=
  hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero
    H x₀ R hHyp hd hζ
    (restrictedMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-- Monic order-zero closure, projected to the reabsorbed root-vs-uncleared numerator endpoint,
using the nonvanishing packaged in `ClaimA2.Hypotheses`. -/
theorem hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_leadingCoeff_one_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    hasseEvalAtRoot H x₀ R 1 0 =
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree :=
  hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_leadingCoeff_one
    H x₀ R hHyp hd (ζ_ne_zero H x₀ R hHyp) hlc

/-- Monic order-zero closure, projected to the first assembled numerator coefficient. -/
theorem coeff_one_βHenselAssembled_eq_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
      = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H :=
  coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero H x₀ R hHyp
    (restrictedMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-- Monic order-zero closure, projected to the fixed order-zero trunc-defect cancellation. -/
theorem trunc_defect_cancel_assembled_zero_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    PowerSeries.coeff 1
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp 0) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H
          * PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp) = 0 := by
  simpa using
    trunc_defect_cancel_assembled_of_partitionMatchAt H x₀ R hHyp 0
      (restrictedPartitionMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-- Monic order-zero closure, projected to the first assembled-root coefficient vanishing. -/
theorem coeff_one_eval_βHenselAssembled_eq_zero_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    PowerSeries.coeff 1
      (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 := by
  simpa using
    coeff_succ_eval_βHenselAssembled_of_partitionMatchAt H x₀ R hHyp 0
      (restrictedPartitionMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.zeroPowerSum_eq_recursion_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.zeroPowerSum_eq_singleBcoeff_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.zeroPowerSum_eq_single_B_coeff_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_leadingCoeff_one_of_hyp
#print axioms BCIKS20.HenselNumerator.coeff_one_βHenselAssembled_eq_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_zero_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_one_eval_βHenselAssembled_eq_zero_of_leadingCoeff_one
