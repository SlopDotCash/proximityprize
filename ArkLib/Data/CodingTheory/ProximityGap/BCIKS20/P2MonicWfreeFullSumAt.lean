/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeFullSum

/-!
# BCIKS20 Appendix A.4 — fixed-order monic W-free full-sum interface

`P2MonicWfreeFullSum.lean` exposes the all-orders equivalence between the global W-free
target and `FaaDiBrunoFullSumVanishes` under `H.leadingCoeff = 1`. This file records the
corresponding fixed-order bridge: one full Faa-di-Bruno sum vanishes at order `t + 1` exactly
when the carved fixed-order residual holds, and therefore exactly when the single W-free
equation at order `t` holds in the monic setting.

The result is per-order API plumbing for building the W-free equations one brick at a time; it
does not prove any of those equations.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- A fixed full Faa-di-Bruno sum vanishes exactly when the fixed carved residual holds. -/
theorem faaDiBrunoFullSum_succ_eq_zero_iff_restrictedMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0 ↔
      RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoMatchAt
  rw [faaDiBrunoFullSum_succ_eq]
  constructor
  · intro h
    linear_combination h
  · intro h
    rw [h]
    ring

/-- Build the fixed carved residual from a single full-sum vanishing statement. -/
theorem RestrictedFaaDiBrunoMatchAt.of_fullSumZero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hzero : faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_restrictedMatchAt H x₀ R hHyp t).1 hzero

/-- Project a single full-sum vanishing statement from the fixed carved residual. -/
theorem fullSumZero_of_restrictedMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0 :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_restrictedMatchAt H x₀ R hHyp t).2 hmatch

/-- Under monic `H`, a fixed full-sum zero is equivalent to the fixed W-free equation. -/
theorem faaDiBrunoFullSum_succ_eq_zero_iff_WfreeForm_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0 ↔
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_restrictedMatchAt H x₀ R hHyp t).trans
    (restrictedMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc)

/-- Project the fixed W-free equation from a single full-sum zero under monic `H`. -/
theorem WfreeForm_eq_of_fullSumZero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1)
    (hzero : faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_WfreeForm_of_leadingCoeff_one
    H x₀ R hHyp t hlc).1 hzero

/-- Build a single full-sum zero from the fixed W-free equation under monic `H`. -/
theorem fullSumZero_of_WfreeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1)
    (hWfree :
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0 :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_WfreeForm_of_leadingCoeff_one
    H x₀ R hHyp t hlc).2 hWfree

end BCIKS20.HenselNumerator

set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.faaDiBrunoFullSum_succ_eq_zero_iff_restrictedMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.of_fullSumZero
#print axioms BCIKS20.HenselNumerator.fullSumZero_of_restrictedMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.faaDiBrunoFullSum_succ_eq_zero_iff_WfreeForm_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.WfreeForm_eq_of_fullSumZero
#print axioms BCIKS20.HenselNumerator.fullSumZero_of_WfreeForm
