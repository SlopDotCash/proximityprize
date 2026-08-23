/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.FaaDiBrunoBijectionPieces
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeFullSumAt

/-!
# BCIKS20 Appendix A.4 — range-indexed monic W-free target

`FaaDiBrunoBijectionPieces.lean` proves that the partition-form side of the fixed-order
restricted Faa-di-Bruno match can be rewritten from an antidiagonal outer index to the same
`i₁ ∈ range (t + 2)` outer index used by the recursion side. This file names that range-indexed
left-hand side and packages the corresponding W-free target.

The result is a same-outer-index target for the remaining monic P2 proof: after the outer reindex
has been applied, the fixed-order full-sum zero / carved residual / W-free equation are all
equivalent to the range-indexed W-free equation under `H.leadingCoeff = 1`.
-/

noncomputable section

open scoped BigOperators Nat
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The partition-form LHS after the outer antidiagonal index has been rewritten to
`i₁ ∈ range (t + 2)`. -/
def restrictedFaaDiBrunoPartitionRangeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) : 𝕃 H :=
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    ∑ i1 ∈ Finset.range (t + 2),
      (liftToFunctionField (H := H)
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
      * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                  (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
          ((i.choose lam.parts.card) * lam.parts.countPerms)
            • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                * (lam.parts.map (fun j =>
                    PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)

/-- The range-indexed form is exactly the existing partition-form LHS. -/
theorem restrictedFaaDiBrunoPartitionForm_eq_partitionRangeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedFaaDiBrunoPartitionRangeForm H x₀ R hHyp t := by
  rw [restrictedFaaDiBrunoPartitionRangeForm]
  exact restrictedFaaDiBrunoPartitionForm_eq_rangeForm H x₀ R hHyp t

/-- Fixed-order range-indexed W-free target.  This is the monic W-free equation after the
left-hand side has been reindexed over the same outer range as the recursion side. -/
def RestrictedFaaDiBrunoRangeWfreeMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) : Prop :=
  restrictedFaaDiBrunoPartitionRangeForm H x₀ R hHyp t =
    restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t

/-- All-order range-indexed W-free target. -/
def RestrictedFaaDiBrunoRangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t

/-- The global range-indexed target is just the family of its fixed-order equations. -/
theorem restrictedFaaDiBrunoRangeWfreeMatch_iff_forall_at
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp ↔
      ∀ t : ℕ, RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  Iff.rfl

/-- Project one fixed-order range-indexed equation from the global range-indexed target. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatch.at
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) (t : ℕ) :
    RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  hrange t

/-- Build the global range-indexed target from fixed-order range-indexed equations. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatch.of_forallAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp :=
  hat

/-- The fixed W-free equation is equivalent to its range-indexed version. -/
theorem WfreeForm_iff_rangeWfreeMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) :
    (restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) ↔
      RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoRangeWfreeMatchAt
  rw [restrictedFaaDiBrunoPartitionForm_eq_partitionRangeForm]

/-- Build the range-indexed target from the original fixed W-free equation. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatchAt.of_WfreeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hWfree :
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) :
    RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  (WfreeForm_iff_rangeWfreeMatchAt H x₀ R hHyp t).1 hWfree

/-- Project the original fixed W-free equation from the range-indexed target. -/
theorem WfreeForm_eq_of_rangeWfreeMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (WfreeForm_iff_rangeWfreeMatchAt H x₀ R hHyp t).2 hrange

/-- Under monic `H`, the fixed carved residual is equivalent to the range-indexed W-free target. -/
theorem restrictedMatchAt_iff_rangeWfreeMatchAt_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t ↔
      RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  (restrictedMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc).trans
    (WfreeForm_iff_rangeWfreeMatchAt H x₀ R hHyp t)

/-- Build the range-indexed W-free target from the fixed carved residual under monic `H`. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatchAt.of_restrictedMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  (restrictedMatchAt_iff_rangeWfreeMatchAt_of_leadingCoeff_one
    H x₀ R hHyp t hlc).1 hmatch

/-- Project the fixed carved residual from the range-indexed target under monic `H`. -/
theorem RestrictedFaaDiBrunoMatchAt.of_rangeWfreeMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t :=
  (restrictedMatchAt_iff_rangeWfreeMatchAt_of_leadingCoeff_one
    H x₀ R hHyp t hlc).2 hrange

/-- Under monic `H`, a fixed full-sum zero is equivalent to the range-indexed W-free target. -/
theorem faaDiBrunoFullSum_succ_eq_zero_iff_rangeWfreeMatchAt_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0 ↔
      RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_WfreeForm_of_leadingCoeff_one
    H x₀ R hHyp t hlc).trans
      (WfreeForm_iff_rangeWfreeMatchAt H x₀ R hHyp t)

/-- Build the range-indexed target from a fixed full-sum zero under monic `H`. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatchAt.of_fullSumZero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1)
    (hzero : faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0) :
    RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_rangeWfreeMatchAt_of_leadingCoeff_one
    H x₀ R hHyp t hlc).1 hzero

/-- Project a fixed full-sum zero from the range-indexed target under monic `H`. -/
theorem fullSumZero_of_rangeWfreeMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0 :=
  (faaDiBrunoFullSum_succ_eq_zero_iff_rangeWfreeMatchAt_of_leadingCoeff_one
    H x₀ R hHyp t hlc).2 hrange

/-- The global W-free predicate is equivalent to the global range-indexed target. -/
theorem WfreeMatch_iff_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp ↔
      RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp := by
  rw [restrictedFaaDiBrunoWfreeMatch_iff_forall_at,
    restrictedFaaDiBrunoRangeWfreeMatch_iff_forall_at]
  exact forall_congr' fun t => WfreeForm_iff_rangeWfreeMatchAt H x₀ R hHyp t

/-- Build the global range-indexed target from the global W-free predicate. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatch.of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp :=
  (WfreeMatch_iff_rangeWfreeMatch H x₀ R hHyp).1 hWfree

/-- The proved monic carved match supplies the global range-indexed W-free target directly. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatch.of_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp :=
  RestrictedFaaDiBrunoRangeWfreeMatch.of_WfreeMatch H x₀ R hHyp
    (RestrictedFaaDiBrunoWfreeMatch.of_monic H x₀ R hHyp hlc)

/-- The proved monic carved match supplies each fixed range-indexed W-free equation directly. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatchAt.of_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  (RestrictedFaaDiBrunoRangeWfreeMatch.of_monic H x₀ R hHyp hlc) t

/-- Project the global W-free predicate from the global range-indexed target. -/
theorem RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  (WfreeMatch_iff_rangeWfreeMatch H x₀ R hHyp).2 hrange

/-- Under monic `H`, full-sum vanishing is equivalent to the global range-indexed W-free target. -/
theorem fullVanishes_iff_rangeWfreeMatch_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp ↔
      RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp :=
  (fullVanishes_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).trans
    (WfreeMatch_iff_rangeWfreeMatch H x₀ R hHyp)

/-- Build the global range-indexed target from full-sum vanishing under monic `H`. -/
theorem RestrictedFaaDiBrunoRangeWfreeMatch.of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp :=
  (fullVanishes_iff_rangeWfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).1 hvan

/-- Project full-sum vanishing from the global range-indexed target under monic `H`. -/
theorem FaaDiBrunoFullSumVanishes.of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  (fullVanishes_iff_rangeWfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).2 hrange

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionRangeForm
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionForm_eq_partitionRangeForm
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatchAt
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoRangeWfreeMatch_iff_forall_at
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch.at
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch.of_forallAt
#print axioms BCIKS20.HenselNumerator.WfreeForm_iff_rangeWfreeMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatchAt.of_WfreeForm
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.WfreeForm_eq_of_rangeWfreeMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_iff_rangeWfreeMatchAt_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatchAt.of_restrictedMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.of_rangeWfreeMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.faaDiBrunoFullSum_succ_eq_zero_iff_rangeWfreeMatchAt_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatchAt.of_fullSumZero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.fullSumZero_of_rangeWfreeMatchAt
#print axioms BCIKS20.HenselNumerator.WfreeMatch_iff_rangeWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch.of_WfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch.of_monic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatchAt.of_monic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.fullVanishes_iff_rangeWfreeMatch_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch.of_fullVanishes
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.FaaDiBrunoFullSumVanishes.of_rangeWfreeMatch
