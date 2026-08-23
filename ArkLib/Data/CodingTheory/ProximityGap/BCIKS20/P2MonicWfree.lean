/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — monic all-order W-free residual surface

`RestrictedFaaDiBrunoExtract.lean` proves that when `H.leadingCoeff = 1`, every `W` factor on the
recursion side of the partition residual collapses.  This file names the resulting W-free
recursion-side form and packages the corresponding residual equivalences.

This is not a proof of the all-order P2 core: the W-free target still contains the ξ telescope and
the Faà-di-Bruno `B_coeff`/`partitionProd` combinatorics.  It just removes the W-power obstruction
from the statement that future proof bricks should target.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The recursion-side partition form after all `W` powers have been erased.  This is the
all-order monic target left after applying `H.leadingCoeff = 1`; it still carries the ξ telescope
and the `B_coeff`/`partitionProd` combinatorics. -/
def restrictedMatchRecursionPartitionWfreeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    𝕃 H :=
  ClaimA2.ζ R x₀ H
    * ((∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
              * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)))
        / ((embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)))

/-- The named W-free form is exactly the existing monic simplification of the recursion side. -/
theorem restrictedMatchRecursionPartitionForm_eq_WfreeForm_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1) :
    restrictedMatchRecursionPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t := by
  unfold restrictedMatchRecursionPartitionWfreeForm
  exact restrictedMatchRecursionPartitionForm_eq_Wfree_of_leadingCoeff_one
    H x₀ R hHyp t hlc

/-- Under monic `H`, the partition residual is equivalent to the W-free target equation. -/
theorem restrictedPartitionMatchAt_iff_WfreeForm_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t ↔
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoPartitionMatchAt
  rw [restrictedMatchRecursionPartitionForm_eq_WfreeForm_of_leadingCoeff_one
    H x₀ R hHyp t hlc]

/-- Build the partition residual from the W-free target equation under monic `H`. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.of_WfreeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree :
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t :=
  (restrictedPartitionMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc).2 hWfree

/-- Project the W-free target equation from the partition residual under monic `H`. -/
theorem WfreeForm_eq_of_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (restrictedPartitionMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc).1 hpart

/-- Under monic `H`, the carved fixed-order P2 core is equivalent to the W-free target equation. -/
theorem restrictedMatchAt_iff_WfreeForm_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t ↔
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp t).trans
    (restrictedPartitionMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc)

/-- Build the carved fixed-order P2 core from the W-free target equation under monic `H`. -/
theorem RestrictedFaaDiBrunoMatchAt.of_WfreeForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree :
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t :=
  (restrictedMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc).2 hWfree

/-- Project the W-free target equation from the carved fixed-order P2 core under monic `H`. -/
theorem WfreeForm_eq_of_restrictedMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (restrictedMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc).1 hmatch

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionWfreeForm
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionForm_eq_WfreeForm_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_iff_WfreeForm_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.of_WfreeForm
#print axioms BCIKS20.HenselNumerator.WfreeForm_eq_of_partitionMatchAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_iff_WfreeForm_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.of_WfreeForm
#print axioms BCIKS20.HenselNumerator.WfreeForm_eq_of_restrictedMatchAt
