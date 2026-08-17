/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoXiTelescope
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.FaaDiBrunoBijectionPieces
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FilterDrop
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicOrderZero

/-!
# P2MatchMonic

Module docstring for `P2MatchMonic.lean`.
-/


noncomputable section
open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- monic: `embed ξ = ζ`. -/
theorem embed_ξ_eq_ζ_of_monic (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) = ClaimA2.ζ R x₀ H := by
  rw [ClaimA2.embeddingOf𝒪Into𝕃_ξ, hlc, map_one, one_pow, one_mul]

/-- monic: cleared `hasseEvalAtRoot` equals the embedded un-cleared representative. -/
theorem hasseEvalAtRoot_eq_embed_uncleared_of_monic (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ)
    (hlc : H.leadingCoeff = 1) :
    hasseEvalAtRoot H x₀ R i1 m
      = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]
  unfold hasseEvalAtRoot
  simp only [hlc, map_one, div_one]

/-- RHS monic form: the global `ζ·(embed ξ)⁻¹` collapses to `1`. -/
theorem rhs_monic_form (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1) :
    restrictedMatchRecursionPartitionForm H x₀ R hHyp t
      = ∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
              * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
              / embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)
                  ^ (2 * (t + 1 - i1) - sigmaLambda lam) := by
  rw [restrictedMatchRecursionPartitionForm_eq_ξfree_of_leadingCoeff_one H x₀ R hHyp t hlc]
  rw [show ClaimA2.ζ R x₀ H * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp))⁻¹ = 1 from by
    rw [embed_ξ_eq_ζ_of_monic H x₀ R hHyp hlc, mul_inv_cancel₀ (ζ_ne_zero H x₀ R hHyp)],
    one_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Core per-`(i₁,λ)` inner identity (monic): the LHS Y-degree sum collapses (via `taylorCollapse`)
to the RHS recursion term. -/
theorem lhs_inner_eq_rhs_term (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (t i1 : ℕ) (lam : Nat.Partition (t + 1 - i1)) :
    (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        (liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
        * ((i.choose lam.parts.card * lam.parts.countPerms)
            • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                * (lam.parts.map (fun j =>
                    PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)))
      = embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
          * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
          / embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)
              ^ (2 * (t + 1 - i1) - sigmaLambda lam) := by
  classical
  set s := lam.parts.card with hs
  set P := (lam.parts.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod with
    hP
  have h0 : PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp) = α₀ H :=
    coeff_zero_βHenselAssembled H x₀ R hHyp
  -- mul-form of taylorCollapse
  have hTC : ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
      (((i.choose s : ℕ) : 𝕃 H)
        * ((liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i)) * (α₀ H) ^ (i - s)))
      = hasseEvalAtRoot H x₀ R i1 s := by
    rw [← taylorCollapse H x₀ R i1 s]
    exact Finset.sum_congr rfl (fun i _ => by rw [nsmul_eq_mul])
  -- rewrite the whole LHS sum into `↑cP * P * hasseEvalAtRoot` form
  have hLHS : (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        (liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
        * ((i.choose s * lam.parts.countPerms)
            • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - s) * P)))
      = ((lam.parts.countPerms : ℕ) : 𝕃 H) * P * hasseEvalAtRoot H x₀ R i1 s := by
    rw [← hTC, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h0, nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hLHS]
  -- P value (monic)
  have hPval : P = embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
      / embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * (t + 1 - i1) - sigmaLambda lam) := by
    rw [hP, show (lam.parts.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod
          = partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp)) from
            rfl,
      partitionProd_coeff_assembled, hlc, map_one, one_pow, one_mul, sum_map_two_mul_sub_one]
  rw [hPval, hasseEvalAtRoot_eq_embed_uncleared_of_monic H x₀ R i1 s hlc,
    B_coeff_eq_countPerms_smul, map_nsmul, nsmul_eq_mul]
  simp only [sigmaLambda, ← hs]
  ring

set_option maxHeartbeats 1000000 in
/-- **The monic BCIKS20 A.4 partition match, all orders.** -/
theorem partitionMatchAt_monic (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t := by
  classical
  unfold RestrictedFaaDiBrunoPartitionMatchAt
  rw [restrictedFaaDiBrunoPartitionForm_eq_rangeForm H x₀ R hHyp t,
    rhs_monic_form H x₀ R hHyp t hlc, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  rw [depSwap H
        (fun i => liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
        (fun i lam => ((i.choose lam.parts.card * lam.parts.countPerms)
            • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                * (lam.parts.map (fun j =>
                    PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)))
        (fun lam => (t + 1) ∉ lam.parts)]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [show (∑ i ∈ (Finset.range ((Q x₀ R H).natDegree + 1)).filter
              (fun i => lam.parts.card ≤ i),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
            * ((i.choose lam.parts.card * lam.parts.countPerms)
                • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                    * (lam.parts.map (fun j =>
                        PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)))
          = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
            * ((i.choose lam.parts.card * lam.parts.countPerms)
                • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                    * (lam.parts.map (fun j =>
                        PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))
        from Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hni => by
          have hlt : i < lam.parts.card := by
            simp only [Finset.mem_filter, Finset.mem_range, not_and, not_le] at hni
            exact hni (Finset.mem_range.mp hi)
          rw [Nat.choose_eq_zero_of_lt hlt]; simp)]
  exact lhs_inner_eq_rhs_term H x₀ R hHyp hlc t i1 lam

set_option maxHeartbeats 1000000 in
/-- **The monic BCIKS20 A.4 restricted Faà-di-Bruno match, all orders (axiom-clean).** -/
theorem restrictedFaaDiBrunoMatch_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp := fun t =>
  RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp t
    (partitionMatchAt_monic H x₀ R hHyp hlc t)

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoMatch_of_monic
