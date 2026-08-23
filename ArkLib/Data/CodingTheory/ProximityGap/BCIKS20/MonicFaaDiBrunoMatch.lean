/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.MonicFaaDiBrunoMatchAlt
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchProof
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.UnclearedEmbedding

/-!
# BCIKS20 Appendix A.4 — monic Faà-di-Bruno match compatibility surface

This module keeps the historical `MonicFaaDiBrunoMatch` import path honest.

The old per-term route attempted to prove that the embedded recursion coefficient `B_coeff`
collapses directly to the cleared root evaluation `hasseEvalAtRoot`. That target is not available
term-by-term: `B_coeff` carries the un-cleared `Y ↦ T` representative
`hasseCoeffRepr𝒪`, while `hasseEvalAtRoot` is the cleared `Y ↦ T / W` evaluation. The nearby
`P2KeystoneReindex` and `UnclearedEmbedding` modules record this obstruction explicitly.

The monic P2 result itself is not lost. It is proved by the bottom-up partition match
`restrictedFaaDiBrunoMatch_of_monic` and the top-down/root endpoints in
`MonicFaaDiBrunoMatchAlt`. This file re-exports small compatibility aliases for those proved
endpoints and avoids reintroducing the false per-term claim.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Compatibility aliases for the proved monic endpoints -/

/-- Compatibility alias for the monic collapse from cleared root evaluation to the genuine
un-cleared coefficient representative. This is the correct replacement for the old attempted
general `B_coeff = countPerms • hasseEvalAtRoot` statement: after `H.leadingCoeff = 1`, the
cleared evaluation equals the embedded un-cleared representative in `𝕃`. -/
theorem hasseEvalAtRoot_eq_embed_uncleared_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) (hlc : H.leadingCoeff = 1) :
    hasseEvalAtRoot H x₀ R i1 m
      = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) :=
  hasseEvalAtRoot_eq_embed_uncleared_of_monic H x₀ R i1 m hlc

/-- Embedded `B_coeff` equals `countPerms • hasseEvalAtRoot` for monic `H`.

This preserves the old monic compatibility surface, but proves it through the valid monic
uncleared-to-cleared collapse instead of the unavailable general cleared-representative route. -/
theorem embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ} (lam : Nat.Partition m)
    (hlc : H.leadingCoeff = 1)
    (_hk : Bivariate.natDegreeY
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R)))
          ≤ R.natDegree - deltaSave i1 - sigmaLambda lam) :
    embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
      = lam.parts.countPerms • hasseEvalAtRoot H x₀ R i1 (sigmaLambda lam) := by
  rw [B_coeff_eq_countPerms_smul, nsmul_eq_mul, map_mul, map_natCast,
    ← hasseEvalAtRoot_eq_embed_uncleared_of_leadingCoeff_one H x₀ R i1 (sigmaLambda lam) hlc,
    nsmul_eq_mul]

/-- LHS per-term coefficient product, monic form. -/
theorem partitionProd_coeff_assembled_of_leadingCoeff_one {m : ℕ}
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (lam : Nat.Partition m) (hlc : H.leadingCoeff = 1) :
    partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp))
      = embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
        / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam) := by
  rw [partitionProd_coeff_assembled H x₀ R hHyp lam,
    liftToFunctionField_leadingCoeff_eq_one_of_leadingCoeff_one H hlc, one_pow, one_mul,
    sum_map_two_mul_sub_one lam, sigmaLambda]

/-- Per-`(i₁, λ)` LHS/RHS term equality for monic `H`.

This is the old monic term-level compatibility theorem, repaired to use the true monic
`hasseEvalAtRoot = embed hasseCoeffRepr𝒪` collapse. -/
theorem lhs_rhs_term_match_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) (hlc : H.leadingCoeff = 1)
    (hk : Bivariate.natDegreeY
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R)))
          ≤ R.natDegree - deltaSave i1 - sigmaLambda lam) :
    lam.parts.countPerms
        • (hasseEvalAtRoot H x₀ R i1 lam.parts.card
            * partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp)))
      = embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
          * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
          / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam) := by
  rw [embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one
      H x₀ R i1 lam hlc hk,
    partitionProd_coeff_assembled_of_leadingCoeff_one H x₀ R hHyp lam hlc]
  -- `σλ = lam.parts.card`, so the two `hasseEvalAtRoot` orders agree.
  show lam.parts.countPerms
      • (hasseEvalAtRoot H x₀ R i1 lam.parts.card
          * (embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
              / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam)))
    = (lam.parts.countPerms • hasseEvalAtRoot H x₀ R i1 (sigmaLambda lam))
        * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
        / (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * m - sigmaLambda lam)
  rw [sigmaLambda, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- Compatibility alias for the proved monic per-`(i₁, λ)` inner identity. -/
theorem lhs_inner_eq_rhs_term_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
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
              ^ (2 * (t + 1 - i1) - sigmaLambda lam) :=
  lhs_inner_eq_rhs_term H x₀ R hHyp hlc t i1 lam

/-- Compatibility alias for the per-order monic partition match. -/
theorem partitionMatchAt_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t :=
  partitionMatchAt_monic H x₀ R hHyp hlc t

/-- Compatibility alias for the all-orders monic restricted Faà-di-Bruno match. -/
theorem restrictedFaaDiBrunoMatch_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc

/-- Compatibility alias for the all-orders full Faà-di-Bruno vanishing theorem in the monic
case. -/
theorem faaDiBrunoFullSumVanishes_of_leadingCoeff_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  faaDiBrunoFullSumVanishes_of_monic H x₀ R hHyp hlc

/-- Compatibility alias for the monic assembled-root endpoint. -/
theorem assembledSeries_isRoot_of_leadingCoeff_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  assembledSeries_isRoot_of_monic H x₀ R hHyp hlc

/-- Compatibility alias for the monic genuine-Hensel-root identification. -/
theorem βHenselAssembled_eq_gammaGenuine_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp :=
  βHenselAssembled_eq_gammaGenuine_of_monic H x₀ R hHyp hlc

/-- Compatibility alias for the monic repaired lift identity. -/
theorem βHensel_lift_identity_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  βHensel_lift_identity_of_monic H x₀ R hHyp hlc t

/-- Compatibility alias for the packaged monic P2 conclusion. -/
theorem P2_closed_topDown_of_leadingCoeff_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed_of_monic H x₀ R hHyp hlc

end BCIKS20.HenselNumerator

-- Axiom audit: the compatibility surface reuses the proven monic endpoints and introduces no
-- `sorryAx`.
namespace BCIKS20.HenselNumerator

#print axioms hasseEvalAtRoot_eq_embed_uncleared_of_leadingCoeff_one
#print axioms embed_B_coeff_eq_countPerms_smul_hasseEvalAtRoot_of_leadingCoeff_one
#print axioms partitionProd_coeff_assembled_of_leadingCoeff_one
#print axioms lhs_rhs_term_match_of_leadingCoeff_one
#print axioms lhs_inner_eq_rhs_term_of_leadingCoeff_one
#print axioms partitionMatchAt_of_leadingCoeff_one
#print axioms restrictedFaaDiBrunoMatch_of_leadingCoeff_one
#print axioms faaDiBrunoFullSumVanishes_of_leadingCoeff_one
#print axioms assembledSeries_isRoot_of_leadingCoeff_one
#print axioms βHenselAssembled_eq_gammaGenuine_of_leadingCoeff_one
#print axioms βHensel_lift_identity_of_leadingCoeff_one
#print axioms P2_closed_topDown_of_leadingCoeff_one

end BCIKS20.HenselNumerator
