/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — order-zero P2 obstruction as a cleared/uncleared gap

`P2Reabsorb` reduces the fixed order-zero partition residual to the un-cleared representative
over `W ^ R.natDegree`. This companion pins that target to the proven cleared-representative
bridge `hasseEvalAtRoot_mul_W_pow_eq_embedding_cleared`.

The result isolates the remaining order-zero content as equality, in `𝕃`, between the image of
the un-cleared `hasseCoeffRepr𝒪` representative and the image of the cleared representative,
under the explicit degree match plus the same cancellation hypotheses.
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The fixed order-zero normalized P2 residual is equivalent to equality of the un-cleared
iterated-Hasse representative and the proven cleared representative after embedding into `𝕃`.

The hypotheses keep the actual arithmetic obligations explicit: the legitimate `ζ` and `W`
cancellations, plus the Y-degree match between the cleared representative exponent and
`R.natDegree`. This theorem packages the obstruction; it does not prove the cleared/uncleared
embedding equality or the degree match. -/
theorem t0_residual_iff_uncleared_emb_eq_cleared_emb
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) := by
  rw [restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
      H x₀ R hHyp hd hζ]
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hbridge :
      hasseEvalAtRoot H x₀ R 1 0
          * liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) := by
    rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree hdeg.le]
    ring
  constructor
  · intro h
    rw [← hbridge, h, div_mul_cancel₀ _ (pow_ne_zero _ hW)]
  · intro h
    rw [h, ← hbridge, mul_div_assoc, div_self (pow_ne_zero _ hW), mul_one]

/-- Constructor form of `t0_residual_iff_uncleared_emb_eq_cleared_emb`. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_uncleared_emb_eq_cleared_emb
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hgap :
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree))) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (t0_residual_iff_uncleared_emb_eq_cleared_emb H x₀ R hHyp hd hζ hdeg).2 hgap

/-- Projection form of `t0_residual_iff_uncleared_emb_eq_cleared_emb`. -/
theorem uncleared_emb_eq_cleared_emb_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) :=
  (t0_residual_iff_uncleared_emb_eq_cleared_emb H x₀ R hHyp hd hζ hdeg).1 hpart

/-- Variant of `t0_residual_iff_uncleared_emb_eq_cleared_emb` using the nonvanishing packaged in
`ClaimA2.Hypotheses`. -/
theorem t0_residual_iff_uncleared_emb_eq_cleared_emb_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) :=
  t0_residual_iff_uncleared_emb_eq_cleared_emb H x₀ R hHyp hd
    (ζ_ne_zero H x₀ R hHyp) hdeg

/-- Constructor form of `t0_residual_iff_uncleared_emb_eq_cleared_emb_of_hyp`. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_uncleared_emb_eq_cleared_emb_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hgap :
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree))) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (t0_residual_iff_uncleared_emb_eq_cleared_emb_of_hyp H x₀ R hHyp hd hdeg).2 hgap

/-- Projection form of `t0_residual_iff_uncleared_emb_eq_cleared_emb_of_hyp`. -/
theorem uncleared_emb_eq_cleared_emb_of_partitionMatchAt_zero_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) :=
  (t0_residual_iff_uncleared_emb_eq_cleared_emb_of_hyp H x₀ R hHyp hd hdeg).1 hpart

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.t0_residual_iff_uncleared_emb_eq_cleared_emb
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_uncleared_emb_eq_cleared_emb
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.t0_residual_iff_uncleared_emb_eq_cleared_emb_of_hyp
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_uncleared_emb_eq_cleared_emb_of_hyp
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_of_partitionMatchAt_zero_of_hyp
