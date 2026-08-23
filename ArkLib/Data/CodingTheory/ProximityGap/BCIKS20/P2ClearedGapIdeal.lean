/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2ClearedGap
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — cleared gap as the explicit ideal-membership target

This lightweight bridge composes two already-proved order-zero endpoints:

* `P2ClearedGap.lean` identifies the normalized order-zero partition residual with equality between
  the un-cleared and cleared representative embeddings.
* `RestrictedFaaDiBrunoExtract.lean` identifies the same partition residual with the explicit
  `zeroClearingPolyFull - evalX (C x₀) (Δ_X^1 R)` membership in `Ideal.span {H_tilde' H}`.

The result lets downstream callers choose either target surface without manually routing through
`RestrictedFaaDiBrunoPartitionMatchAt ... 0`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Equality of the un-cleared and cleared order-zero representative embeddings is equivalent to
the explicit order-zero ideal membership target. This is just the shared
`RestrictedFaaDiBrunoPartitionMatchAt ... 0` middle proposition packaged away. -/
theorem uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) ↔
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} :=
  (t0_residual_iff_uncleared_emb_eq_cleared_emb H x₀ R hHyp hd hζ hdeg).symm.trans
    (restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_sub_mem H x₀ R hHyp hd)

/-- Project the explicit ideal membership from the cleared/uncleared embedding equality. -/
theorem zeroClearingPolyFull_sub_mem_of_uncleared_emb_eq_cleared_emb
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hgap :
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree))) :
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} :=
  (uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem
    H x₀ R hHyp hd hζ hdeg).1 hgap

/-- Build the cleared/uncleared embedding equality from the explicit ideal membership. -/
theorem uncleared_emb_eq_cleared_emb_of_zeroClearingPolyFull_sub_mem
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hmem :
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H}) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) :=
  (uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem
    H x₀ R hHyp hd hζ hdeg).2 hmem

/-- In the monic regime, the order-zero cleared/uncleared embedding gap closes directly. -/
theorem uncleared_emb_eq_cleared_emb_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hlc : H.leadingCoeff = 1) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) :=
  uncleared_emb_eq_cleared_emb_of_partitionMatchAt_zero H x₀ R hHyp hd hζ hdeg
    (restrictedPartitionMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-- Variant of `uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem` using the
nonvanishing packaged in `ClaimA2.Hypotheses`. -/
theorem uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) ↔
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} :=
  uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem H x₀ R hHyp hd
    (ζ_ne_zero H x₀ R hHyp) hdeg

/-- Project the explicit ideal membership from the cleared/uncleared embedding equality, using the
nonvanishing packaged in `ClaimA2.Hypotheses`. -/
theorem zeroClearingPolyFull_sub_mem_of_uncleared_emb_eq_cleared_emb_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hgap :
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree))) :
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} :=
  (uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem_of_hyp
    H x₀ R hHyp hd hdeg).1 hgap

/-- Build the cleared/uncleared embedding equality from the explicit ideal membership, using the
nonvanishing packaged in `ClaimA2.Hypotheses`. -/
theorem uncleared_emb_eq_cleared_emb_of_zeroClearingPolyFull_sub_mem_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hmem :
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H}) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) :=
  (uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem_of_hyp
    H x₀ R hHyp hd hdeg).2 hmem

/-- In the monic regime, the order-zero cleared/uncleared embedding gap closes directly, using the
nonvanishing packaged in `ClaimA2.Hypotheses`. -/
theorem uncleared_emb_eq_cleared_emb_of_leadingCoeff_one_of_hyp
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree)
    (hlc : H.leadingCoeff = 1) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R 1 0 R.natDegree)) :=
  uncleared_emb_eq_cleared_emb_of_leadingCoeff_one H x₀ R hHyp hd
    (ζ_ne_zero H x₀ R hHyp) hdeg hlc

end BCIKS20.HenselNumerator

set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_sub_mem_of_uncleared_emb_eq_cleared_emb
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_of_zeroClearingPolyFull_sub_mem
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_iff_zeroClearingPolyFull_sub_mem_of_hyp
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_sub_mem_of_uncleared_emb_eq_cleared_emb_of_hyp
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_of_zeroClearingPolyFull_sub_mem_of_hyp
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.uncleared_emb_eq_cleared_emb_of_leadingCoeff_one_of_hyp
