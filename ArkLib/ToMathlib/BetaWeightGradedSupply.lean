/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightGradedAssembly
import ArkLib.ToMathlib.BetaInputSupply
import ArkLib.ToMathlib.DiscriminantBadSet

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-- Right-multiplication monotonicity for `WithBot ℕ` weight bounds (local copy of the
private `BetaInputSupply` helper). -/
private theorem withBot_mul_right_le' {a : WithBot ℕ} {c d : ℕ}
    (h : a ≤ (c : WithBot ℕ)) : a * (d : WithBot ℕ) ≤ ((c * d : ℕ) : WithBot ℕ) := by
  have hcd : ((c * d : ℕ) : WithBot ℕ) = (c : WithBot ℕ) * (d : WithBot ℕ) := by
    push_cast; ring
  rw [hcd]
  gcongr

/-- **The graded finite-range `hcardFin` bridge (canonical `Bcoeff`).** A concrete cardinality
bound at the graded budget `(α(2t−1)+A)·d_H` on `[k,T]` yields the exact
`Section5StrictDataFin.hcardFin` field, via `betaRec_weight_le_graded`. -/
theorem hcardFin_of_graded (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {matchingSet : Finset F}
    (hconcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
                * (2 * t - 1)
              + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ)) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH
          (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
        * H.natDegree := by
  intro t hkt htT
  have hwt := betaRec_weight_le_graded x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR t
  have hmul : weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
        * (H.natDegree : WithBot ℕ)
      ≤ ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ) :=
    withBot_mul_right_le' (by simpa using hwt)
  exact lt_of_le_of_lt hmul (hconcreteFin t hkt htT)

section Discriminant

variable [Fintype F] [DecidableEq F]

/-- The graded cardinality budget at index `t`. -/
def gradedCardBudget (dY D dH : ℕ) (t : ℕ) : ℕ :=
  ((dY * (D - dH + 1) + D + (D - dH + 1)) * (2 * t - 1) + (D - dH + 1)) * dH

/-- The graded budget is monotone in `t`. -/
lemma gradedCardBudget_mono (dY D dH : ℕ) {t T : ℕ} (h : t ≤ T) :
    gradedCardBudget dY D dH t ≤ gradedCardBudget dY D dH T := by
  unfold gradedCardBudget
  have h1 : 2 * t - 1 ≤ 2 * T - 1 := by omega
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ h1) _)

/-- **The discriminant-supplied graded cardinality family.** A nonzero discriminant whose
non-vanishing locus lies in the matching set, with the single top-index field-size bound
`gradedCardBudget(T) + natDegree disc < |F|`, yields the whole `[k,T]` graded `hconcreteFin`
family (in `WithBot ℕ`) consumed by `hcardFin_of_graded`. -/
theorem gradedConcreteFin_of_disc {disc : F[X]} (hdisc : disc ≠ 0)
    {matchingSet : Finset F}
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    {dY D dH k T : ℕ}
    (hbig : gradedCardBudget dY D dH T + disc.natDegree < Fintype.card F) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > ((((dY * (D - dH + 1) + D + (D - dH + 1)) * (2 * t - 1)
            + (D - dH + 1)) * dH : ℕ) : WithBot ℕ) := by
  intro t _hkt htT
  have hT : gradedCardBudget dY D dH T < matchingSet.card :=
    ArkLib.Match304.card_matching_gt_of_disc hdisc hcover hbig
  have ht : gradedCardBudget dY D dH t < matchingSet.card :=
    lt_of_le_of_lt (gradedCardBudget_mono dY D dH htT) hT
  have : (gradedCardBudget dY D dH t : WithBot ℕ) < (matchingSet.card : WithBot ℕ) := by
    exact_mod_cast ht
  simpa [gradedCardBudget] using this

end Discriminant

end ArkLib

#print axioms ArkLib.hcardFin_of_graded
#print axioms ArkLib.gradedConcreteFin_of_disc
