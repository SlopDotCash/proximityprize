/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightInductionExcl
import ArkLib.ToMathlib.GradedHteleArith
import ArkLib.ToMathlib.BetaWeightCollapse
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.BCoeffVanishing

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-- Base case: the weight of `mk X` is at most `A = D − d_H + 1`. -/
lemma weight_mk_X_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (hdHD : H.natDegree ≤ D) :
    weight_Λ_over_𝒪 hH
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H) D
      ≤ (WithBot.some (D - H.natDegree + 1) : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_le_of_mk_eq hD hH (r := (Polynomial.X : F[X][Y])) rfl).trans ?_
  rw [weight_Λ_le_iff]
  intro n hn
  rw [Polynomial.mem_support_iff, Polynomial.coeff_X] at hn
  by_cases h1 : n = 1
  · subst h1
    simp only [Polynomial.coeff_X_one, Polynomial.natDegree_one, one_mul, add_zero]
    have : Bivariate.natDegreeY H = H.natDegree := rfl
    omega
  · rw [if_neg (fun h => h1 h.symm)] at hn
    exact absurd rfl hn

/-- The per-part budget sum expands: `Σ count·(α(2l−1)+β) = α(2m−σ)+βσ`. -/
lemma partsCount_affine_sum {m : ℕ} (p : Nat.Partition m) (α β : ℕ) :
    ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * (α * (2 * l.1 - 1) + β)
      = α * (2 * m - Multiset.card p.parts) + β * Multiset.card p.parts := by
  classical
  have hdist : ∀ l ∈ p.parts.toFinset.attach,
      p.parts.count l.1 * (α * (2 * l.1 - 1) + β)
        = α * (p.parts.count l.1 * (2 * l.1 - 1)) + β * p.parts.count l.1 := by
    intro l _; ring
  rw [Finset.sum_congr rfl hdist, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    betaRec_partsCount_two_mul_sub p, betaRec_partsCount_smul_card p]

/-- **The graded weight theorem (the canonical-Bcoeff assembly).** Under monicity, the Y-degree
condition, and the paper grading `hR`, the canonical `betaRec` weights obey the slack budget
`wβ t = α(2t−1)+β` with `α = d·A+D+A`, `β = A`, `A = D−d_H+1`, `d = natDegreeY R`. -/
theorem betaRec_weight_le_graded (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  set d := Bivariate.natDegreeY R with hd
  set A := D - H.natDegree + 1 with hA
  set α := d * A + D + A with hα
  refine betaRec_weight_le_excl x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R)
    hD hH (bW := 0) (bξ := (d - 1) * A)
    (bB := fun i₁ {m} p => (d - Multiset.card p.parts) * A + (D - Multiset.card p.parts))
    (wβ := fun t => α * (2 * t - 1) + A) ?_ ?_ ?_ ?_ ?_
  · -- hbW (monic)
    simpa using
      BCIKS20.HenselNumerator.W𝒪_weight_le_zero_of_monic H hmonic hH hD
  · -- hbξ via weight_ξ_bound
    have h := weight_ξ_bound (H := H) (R := R) x₀ hH hHyp hd2 hD hD_Rx0
    have hbridge : (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)
        = (d - 1) * A := by
      have : Bivariate.natDegreeY H = H.natDegree := rfl
      rw [this, ← hd, ← hA]
    rwa [hbridge] at h
  · -- hbB via B_coeff_weight_le_graded
    intro i₁ m p
    have h := BCIKS20.HenselNumerator.B_coeff_weight_le_graded (H := H) x₀ R i₁ p hH hD hR
    have hbridge : (Bivariate.natDegreeY R - BCIKS20.HenselNumerator.sigmaLambda p)
          * (D + 1 - Bivariate.natDegreeY H)
          + (D - BCIKS20.HenselNumerator.sigmaLambda p)
        = (d - Multiset.card p.parts) * A + (D - Multiset.card p.parts) := by
      have h1 : Bivariate.natDegreeY H = H.natDegree := rfl
      have h2 : BCIKS20.HenselNumerator.sigmaLambda p = Multiset.card p.parts := rfl
      have h3 : D + 1 - H.natDegree = A := by omega
      rw [h1, h2, ← hd, h3]
    rwa [hbridge] at h
  · -- hβ0: weight(mk X) ≤ wβ 0 = α·0 + A = A
    have h := weight_mk_X_le (H := H) hD hH hdHD
    simpa [← hA] using h
  · -- htele (non-forbidden)
    intro s i₁ hi₁ p hexcl
    have hi₁' : i₁ < s + 2 := Finset.mem_range.mp hi₁
    beta_reduce
    rw [partsCount_affine_sum p α A, mul_zero, zero_add,
      show betaξExp i₁ p = 2 * i₁ + Multiset.card p.parts - 2 from rfl]
    set σ := Multiset.card p.parts with hσ
    -- cases on σ
    rcases Nat.eq_zero_or_pos σ with hσ0 | hσ1
    · -- empty partition: m = 0, i₁ = s+1
      have hcard0 : Multiset.card p.parts = 0 := by rw [← hσ]; exact hσ0
      have hp0 : p.parts = 0 := Multiset.card_eq_zero.mp hcard0
      have hm0 : s + 1 - i₁ = 0 := by
        have hps := p.parts_sum
        rw [hp0] at hps
        simp at hps
        omega
      have hi : i₁ = s + 1 := by omega
      rw [hσ0, hm0]
      simp only [Nat.sub_zero, Nat.mul_zero, mul_zero, add_zero]
      rw [show 2 * i₁ - 2 = 2 * s from by omega]
      have hstep : 2 * s * ((d - 1) * A) ≤ 2 * s * (d * A) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right A (Nat.sub_le d 1))
      -- direct: LHS ≤ 2s(dA) + dA + D ≤ α(2s+1)+A  since α = dA+D+A ≥ dA and α·2s ≥ 2s·dA
      have h1 : 2 * s * ((d - 1) * A) + (d * A + D) ≤ α * (2 * s) + α := by
        have hα_ge : d * A ≤ α := by rw [hα]; omega
        have h2 : 2 * s * ((d - 1) * A) ≤ α * (2 * s) := by
          calc 2 * s * ((d - 1) * A) ≤ 2 * s * (d * A) := hstep
            _ ≤ 2 * s * α := Nat.mul_le_mul_left _ hα_ge
            _ = α * (2 * s) := Nat.mul_comm _ _
        have h3 : d * A + D ≤ α := by rw [hα]; omega
        omega
      calc 2 * s * ((d - 1) * A) + (d * A + D)
          ≤ α * (2 * s) + α := h1
        _ = α * (2 * s + 1) := by ring
        _ ≤ α * (2 * (s + 1) - 1) + A := by
            have : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
            rw [this]
            omega
    · -- σ ≥ 1: bridge forbidden to (i₁=0 ∧ σ=1), then graded_htele_arith
      have hexcl' : ¬(i₁ = 0 ∧ σ = 1) := by
        rintro ⟨hi0, hσ1'⟩
        apply hexcl
        refine ⟨hi0, ?_⟩
        obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp (hσ ▸ hσ1')
        have hsum := p.parts_sum
        rw [ha] at hsum ⊢
        simp at hsum
        rw [hsum]
        subst hi0
        norm_num
      have harith := GradedHtele.graded_htele_arith d D H.natDegree
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)) (by omega) hdHD
        i₁ σ hσ1 hexcl'
      -- combine: arith gives LHS_abs ≤ α·(2i₁+σ−1)+A; add α(2m−σ) to both sides;
      -- note (2i₁+σ−1) + (2m−σ) = 2s+1 (m = s+1−i₁, σ ≤ m... need σ ≤ 2m? actually 2m−σ trunc)
      have hσm : σ ≤ s + 1 - i₁ := by
        rw [hσ]
        exact betaRec_card_le p
      have hkey : 2 * i₁ + σ - 1 + (2 * (s + 1 - i₁) - σ) = 2 * s + 1 := by omega
      have hAσ : (D - H.natDegree + 1) * σ = A * σ := by rw [hA]
      -- final arithmetic
      have := Nat.add_le_add_right harith (α * (2 * (s + 1 - i₁) - σ))
      calc (2 * i₁ + σ - 2) * ((d - 1) * A)
            + ((d - σ) * A + (D - σ))
            + (α * (2 * (s + 1 - i₁) - σ) + A * σ)
          = ((2 * i₁ + σ - 2) * ((d - 1) * (D - H.natDegree + 1))
              + ((d - σ) * (D - H.natDegree + 1) + (D - σ))
              + (D - H.natDegree + 1) * σ) + α * (2 * (s + 1 - i₁) - σ) := by
            rw [← hA]; ring
        _ ≤ ((d * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)) * (2 * i₁ + σ - 1)
              + (D - H.natDegree + 1)) + α * (2 * (s + 1 - i₁) - σ) := Nat.add_le_add_right harith _
        _ = α * (2 * i₁ + σ - 1) + α * (2 * (s + 1 - i₁) - σ) + A := by rw [hα, hA]; ring
        _ = α * ((2 * i₁ + σ - 1) + (2 * (s + 1 - i₁) - σ)) + A := by ring
        _ = α * (2 * s + 1) + A := by rw [hkey]
        _ = α * (2 * (s + 1) - 1) + A := by rw [show (2 * (s + 1) - 1 : ℕ) = 2 * s + 1 from by omega]

end ArkLib

#print axioms ArkLib.betaRec_weight_le_graded
