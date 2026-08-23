/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-! # The Sharp Divisibility Obstruction for Non-Monic `H`

The `AlphaGenuineRegularWeightLe` and `DivWeightLe` invariants assert that `W𝒪 ∣ βHensel 0`
in `𝒪 H`. As `W𝒪 = mk (C (lc H))`, this divisibility requires `lc H ∣ X` in `F[X]`.
We prove this impossibility outright, confirming the author's note that the unresummed
invariant is provably false for general non-monic `H`.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]


theorem not_DivWeightLe_zero_of_not_dvd_X (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) (h_not_dvd : ¬ H.leadingCoeff ∣ Polynomial.X) :
    ¬ DivWeightLe_zero H x₀ R hHyp hH D := by
  rintro ⟨a, hEq, _⟩
  have hEq2 : βHensel H x₀ R hHyp 0 = a * W𝒪 H := by simpa using hEq
  rw [βHensel_zero] at hEq2
  set A := canonicalRepOf𝒪 hH a with hA
  have hA_mk : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) A = a := mk_canonicalRepOf𝒪 hH a
  have hW_mk : W𝒪 H = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C H.leadingCoeff) := rfl
  have hmk_eq : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (A * Polynomial.C H.leadingCoeff) := by
    rw [hEq2, ← hA_mk, hW_mk, ← map_mul]
  have hdif : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) ((Polynomial.X : F[X][Y]) - A * Polynomial.C H.leadingCoeff) = 0 := by
    rw [map_sub, hmk_eq, sub_self]
  have hdegX : (Polynomial.X : F[X][Y]).degree < (H_tilde' H).degree := by
    rw [Polynomial.degree_X, Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero, natDegree_H_tilde' hH]
    exact_mod_cast (by omega)
  have hdegA : A.degree < (H_tilde' H).degree := canonicalRepOf𝒪_degree_lt hH a
  have hdegC : (Polynomial.C H.leadingCoeff).degree ≤ 0 := Polynomial.degree_C_le
  have hdegAC : (A * Polynomial.C H.leadingCoeff).degree < (H_tilde' H).degree := by
    refine (Polynomial.degree_mul_le _ _).trans_lt ?_
    have h1 : A.degree + (Polynomial.C H.leadingCoeff).degree ≤ A.degree + 0 := add_le_add_right hdegC _
    have h2 : A.degree + 0 = A.degree := add_zero _
    rw [h2] at h1
    exact lt_of_le_of_lt h1 hdegA
  have hdeg_sub : ((Polynomial.X : F[X][Y]) - A * Polynomial.C H.leadingCoeff).degree < (H_tilde' H).degree := by
    refine (Polynomial.degree_sub_le _ _).trans_lt ?_
    exact max_lt hdegX hdegAC
  have h_eq_zero : (Polynomial.X : F[X][Y]) - A * Polynomial.C H.leadingCoeff = 0 := by
    have h_can := canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hdeg_sub
    rw [hdif, canonicalRepOf𝒪_zero hH] at h_can
    exact h_can.symm
  have h_X_eq : (Polynomial.X : F[X][Y]) = A * Polynomial.C H.leadingCoeff := sub_eq_zero.mp h_eq_zero
  -- (Polynomial.X : F[X][Y]) is actually the variable Y in F[X][Y]
  -- We extract the Y-coefficient of both sides.
  have h_coeff : (Polynomial.X : F[X][Y]).coeff 1 = (A * Polynomial.C H.leadingCoeff).coeff 1 := by rw [h_X_eq]
  rw [Polynomial.coeff_X_one] at h_coeff
  rw [Polynomial.coeff_mul_C, mul_comm] at h_coeff
  have h_div_one : H.leadingCoeff ∣ 1 := ⟨A.coeff 1, h_coeff⟩
  apply h_not_dvd
  exact dvd_trans h_div_one (one_dvd Polynomial.X)

/-! # Positive Case: The Corrected Non-Monic Resummation Target
While `DivWeightLe_zero` is mathematically false because `W𝒪` does not unconditionally divide `βHensel 0`,
we can correctly clear the monic obstruction by universally multiplying the target by `W𝒪 H`.
This provides the corrected base case for the weight induction.
-/

noncomputable def AlphaWeightZeroResummationTarget (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : 𝒪 H :=
  W𝒪 H * βHensel H x₀ R hHyp 0

theorem DivWeightLe_zero_resummed (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) :
    ∃ (a : 𝒪 H), AlphaWeightZeroResummationTarget H x₀ R hHyp = a * W𝒪 H
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 := by
  use βHensel H x₀ R hHyp 0
  constructor
  · rw [AlphaWeightZeroResummationTarget]
    exact mul_comm (W𝒪 H) (βHensel H x₀ R hHyp 0)
  · exact βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD

end BCIKS20.HenselNumerator.AlphaWeight
