/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.DescendedRset

/-!
# Descended Claim 5.7 agreement wrappers

This file starts the downstream adoption of the hfactor-free descended Claim 5.7 bundle without
editing the large legacy `Agreement.lean` or the active `DescendedRset.lean` surface.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]}
variable {ωs : Fin n ↪ F}

open BCIKS20AppendixA.ClaimA2 in
/-- Descended Claim 5.8 coefficient vanishing from beta-rec embedding vanishing.

This is the `Claim57ResidualsDescended` companion to
`approximate_solution_is_exact_solution_coeffs_of_beta_embedding_zero`: the extracted
`R_descended`/`H_descended` pair and Claim A.2 hypotheses come directly from the descended bundle,
with only the explicit `pg_RsetDescended = pg_Rset` coincidence hypothesis needed to reuse the
legacy Claim 5.7 extractor. -/
lemma approximate_solution_descended_coeffs_of_beta_embedding_zero
    (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs =
      pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (β
          (H := H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) t) = 0) :
    ∀ t ≥ k,
      α' x₀
        (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
          (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (irreducible_H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
          (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (natDegree_H_descended_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
          (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (claimA2_hypotheses_descended (F := F) (m := m) (n := n) (k := k)
          (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        t =
      (0 : BCIKS20AppendixA.𝕃
        (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
          (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)) := by
  intro t ht
  exact alpha'_eq_zero_of_embedding_beta_eq_zero
    (F := F) (x₀ := x₀)
    (R := R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (H := H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (irreducible_H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (natDegree_H_descended_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (claimA2_hypotheses_descended (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (hemb t ht)

open BCIKS20AppendixA.ClaimA2 in
/-- Descended alpha-series truncation from beta-rec embedding vanishing. -/
lemma approximate_solution_alpha_descended_powerSeries_eq_trunc_of_beta_embedding_zero
    (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs =
      pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (β
          (H := H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) t) = 0) :
    PowerSeries.mk
      (α' x₀
        (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
          (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (irreducible_H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
          (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (natDegree_H_descended_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
          (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (claimA2_hypotheses_descended (F := F) (m := m) (n := n) (k := k)
          (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)) =
      ((PowerSeries.mk
        (α' x₀
          (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (irreducible_H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (natDegree_H_descended_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (claimA2_hypotheses_descended (F := F) (m := m) (n := n) (k := k)
            (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide))).trunc k :
        PowerSeries (BCIKS20AppendixA.𝕃
          (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide))) := by
  exact alpha'_powerSeries_eq_trunc_of_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (natDegree_H_descended_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (claimA2_hypotheses_descended (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (approximate_solution_descended_coeffs_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide hemb)

open BCIKS20AppendixA.ClaimA2 in
/-- Descended gamma-tail coefficient vanishing from beta-rec embedding vanishing. -/
lemma approximate_solution_gamma_descended_coeff_zero_of_beta_embedding_zero
    (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs =
      pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
        (β
          (H := H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) t) = 0) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀
          (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (irreducible_H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (natDegree_H_descended_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (claimA2_hypotheses_descended (F := F) (m := m) (n := n) (k := k)
            (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)) =
        (0 : BCIKS20AppendixA.𝕃
          (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
            (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (natDegree_H_descended_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (claimA2_hypotheses_descended (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
    (approximate_solution_descended_coeffs_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide hemb)

#print axioms ProximityGap.approximate_solution_descended_coeffs_of_beta_embedding_zero
#print axioms
  ProximityGap.approximate_solution_alpha_descended_powerSeries_eq_trunc_of_beta_embedding_zero
#print axioms
  ProximityGap.approximate_solution_gamma_descended_coeff_zero_of_beta_embedding_zero

end ProximityGap
