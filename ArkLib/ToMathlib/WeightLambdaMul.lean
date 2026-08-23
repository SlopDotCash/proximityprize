/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsCore

/-!
# Exact multiplicativity (additivity) of the BCIKS20 weight `Λ` on the polynomial ring

The BCIKS20 Appendix A.2 weighted degree `weight_Λ` on `F[X][Y]` (`F` a field) is only
*sub*-additive on the regular ring `𝒪 H` after reduction (`weight_Λ_over_𝒪_mul_le`,
`weight_Λ_mul_le`).  On the **polynomial ring** `F[X][Y]` itself — an integral domain — it is in
fact **exactly additive**:

`weight_Λ (f * g) H D = weight_Λ f H D + weight_Λ g H D`  for `f, g ≠ 0`.

This is the leading-form multiplicativity (`gr` of a domain under a monomial filtration is a domain),
proved here by the extremal-monomial argument: pick the *maximal*-`Y`-degree monomial attaining the
top weight in each factor; in the product, the coefficient at the summed `(Y, X)`-bidegree receives
exactly one surviving contribution — the product of the two leading `F[X]`-coefficients — which is
nonzero because `F[X]` is a domain.

This is the genuine multiplicativity that the field weight (an honest `AddValuation` on the function
field `𝕃 H`) extends, and that the sub-additive `weight_Λ_over_𝒪` cannot supply.  Mathlib has no
`weightedTotalDegree_mul` (only `IsWeightedHomogeneous.mul`), so this is proved from first principles.
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA

namespace BCIKS20AppendixA

variable {F : Type} [Field F]

/-- For `f ≠ 0`: extract the top `weight_Λ` value `W` and a *maximal*-`Y`-degree index `i₀`
attaining it, together with the global upper bound and the maximality property. -/
private lemma weight_Λ_exists_top (f H : F[X][Y]) (D : ℕ) (hf : f ≠ 0) :
    ∃ (W i₀ : ℕ),
      weight_Λ f H D = WithBot.some W ∧
      i₀ ∈ f.support ∧
      i₀ * (D + 1 - Bivariate.natDegreeY H) + (f.coeff i₀).natDegree = W ∧
      (∀ i ∈ f.support,
        i * (D + 1 - Bivariate.natDegreeY H) + (f.coeff i).natDegree ≤ W) ∧
      (∀ i ∈ f.support,
        i * (D + 1 - Bivariate.natDegreeY H) + (f.coeff i).natDegree = W → i ≤ i₀) := by
  classical
  set wv : ℕ → ℕ := fun i => i * (D + 1 - Bivariate.natDegreeY H) + (f.coeff i).natDegree with hwv
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  have hdef : weight_Λ f H D = f.support.sup (fun i => (WithBot.some (wv i) : WithBot ℕ)) := rfl
  obtain ⟨W, hW⟩ : ∃ W : ℕ, weight_Λ f H D = WithBot.some W := by
    rcases hcase : weight_Λ f H D with _ | W
    · exfalso
      obtain ⟨j, hj⟩ := hne
      have hbot : (f.support.sup fun i => (WithBot.some (wv i) : WithBot ℕ)) = ⊥ := by
        rw [← hdef]; exact hcase
      simp only [Finset.sup_eq_bot_iff] at hbot
      exact WithBot.coe_ne_bot (hbot j hj)
    · exact ⟨W, rfl⟩
  have hle : ∀ i ∈ f.support, wv i ≤ W := by
    intro i hi
    have h1 := le_weight_Λ_of_mem_support (f := f) (H := H) (D := D) hi
    rw [hW] at h1
    exact_mod_cast h1
  obtain ⟨j, hj, hjeq⟩ : ∃ j ∈ f.support, wv j = W := by
    obtain ⟨j, hj, hjsup⟩ :=
      Finset.exists_mem_eq_sup f.support hne (fun i => (WithBot.some (wv i) : WithBot ℕ))
    refine ⟨j, hj, ?_⟩
    rw [hdef, hjsup] at hW
    exact_mod_cast hW
  set A := f.support.filter (fun i => wv i = W) with hA
  have hAne : A.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hjeq⟩⟩
  refine ⟨W, A.max' hAne, hW, ?_, ?_, hle, ?_⟩
  · exact (Finset.mem_filter.mp (A.max'_mem hAne)).1
  · exact (Finset.mem_filter.mp (A.max'_mem hAne)).2
  · intro i hi hiW; exact A.le_max' i (Finset.mem_filter.mpr ⟨hi, hiW⟩)

/-- **`weight_Λ` is exactly additive on the polynomial ring `F[X][Y]`** (an integral domain).
The reverse of the sub-additive `weight_Λ_mul_le`, via leading-form multiplicativity. -/
theorem weight_Λ_mul (f g H : F[X][Y]) (D : ℕ) (hf : f ≠ 0) (hg : g ≠ 0) :
    weight_Λ (f * g) H D = weight_Λ f H D + weight_Λ g H D := by
  classical
  set m : ℕ := D + 1 - Bivariate.natDegreeY H with hm
  obtain ⟨Wf, i_f, hWf, hif_sup, hif_eq, hf_le, hf_max⟩ := weight_Λ_exists_top f H D hf
  obtain ⟨Wg, i_g, hWg, hig_sup, hig_eq, hg_le, hg_max⟩ := weight_Λ_exists_top g H D hg
  rw [← hm] at hif_eq hig_eq hf_le hg_le hf_max hg_max
  set af := (f.coeff i_f).natDegree with haf
  set ag := (g.coeff i_g).natDegree with hag
  have hfc_ne : f.coeff i_f ≠ 0 := Polynomial.mem_support_iff.mp hif_sup
  have hgc_ne : g.coeff i_g ≠ 0 := Polynomial.mem_support_iff.mp hig_sup
  have hkey : ((f * g).coeff (i_f + i_g)).coeff (af + ag)
      = (f.coeff i_f).leadingCoeff * (g.coeff i_g).leadingCoeff := by
    rw [Polynomial.coeff_mul, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single (i_f, i_g)]
    · dsimp only
      rw [Polynomial.coeff_mul, Finset.sum_eq_single (af, ag)]
      · dsimp only
        rw [haf, hag, Polynomial.coeff_natDegree, Polynomial.coeff_natDegree]
      · rintro ⟨p, p'⟩ hmem hne
        dsimp only
        have hpp : p + p' = af + ag := Finset.mem_antidiagonal.mp hmem
        rcases Nat.lt_or_ge (f.coeff i_f).natDegree p with hp | hp
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hp, zero_mul]
        · have hp2 : (g.coeff i_g).natDegree < p' := by
            rcases Nat.lt_or_ge (g.coeff i_g).natDegree p' with h | h
            · exact h
            · exfalso; apply hne
              rw [← haf] at hp; rw [← hag] at h
              rw [Prod.mk.injEq]; exact ⟨by omega, by omega⟩
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hp2, mul_zero]
      · intro h; simp at h
    · rintro ⟨i, i'⟩ hmem hne
      dsimp only
      have hii : i + i' = i_f + i_g := Finset.mem_antidiagonal.mp hmem
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨p, p'⟩ hpmem
      dsimp only
      have hpp : p + p' = af + ag := Finset.mem_antidiagonal.mp hpmem
      by_cases hfi : f.coeff i = 0
      · simp [hfi]
      by_cases hgi : g.coeff i' = 0
      · simp [hgi]
      · have hisup : i ∈ f.support := Polynomial.mem_support_iff.mpr hfi
        have hisup' : i' ∈ g.support := Polynomial.mem_support_iff.mpr hgi
        have hdf : i * m + (f.coeff i).natDegree ≤ Wf := hf_le i hisup
        have hdg : i' * m + (g.coeff i').natDegree ≤ Wg := hg_le i' hisup'
        have hsum : (f.coeff i).natDegree + (g.coeff i').natDegree < af + ag := by
          rcases Nat.lt_or_ge ((f.coeff i).natDegree + (g.coeff i').natDegree) (af + ag) with h | h
          · exact h
          · exfalso
            have hNm : i * m + i' * m = i_f * m + i_g * m := by
              rw [← Nat.add_mul, ← Nat.add_mul, hii]
            have htop : Wf + Wg = i_f * m + i_g * m + (af + ag) := by
              rw [← hif_eq, ← hig_eq]; ring
            have heq_f : i * m + (f.coeff i).natDegree = Wf := by omega
            have heq_g : i' * m + (g.coeff i').natDegree = Wg := by omega
            have hile : i ≤ i_f := hf_max i hisup heq_f
            have hi'le : i' ≤ i_g := hg_max i' hisup' heq_g
            exact hne (by rw [Prod.mk.injEq]; exact ⟨by omega, by omega⟩)
        by_cases hp : p ≤ (f.coeff i).natDegree
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (n := p') (by omega), mul_zero]
        · rw [not_le] at hp
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hp, zero_mul]
    · intro h; simp at h
  have hlc_ne : (f.coeff i_f).leadingCoeff * (g.coeff i_g).leadingCoeff ≠ 0 :=
    mul_ne_zero (by rwa [Polynomial.leadingCoeff_ne_zero])
      (by rwa [Polynomial.leadingCoeff_ne_zero])
  have hcoeff_ne : ((f * g).coeff (i_f + i_g)).coeff (af + ag) ≠ 0 := by rw [hkey]; exact hlc_ne
  have hfgc_ne : (f * g).coeff (i_f + i_g) ≠ 0 := by
    intro h; rw [h, Polynomial.coeff_zero] at hcoeff_ne; exact hcoeff_ne rfl
  have hfg_sup : (i_f + i_g) ∈ (f * g).support := Polynomial.mem_support_iff.mpr hfgc_ne
  have hdeg_ge : af + ag ≤ ((f * g).coeff (i_f + i_g)).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff_ne
  have hge : (WithBot.some (Wf + Wg) : WithBot ℕ) ≤ weight_Λ (f * g) H D := by
    refine le_trans ?_ (le_weight_Λ_of_mem_support hfg_sup)
    apply WithBot.coe_le_coe.mpr
    have hWfg : Wf + Wg = (i_f + i_g) * m + (af + ag) := by rw [← hif_eq, ← hig_eq]; ring
    rw [hWfg, ← hm]
    exact Nat.add_le_add_left hdeg_ge _
  have hle_total : weight_Λ (f * g) H D ≤ weight_Λ f H D + weight_Λ g H D :=
    weight_Λ_mul_le f g H D
  rw [hWf, hWg, ← WithBot.coe_add] at hle_total ⊢
  exact le_antisymm hle_total hge

end BCIKS20AppendixA
