/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- dedup-audit(#257): intended consolidation target for finSumFinEquiv_symm_dite; also holds the unique degreeOf_sum_mul_prod_erase_le_card. Do not delete. #257 A4.
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-!
# `finSumFinEquiv` value form + sumcheck round-poly degree bound

* `finSumFinEquiv_symm_dite` — the value-form classification of `finSumFinEquiv.symm` by whether the
  underlying `Nat` value is `< m`. Currently proved inline/duplicated across RingSwitching and
  Binius (issues #19/#29/#33/#62).
* `MvPolynomial.degreeOf_sum_mul_prod_erase_le_card` — the individual-degree bound on a
  LogUp/sumcheck round polynomial `∑ⱼ numⱼ·∏_{erase j} den`, when each `numⱼ`, `denⱼ` has
  `degreeOf i ≤ 1` (issue #13): `degreeOf i (…) ≤ |s|`.
-/

open Finset

/-- Value-form classification of `finSumFinEquiv.symm`. -/
theorem finSumFinEquiv_symm_dite {m n : ℕ} (x : Fin (m + n)) :
    finSumFinEquiv.symm x
      = if h : (x : ℕ) < m then Sum.inl ⟨x, h⟩ else Sum.inr ⟨(x : ℕ) - m, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  by_cases h : (x : ℕ) < m
  · rw [dif_pos h, finSumFinEquiv_apply_left]; ext; simp
  · rw [dif_neg h, finSumFinEquiv_apply_right]; ext; simp; omega

namespace MvPolynomial

/-- LogUp/sumcheck round-polynomial individual-degree bound: if each `num j` and `den j` has
`degreeOf i ≤ 1`, then `degreeOf i (∑ j, num j · ∏_{erase j} den) ≤ |s|`. -/
theorem degreeOf_sum_mul_prod_erase_le_card {σ R : Type*} [CommRing R] [DecidableEq σ]
    {α : Type*} [DecidableEq α] (i : σ) (s : Finset α) (num den : α → MvPolynomial σ R)
    (hnum : ∀ j ∈ s, MvPolynomial.degreeOf i (num j) ≤ 1)
    (hden : ∀ j ∈ s, MvPolynomial.degreeOf i (den j) ≤ 1) :
    MvPolynomial.degreeOf i (∑ j ∈ s, num j * ∏ l ∈ s.erase j, den l) ≤ s.card := by
  refine le_trans (MvPolynomial.degreeOf_sum_le i s _) ?_
  refine Finset.sup_le ?_
  intro j hj
  have hcard : (s.erase j).card = s.card - 1 := Finset.card_erase_of_mem hj
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨j, hj⟩
  calc MvPolynomial.degreeOf i (num j * ∏ l ∈ s.erase j, den l)
      ≤ MvPolynomial.degreeOf i (num j)
          + MvPolynomial.degreeOf i (∏ l ∈ s.erase j, den l) := MvPolynomial.degreeOf_mul_le i _ _
    _ ≤ 1 + ∑ l ∈ s.erase j, MvPolynomial.degreeOf i (den l) := by
        gcongr
        · exact hnum j hj
        · exact MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ 1 + ∑ _l ∈ s.erase j, 1 := by
        gcongr with l hl
        exact hden l (Finset.mem_of_mem_erase hl)
    _ = 1 + (s.erase j).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ s.card := by rw [hcard]; omega

end MvPolynomial

#print axioms finSumFinEquiv_symm_dite
#print axioms MvPolynomial.degreeOf_sum_mul_prod_erase_le_card
