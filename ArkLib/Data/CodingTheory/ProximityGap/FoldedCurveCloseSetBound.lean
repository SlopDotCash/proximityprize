/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.CurveAgreementThreshold
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25SpreadBound
import ArkLib.Data.CodingTheory.ProximityGap.GG25MCAFromCurveDecodability


/-!
# The folded curve close-set bound (B2 producer, `A = Fin s → F`) (#389, #334)

The folded generalization of `curveCloseSet_codewordCurve_card_le` to symbols in `Fin s → F` (the
deployed folded Reed–Solomon setting).  An agreeing coordinate matches all `s` components, so for
any fixed weight `lam : Fin s → F` the scalar polynomial `Pᵢ = ∑ⱼ (lam · (uⱼᵢ − cⱼᵢ))·Xʲ`
(degree `≤ ℓ`) vanishes at every close seed where the curves agree at `i`.  The curve list bound
`curve_agreement_card_le` then gives `|curveCloseSet δ u (comb c)| · (a − b) ≤ ℓ · n`, with
`a = n − ⌊δn⌋` and `b = #{i : Pᵢ = 0}`.  Choosing `lam` to separate the moving coordinates
(possible when `|F| > n`) makes `b` the genuine count of identically-zero coordinates — the
per-codeword-curve producer ingredient in the folded regime.  Axiom-clean.
-/
open Finset Polynomial
open scoped NNReal

namespace ProximityGap

open GG25Lemma32

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Field F] [Fintype F] [DecidableEq F]

/-- **Folded curve close-set bound against a codeword-curve (B2 producer, `A = Fin s → F`).**
In the folded setting an agreeing coordinate matches all `s` components, so for any fixed weight
vector `lam : Fin s → F` the scalar polynomial `Pᵢ = ∑ⱼ (lam · (uⱼᵢ − cⱼᵢ))·Xʲ` (degree `≤ ℓ`)
vanishes at every close seed whenever the curves agree at `i`.  Hence the curve list bound applies:
`|curveCloseSet δ u (comb c)| · (a − b) ≤ ℓ · n`, with `a = n − ⌊δn⌋` and `b = #{i : Pᵢ = 0}`.
Choosing `lam` to separate the moving coordinates (possible when `|F| > n`) makes `b` the genuine
count of identically-zero coordinates.  This is the folded generalization of the unfolded
`curveCloseSet_codewordCurve_card_le`. -/
theorem foldedCurveCloseSet_codewordCurve_card_le {s ℓ : ℕ}
    (u c : Fin (ℓ + 1) → ι → (Fin s → F)) (lam : Fin s → F) {b : ℕ}
    (hb : (univ.filter (fun i => (∑ j : Fin (ℓ + 1),
        Polynomial.C (∑ m : Fin s, lam m * (u j i m - c j i m)) * Polynomial.X ^ (j : ℕ) : Polynomial F) = 0)).card = b)
    {δ : ℝ≥0} (hab : b < Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) :
    (curveCloseSet δ u (comb c : F → ι → (Fin s → F))).card
        * ((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) - b)
      ≤ ℓ * Fintype.card ι := by
  classical
  set P : ι → Polynomial F :=
    fun i => ∑ j : Fin (ℓ + 1),
      Polynomial.C (∑ m : Fin s, lam m * (u j i m - c j i m)) * Polynomial.X ^ (j : ℕ) with hP
  set a := Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ with ha
  have hdeg : ∀ i, (P i).natDegree ≤ ℓ := by
    intro i
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun k _ => ?_)
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.lt_succ_iff.mp k.isLt
  -- agreement at `i` forces the `lam`-combined polynomial to vanish
  have hev_imp : ∀ (α : F) (i : ι), comb u α i = comb c α i → (P i).eval α = 0 := by
    intro α i hagree
    have hcompzero : ∀ m : Fin s,
        ∑ j : Fin (ℓ + 1), lam m * (u j i m - c j i m) * α ^ (j : ℕ) = 0 := by
      intro m
      have hm := congrFun hagree m
      simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hm
      have hz : ∑ j : Fin (ℓ + 1), (u j i m - c j i m) * α ^ (j : ℕ) = 0 := by
        simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
        simpa [mul_comm] using hm
      calc ∑ j : Fin (ℓ + 1), lam m * (u j i m - c j i m) * α ^ (j : ℕ)
          = lam m * ∑ j : Fin (ℓ + 1), (u j i m - c j i m) * α ^ (j : ℕ) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = 0 := by rw [hz, mul_zero]
    rw [hP]
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun m _ => hcompzero m)
  -- the close set lands inside the `≥ a`-vanishing set
  have hsub : curveCloseSet δ u (comb c : F → ι → (Fin s → F))
      ⊆ univ.filter (fun α : F => a ≤ (univ.filter (fun i => (P i).eval α = 0)).card) := by
    intro α hα
    simp only [curveCloseSet, mem_filter, mem_univ, true_and] at hα
    have hham : hammingDist (comb u α) (comb c α) ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ :=
      hammingDist_le_floor_of_relHam_le hα
    rw [mem_filter]
    refine ⟨mem_univ α, ?_⟩
    have hpart : (univ.filter (fun i => comb u α i = comb c α i)).card
        + hammingDist (comb u α) (comb c α) = Fintype.card ι := by
      rw [hammingDist, ← Finset.card_univ (α := ι)]
      exact Finset.card_filter_add_card_filter_not (s := univ)
        (fun i => comb u α i = comb c α i)
    have hagree_a : a ≤ (univ.filter (fun i => comb u α i = comb c α i)).card := by
      rw [ha]; omega
    refine le_trans hagree_a (Finset.card_le_card ?_)
    intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨mem_univ i, hev_imp α i hi.2⟩
  calc (curveCloseSet δ u (comb c : F → ι → (Fin s → F))).card * (a - b)
      ≤ (univ.filter (fun α : F =>
          a ≤ (univ.filter (fun i => (P i).eval α = 0)).card)).card * (a - b) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ ℓ * Fintype.card ι := curve_agreement_card_le P hdeg hb hab

end ProximityGap
