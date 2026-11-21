/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._R17TchiMomentIdentities

/-!
# Mean square of Paley discrepancy under a relative affine transformation

Move one of two fixed sets by every invertible affine map of the field. For a nontrivial
multiplicative character the sum of the squared discrepancies is exactly
`|A||B|(q − |A|)(q − |B|)`. There are `q(q−1)` affine maps, with multiplicity retained
if a set has affine symmetries.
-/

namespace ArkLib.ProximityGap.Frontier.PaleyAffineSecondMoment

open Finset R16LegendreCosetFace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R]

private theorem affine_pair (f h : F → R) (hh : ∑ x : F, h x = 0) (b c : F) :
    ∑ u : F, ∑ v : F, f (u * b + v) * h (u * c + v) =
      if b = c then (Fintype.card F : R) * ∑ x : F, f x * h x else 0 := by
  have htrans (u : F) : ∑ v : F, f (u * b + v) * h (u * c + v) =
      ∑ x : F, f x * h ((c - b) * u + x) := by
    refine Fintype.sum_equiv (Equiv.addLeft (u * b)) _ _ (fun v => ?_)
    change f (u * b + v) * h (u * c + v) = f (u * b + v) * h ((c - b) * u + (u * b + v))
    rw [show (c - b) * u + (u * b + v) = u * c + v by ring]
  simp_rw [htrans]
  by_cases heq : b = c
  · subst c
    simp [nsmul_eq_mul]
  · rw [ite_eq_right heq, Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro x _
    rw [← Finset.mul_sum]
    have hm : ∑ u : F, h ((c - b) * u + x) = ∑ u : F, h u :=
      Fintype.sum_equiv ((Equiv.mulLeft₀ (c - b) (sub_ne_zero.mpr (Ne.symm heq))).trans
        (Equiv.addRight x)) _ _ (fun _ => rfl)
    rw [hm, hh, mul_zero]

private theorem affine_product (B : Finset F) (f h : F → R) (hh : ∑ x : F, h x = 0) :
    ∑ u ∈ (Finset.univ.erase (0 : F)), ∑ v : F,
        (∑ b ∈ B, f (u * b + v)) * (∑ b ∈ B, h (u * b + v)) =
      (B.card : R) * ((Fintype.card F : R) - B.card) * ∑ x : F, f x * h x := by
  classical
  let K (u : F) := ∑ v : F, (∑ b ∈ B, f (u * b + v)) * ∑ b ∈ B, h (u * b + v)
  change ∑ u ∈ Finset.univ.erase (0 : F), K u = _
  have hfull : ∑ u : F, K u = B.card * ((Fintype.card F : R) * ∑ x : F, f x * h x) := by
    unfold K
    simp_rw [Finset.sum_mul_sum]
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := B)]
    simp_rw [affine_pair f h hh]
    simp [nsmul_eq_mul]
  have hz : K 0 = (B.card : R) ^ 2 * ∑ x : F, f x * h x := by
    simp only [K, zero_mul, zero_add, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  have hsplit := Finset.add_sum_erase Finset.univ K (Finset.mem_univ (0 : F))
  rw [hfull, hz] at hsplit
  calc
    _ = B.card * ((Fintype.card F : R) * ∑ x : F, f x * h x) -
        (B.card : R) ^ 2 * ∑ x : F, f x * h x := by linear_combination hsplit
    _ = _ := by ring

/-- Exact discrepancy sum of squares over relative affine images, for every nontrivial character. -/
theorem mulChar_sum_sq_affine {χ : MulChar F ℂ} (hχ : χ ≠ 1) (A B : Finset F) :
    ∑ u ∈ Finset.univ.erase (0 : F), ∑ v : F,
      ‖∑ a ∈ A, ∑ b ∈ B, χ (a + (u * b + v))‖ ^ 2 =
        (A.card : ℝ) * B.card * ((Fintype.card F : ℝ) - A.card) *
          ((Fintype.card F : ℝ) - B.card) := by
  classical
  let W : F → ℂ := fun x => ∑ a ∈ A, χ (a + x)
  have hcent : ∑ x : F, W x = 0 := by
    unfold W
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    exact (Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ => rfl)).trans
      (MulChar.sum_eq_zero_of_ne_one hχ)
  have henergy : ∑ x : F, W x * star (W x) =
      (A.card : ℂ) * ((Fintype.card F : ℂ) - A.card) := by
    have hm := R17TchiMomentIdentities.sum_shiftedCharSum_mul_conj hχ
      (A.map (Equiv.neg F).toEmbedding)
    rw [mul_sub, ← pow_two]
    have hshift (x : F) : shiftedCharSum χ (A.map (Equiv.neg F).toEmbedding) x = W x := by
      simp only [shiftedCharSum, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.neg_apply,
        sub_neg_eq_add, W]
      exact Finset.sum_congr rfl (fun a _ => congrArg χ (add_comm x a))
    simp only [hshift, Finset.card_map, starRingEnd_apply] at hm
    exact hm
  have hprod := affine_product B W (fun x => star (W x))
    (by rw [← star_sum, hcent, star_zero])
  rw [henergy] at hprod
  have htransform (u v : F) :
      (∑ b ∈ B, W (u * b + v)) * ∑ b ∈ B, star (W (u * b + v)) =
      ((‖∑ a ∈ A, ∑ b ∈ B, χ (a + (u * b + v))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← star_sum]
    have hswap : ∑ b ∈ B, W (u*b+v) = ∑ a ∈ A, ∑ b ∈ B, χ (a + (u*b+v)) := Finset.sum_comm
    rw [hswap, ← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [htransform] at hprod
  have hreal : ∑ u ∈ Finset.univ.erase (0 : F), ∑ v : F,
      ‖∑ a ∈ A, ∑ b ∈ B, χ (a + (u * b + v))‖ ^ 2 =
      (B.card : ℝ) * ((Fintype.card F : ℝ) - B.card) *
        (A.card * ((Fintype.card F : ℝ) - A.card)) := by exact_mod_cast hprod
  rw [hreal]
  ring

/-- The affine placements whose discrepancy is at least `T`. -/
noncomputable def exceptions (χ : MulChar F ℂ) (A B : Finset F) (T : ℝ) : Finset (F × F) :=
  ((Finset.univ.erase (0 : F)) ×ˢ Finset.univ).filter fun uv =>
    T ≤ ‖∑ a ∈ A, ∑ b ∈ B, χ (a + (uv.1 * b + uv.2))‖

/-- Exact second-moment budget for the exceptional affine placements of any two fixed sets. -/
theorem exceptions_card_mul_sq_le {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    (A B : Finset F) {T : ℝ} (hT : 0 ≤ T) :
    ((exceptions χ A B T).card : ℝ) * T ^ 2 ≤
      (A.card : ℝ) * B.card * ((Fintype.card F : ℝ) - A.card) *
        ((Fintype.card F : ℝ) - B.card) := by
  classical
  let D := (Finset.univ.erase (0 : F)) ×ˢ (Finset.univ : Finset F)
  let score (uv : F × F) := ‖∑ a ∈ A, ∑ b ∈ B, χ (a + (uv.1 * b + uv.2))‖
  calc
    _ = ∑ _ ∈ exceptions χ A B T, T ^ 2 := by simp
    _ ≤ ∑ uv ∈ exceptions χ A B T, score uv ^ 2 := by
      apply Finset.sum_le_sum
      intro uv huv
      exact pow_le_pow_left₀ hT (Finset.mem_filter.mp huv).2 2
    _ ≤ ∑ uv ∈ D, score uv ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => sq_nonneg _)
    _ = _ := by
      rw [Finset.sum_product]
      exact mulChar_sum_sq_affine hχ A B

end ArkLib.ProximityGap.Frontier.PaleyAffineSecondMoment

#print axioms ArkLib.ProximityGap.Frontier.PaleyAffineSecondMoment.mulChar_sum_sq_affine
#print axioms ArkLib.ProximityGap.Frontier.PaleyAffineSecondMoment.exceptions_card_mul_sq_le
