/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._R23ParameterChoice
import ArkLib.Research.ProximityGap.Frontier.PaleyCosetCancellation

/-!
# Quadratic discrepancy under a common inversion

The pole-dependent signs in a common inversion turn the discrepancy into a sum over ordered
pairs. In its second moment, an off-diagonal pair has at most two partners with the same
unordered endpoints. The quartic Stepanov theorem bounds all other pair correlations.
-/

namespace ArkLib.ProximityGap.Frontier.PaleyProjectiveMoment

open Finset R18FourthMomentTwist R20QuadFaceBridge R22StepanovAssembly R23ParameterChoice

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A sum over a set of ordered pairs with the two quadratic signs attached to the pole. -/
noncomputable def weightedSum (P : Finset (F × F)) (w : F × F → ℝ) (t : F) : ℝ :=
  ∑ e ∈ P, w e * (quadraticChar F (t - e.1) : ℝ) * (quadraticChar F (t - e.2) : ℝ)

private theorem expand_moment (P : Finset (F × F)) (w : F × F → ℝ) :
    ∑ t : F, (weightedSum P w t) ^ 2 =
      ∑ e ∈ P, ∑ f ∈ P, w e * w f * (intQuartic (e, f) : ℝ) := by
  unfold weightedSum
  simp_rw [pow_two, sum_mul_sum, sum_comm (s := univ) (t := P)]
  refine sum_congr rfl fun e _ => sum_congr rfl fun f _ => ?_
  simp only [intQuartic, map_mul, Int.cast_sum, Int.cast_mul, mul_sum]
  exact sum_congr rfl fun t _ => by ring

private theorem edge_bound {C : ℝ} (hC : 0 ≤ C)
    (hW : QuarticWeilInputC (quadCharC F) univ C) (w : F × F → ℝ)
    {e f : F × F} (he : |w e| ≤ 1) (hf : |w f| ≤ 1) (hdiag : e.1 = e.2 → w e = 0) :
    w e * w f * (intQuartic (e, f) : ℝ) ≤
      (if e = f then (Fintype.card F : ℝ) else 0) +
      (if e.swap = f then (Fintype.card F : ℝ) else 0) + C * Real.sqrt (Fintype.card F) := by
  let K : ℝ := intQuartic (e, f)
  have hterm : w e * w f * K ≤ |K| := calc
    _ ≤ |w e * w f * K| := le_abs_self _
    _ = |w e| * |w f| * |K| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * 1 * |K| := by gcongr
    _ = _ := by ring
  have htriv : |K| ≤ (Fintype.card F : ℝ) := by
    simpa only [norm_quadTerm_quadCharC] using norm_quadTerm_le_card (quadCharC F) (e, f)
  have hnn : 0 ≤ C * Real.sqrt (Fintype.card F) := by positivity
  change w e * w f * K ≤ _
  by_cases h₁ : e = f
  · rw [ite_eq_left h₁]
    split_ifs <;> linarith
  by_cases h₂ : e.swap = f
  · rw [ite_eq_right h₁, ite_eq_left h₂]
    linarith
  rw [ite_eq_right h₁, ite_eq_right h₂, zero_add, zero_add]
  by_cases hd : e.1 = e.2
  · simpa [hdiag hd] using hnn
  have hnd : ¬ IsDegenerate (e, f) := by
    rintro (h | h | h)
    · exact h₁ (Prod.ext h.1 h.2)
    · exact h₂ (Prod.ext h.2 h.1)
    · exact hd h.1
  have hb := hW (e, f) (by simp) hnd
  rw [norm_quadTerm_quadCharC] at hb
  exact hterm.trans hb

/-- Weighted second moment for any ordered-pair support. The weights are bounded by one
and vanish on loops. The coefficient `2` counts both possible orders of the endpoints. -/
theorem weighted_moment_of_quartic {C : ℝ} (hC : 0 ≤ C)
    (hW : QuarticWeilInputC (quadCharC F) univ C) (P : Finset (F × F)) (w : F × F → ℝ)
    (hw : ∀ e ∈ P, |w e| ≤ 1) (hd : ∀ e ∈ P, e.1 = e.2 → w e = 0) :
    ∑ t : F, (weightedSum P w t) ^ 2 ≤
      2 * (Fintype.card F : ℝ) * P.card + C * Real.sqrt (Fintype.card F) * P.card ^ 2 := by
  classical
  let q : ℝ := Fintype.card F
  let c := C * Real.sqrt q
  have hrow (e : F × F) (he : e ∈ P) :
      ∑ f ∈ P, w e * w f * (intQuartic (e, f) : ℝ) ≤ q + q + P.card * c := by
    calc
      _ ≤ ∑ f ∈ P, ((if e = f then q else 0) + (if e.swap = f then q else 0) + c) :=
        sum_le_sum fun f hf => edge_bound hC hW w (hw e he) (hw f hf) (hd e he)
      _ = (if e ∈ P then q else 0) + (if e.swap ∈ P then q else 0) + P.card * c := by
        simp [sum_add_distrib, nsmul_eq_mul]
      _ ≤ _ := by
        have hq : 0 ≤ q := Nat.cast_nonneg _
        split_ifs <;> linarith
  calc
    _ = _ := expand_moment P w
    _ ≤ ∑ _ ∈ P, (q + q + P.card * c) := sum_le_sum hrow
    _ = _ := by simp [nsmul_eq_mul, c, q]; ring

/-- Paley discrepancy with the two denominator signs from a common inversion. -/
noncomputable def discrepancy (A B : Finset F) (t : F) : ℝ :=
  weightedSum (A ×ˢ B) (fun e => (quadraticChar F (e.1 - e.2) : ℝ)) t

private theorem discrepancy_moment {C : ℝ} (hC : 0 ≤ C)
    (hW : QuarticWeilInputC (quadCharC F) univ C) (A B : Finset F) :
    ∑ t : F, (discrepancy A B t) ^ 2 ≤
      2 * (Fintype.card F : ℝ) * (A.card * B.card) +
        C * Real.sqrt (Fintype.card F) * (A.card * B.card : ℝ) ^ 2 := by
  apply le_trans (weighted_moment_of_quartic hC hW (A ×ˢ B)
    (fun e => (quadraticChar F (e.1 - e.2) : ℝ)) ?_ ?_)
  · simp [Finset.card_product]
  · intro e _
    rcases (quadraticChar_isQuadratic F) (e.1 - e.2) with h | h | h <;> simp [h]
  · intro e _ he
    simp [he]

/-- Unconditional projective second moment over any finite field of odd characteristic. -/
theorem sum_sq_le (hF : ringChar F ≠ 2) (A B : Finset F) :
    ∑ t : F, (discrepancy A B t) ^ 2 ≤
      2 * (Fintype.card F : ℝ) * (A.card * B.card) +
        14 * Real.sqrt (Fintype.card F) * (A.card * B.card : ℝ) ^ 2 := by
  apply discrepancy_moment (by norm_num)
  convert quarticWeilInputC_of_cubicHasseC hF (k := 13) (by norm_num)
    (legendreCubicHasseC_unconditional hF) univ using 1
  norm_num

/-- Improved unconditional coefficient for field orders at least 3251. -/
theorem sum_sq_le_of_card (hF : ringChar F ≠ 2) (hq : 3251 ≤ Fintype.card F) (A B : Finset F) :
    ∑ t : F, (discrepancy A B t) ^ 2 ≤
      2 * (Fintype.card F : ℝ) * (A.card * B.card) +
        8 * Real.sqrt (Fintype.card F) * (A.card * B.card : ℝ) ^ 2 := by
  apply discrepancy_moment (by norm_num)
  convert quarticWeilInputC_of_cubicHasseC hF (k := 7) (by norm_num)
    (legendreCubicHasseC_49_of_large hF hq) univ using 1
  norm_num

/-- The finite image of a set under the chart with pole `t`. -/
def inverseImage (A : Finset F) (t : F) : Finset F :=
  (A.erase t).image fun a => (a - t)⁻¹

omit [Field F] [Fintype F] in
private theorem sum_erase_zero (A : Finset F) (t : F) (f : F → ℝ) (hz : f t = 0) :
    ∑ a ∈ A.erase t, f a = ∑ a ∈ A, f a := by
  by_cases ht : t ∈ A
  · simpa [hz] using Finset.sum_erase_add A f ht
  · rw [erase_eq_of_notMem ht]

/-- The actual discrepancy on the two finite chart images differs from the weighted sum
by the character of `−1`. Puncturing before inversion permits every pole in the field. -/
theorem inverseImage_discrepancy (A B : Finset F) (t : F) :
    ∑ x ∈ inverseImage A t, ∑ y ∈ inverseImage B t, (quadraticChar F (x - y) : ℝ) =
      (quadraticChar F (-1) : ℝ) * discrepancy A B t := by
  classical
  let M : _root_.ProximityGap.MobiusSeamCoordinateSupply.Mobius F := ⟨0, -1, -1, t⟩
  have hden (x : F) : M.den x = t - x := by
    change -1 * x + t = t - x
    ring
  have hval (x : F) : M.value x = (x - t)⁻¹ := by
    rw [_root_.ProximityGap.MobiusSeamCoordinateSupply.Mobius.value, hden]
    change (0 * x + -1) / (t - x) = (x - t)⁻¹
    rw [show t - x = -(x - t) by ring, div_eq_mul_inv, inv_neg]
    ring
  have hdet : M.det = -1 := by
    change 0 * t - -1 * -1 = -1
    ring
  have hn (S : Finset F) (x : F) (hx : x ∈ S.erase t) : M.den x ≠ 0 := by
    rw [hden]
    exact sub_ne_zero.mpr (Ne.symm (mem_erase.mp hx).1)
  have h := _root_.ProximityGap.PaleyCosetCancellation.mobius_weighted_image_sum M
    (by rw [hdet]; exact neg_ne_zero.mpr one_ne_zero) (A.erase t) (B.erase t) (hn A) (hn B)
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  have hmap (S : Finset F) : S.image M.value = S.image (fun x => (x - t)⁻¹) := by
    rw [show M.value = (fun x => (x - t)⁻¹) from funext hval]
  simp only [hmap, hden, hdet, one_mul] at h
  refine h.trans (congrArg ((quadraticChar F (-1) : ℝ) * ·) ?_)
  let K (a b : F) := (quadraticChar F (t-a) : ℝ) * (quadraticChar F (t-b) : ℝ) *
    (quadraticChar F (a-b) : ℝ)
  change ∑ a ∈ A.erase t, ∑ b ∈ B.erase t, K a b = discrepancy A B t
  have hB (a : F) := sum_erase_zero B t (K a) (by simp [K])
  simp_rw [hB]
  rw [sum_erase_zero A t _ (by simp [K]), discrepancy, weightedSum, Finset.sum_product]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by dsimp [K]; ring

/-- Upper tail of the actual discrepancy on finite chart images. -/
noncomputable def exceptions (A B : Finset F) (T : ℝ) : Finset F :=
  univ.filter fun t =>
    T ≤ |∑ x ∈ inverseImage A t, ∑ y ∈ inverseImage B t, (quadraticChar F (x - y) : ℝ)|

/-- The exceptional-pole count is bounded by the projective second moment. -/
theorem exceptions_card_mul_sq_le (A B : Finset F) {T : ℝ} (hT : 0 ≤ T) :
    ((exceptions A B T).card : ℝ) * T ^ 2 ≤ ∑ t : F, (discrepancy A B t) ^ 2 := by
  classical
  have hs : (quadraticChar F (-1) : ℝ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero (α := F)))
  calc
    _ = ∑ _ ∈ exceptions A B T, T ^ 2 := by simp
    _ ≤ ∑ t ∈ exceptions A B T, (discrepancy A B t) ^ 2 := by
      refine sum_le_sum fun t ht => ?_
      have h := pow_le_pow_left₀ hT (mem_filter.mp ht).2 2
      simpa only [sq_abs, inverseImage_discrepancy, mul_pow, hs, one_mul] using h
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- At relative threshold `η`, the exceptional fraction times `η²` is at most
`2 / (|A||B|) + 8 / √q`. The fraction is over all poles, with punctured finite images. -/
theorem relative_exceptions_le (hF : ringChar F ≠ 2) (hq : 3251 ≤ Fintype.card F)
    {A B : Finset F} (hA : A.Nonempty) (hB : B.Nonempty) {η : ℝ} (hη : 0 ≤ η) :
    ((exceptions A B (η * (A.card * B.card : ℝ))).card : ℝ) / (Fintype.card F) * η ^ 2 ≤
      2 / (A.card * B.card : ℝ) + 8 / Real.sqrt (Fintype.card F) := by
  let q : ℝ := Fintype.card F
  let n := (A.card * B.card : ℝ)
  let r := Real.sqrt q
  let E : ℝ := (exceptions A B (η * n)).card
  have hqp : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hr : 0 < r := Real.sqrt_pos.mpr hqp
  have hn : 0 < n := by
    dsimp [n]
    exact mul_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast hB.card_pos)
  have he : E * (η * n) ^ 2 ≤ 2 * q * n + 8 * r * n ^ 2 :=
    (exceptions_card_mul_sq_le A B (mul_nonneg hη hn.le)).trans (sum_sq_le_of_card hF hq A B)
  have hsq : r ^ 2 = q := Real.sq_sqrt hqp.le
  change E / q * η ^ 2 ≤ 2 / n + 8 / r
  apply le_of_mul_le_mul_right (a := q * n ^ 2) _ (by positivity)
  calc
    _ = E * (η * n) ^ 2 := by field_simp
    _ ≤ _ := he
    _ = _ := by rw [← hsq]; field_simp

end ArkLib.ProximityGap.Frontier.PaleyProjectiveMoment

#print axioms ArkLib.ProximityGap.Frontier.PaleyProjectiveMoment.sum_sq_le
#print axioms ArkLib.ProximityGap.Frontier.PaleyProjectiveMoment.sum_sq_le_of_card
#print axioms ArkLib.ProximityGap.Frontier.PaleyProjectiveMoment.inverseImage_discrepancy
#print axioms ArkLib.ProximityGap.Frontier.PaleyProjectiveMoment.exceptions_card_mul_sq_le
#print axioms ArkLib.ProximityGap.Frontier.PaleyProjectiveMoment.relative_exceptions_le
