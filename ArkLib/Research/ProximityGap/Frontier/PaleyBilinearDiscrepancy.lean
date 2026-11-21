/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QuadraticGaussSumMagnitude
import ArkLib.Research.ProximityGap.Frontier._R17TchiMomentIdentities
import ArkLib.Research.ProximityGap.Frontier._R23ParameterChoice
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Paley discrepancy on arbitrary sets

For sets `A` and `B` in a finite field of order `q`, let `S` be the sum of a
nontrivial multiplicative character at `a + b` over `A × B`. The second moment over translates of
`B` gives `q |S|² ≤ |A||B|(q − |A|)(q − |B|)` by Cauchy–Schwarz on `A` and its
complement. This gives the dense range of the classical Paley graph conjecture at every
`δ > 0` for which `q^(1 + 2δ) ≤ |A||B|`. For the quadratic character,
the campaign's Stepanov fourth moment gives a power saving by sampling any `1 ≤ r ≤ |B|` with
`r⁴ ≤ q` and `17q^(1 + 4δ) ≤ |A|r²`. The arbitrary small-set case over prime fields remains open.
-/

namespace ArkLib.ProximityGap.Frontier.PaleyBilinearDiscrepancy

open Finset R16LegendreCosetFace ArkLib.ProximityGap.Round7QuadraticGauss

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Centered discrepancy estimate for a nontrivial character, including both density factors. -/
theorem mulChar_sum_sq_le {χ : MulChar F ℂ} (hχ : χ ≠ 1) (A B : Finset F) :
    (Fintype.card F : ℝ) * ‖∑ a ∈ A, ∑ b ∈ B, χ (a + b)‖ ^ 2 ≤
      (A.card : ℝ) * B.card * ((Fintype.card F : ℝ) - A.card) *
        ((Fintype.card F : ℝ) - B.card) := by
  classical
  let W : F → ℂ := fun a => ∑ b ∈ B, χ (a + b)
  change (Fintype.card F : ℝ) * ‖∑ a ∈ A, W a‖ ^ 2 ≤ _
  have hzero : ∑ a : F, W a = 0 := by
    unfold W
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    calc
      ∑ a : F, χ (a + b) = ∑ a : F, χ a :=
        Fintype.sum_equiv (Equiv.addRight b) _ _ (fun _ => rfl)
      _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  have hmoment : ∑ a : F, ‖W a‖ ^ 2 =
      (B.card : ℝ) * ((Fintype.card F : ℝ) - B.card) := by
    have hm := R17TchiMomentIdentities.sum_shiftedCharSum_mul_conj hχ
      (B.map (Equiv.neg F).toEmbedding)
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hm
    have hc : ∑ a : F, ((‖W a‖ ^ 2 : ℝ) : ℂ) =
        (B.card : ℂ) * (Fintype.card F : ℂ) - (B.card : ℂ) ^ 2 := by
      simpa [shiftedCharSum, W] using hm
    rw [mul_sub, ← pow_two]
    exact_mod_cast hc
  have hcompl : ∑ a ∈ Aᶜ, W a = -(∑ a ∈ A, W a) := by
    have h := Finset.sum_compl_add_sum A W
    rw [hzero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hcard : ((Aᶜ).card : ℝ) = (Fintype.card F : ℝ) - A.card := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ A)]
  have hCS (T : Finset F) : ‖∑ a ∈ T, W a‖ ^ 2 ≤ (T.card : ℝ) * ∑ a ∈ T, ‖W a‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le T W) 2).trans sq_sum_le_card_mul_sum_sq
  have hA := hCS A
  have hAc := hCS Aᶜ
  rw [hcompl, norm_neg] at hAc
  have htotal := Finset.sum_compl_add_sum A (fun a => ‖W a‖ ^ 2)
  rw [hmoment] at htotal
  have hbound := add_le_add
    (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg Aᶜ.card : (0 : ℝ) ≤ _))
    (mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg A.card : (0 : ℝ) ≤ _))
  calc
    _ = (Aᶜ.card : ℝ) * ‖∑ a ∈ A, W a‖ ^ 2 + (A.card : ℝ) * ‖∑ a ∈ A, W a‖ ^ 2 := by
      rw [hcard]
      ring
    _ ≤ _ := hbound
    _ = (A.card : ℝ) * Aᶜ.card *
        ((∑ a ∈ Aᶜ, ‖W a‖ ^ 2) + ∑ a ∈ A, ‖W a‖ ^ 2) := by ring
    _ = _ := by rw [htotal, hcard]; ring

/-- Dense-set power saving for every nontrivial multiplicative character. -/
theorem mulChar_sum_power_saving {χ : MulChar F ℂ} (hχ : χ ≠ 1) (A B : Finset F) (δ : ℝ)
    (hsize : (Fintype.card F : ℝ) ^ (1 + 2 * δ) ≤ (A.card : ℝ) * B.card) :
    ‖∑ a ∈ A, ∑ b ∈ B, χ (a + b)‖ ≤
      (Fintype.card F : ℝ) ^ (-δ) * ((A.card : ℝ) * B.card) := by
  let q : ℝ := Fintype.card F
  let m : ℝ := (A.card : ℝ) * B.card
  let S : ℂ := ∑ a ∈ A, ∑ b ∈ B, χ (a + b)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have ha : (A.card : ℝ) ≤ q := by dsimp only [q]; exact_mod_cast Finset.card_le_univ A
  have hb : (B.card : ℝ) ≤ q := by dsimp only [q]; exact_mod_cast Finset.card_le_univ B
  have hc : q * ‖S‖ ^ 2 ≤ m * (q - A.card) * (q - B.card) := by
    exact mulChar_sum_sq_le hχ A B
  have hs : ‖S‖ ^ 2 ≤ m * q := by
    apply le_of_mul_le_mul_left (a := q) _ hq
    calc
      _ ≤ m * (q - A.card) * (q - B.card) := hc
      _ ≤ m * q * q := by
        gcongr <;> linarith
      _ = _ := by ring
  have ht : q * (q ^ δ) ^ 2 ≤ m := by
    change q ^ ((1 : ℝ) + 2 * δ) ≤ m at hsize
    rwa [Real.rpow_add hq, Real.rpow_one, mul_comm (2 : ℝ) δ,
      Real.rpow_mul hq.le, Real.rpow_two] at hsize
  change ‖S‖ ≤ q ^ (-δ) * m
  rw [Real.rpow_neg hq.le, inv_mul_eq_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq δ)).mpr
  apply le_of_sq_le_sq _ hm
  calc
    (‖S‖ * q ^ δ) ^ 2 = ‖S‖ ^ 2 * (q ^ δ) ^ 2 := by rw [mul_pow]
    _ ≤ (m * q) * (q ^ δ) ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = m * (q * (q ^ δ) ^ 2) := mul_assoc _ _ _
    _ ≤ m * m := mul_le_mul_of_nonneg_left ht hm
    _ = m ^ 2 := (pow_two m).symm

private theorem norm_quadCharC_sum (A B : Finset F) :
    ‖∑ a ∈ A, ∑ b ∈ B, quadCharC F (a + b)‖ =
      |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)| := by
  rw [← Complex.norm_intCast]
  simp only [quadCharC_apply, Int.cast_sum]

/-- Integer form of the centered estimate for the quadratic Paley graph. -/
theorem bilinear_sum_sq_le (hF : ringChar F ≠ 2) (A B : Finset F) :
    (Fintype.card F : ℤ) * (∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b)) ^ 2 ≤
      (A.card : ℤ) * B.card * ((Fintype.card F : ℤ) - A.card) *
        ((Fintype.card F : ℤ) - B.card) := by
  have h := mulChar_sum_sq_le (quadCharC_ne_one hF) A B
  rw [norm_quadCharC_sum, sq_abs] at h
  exact_mod_cast h

/-- Dense-set power saving for the quadratic character on an odd finite field. -/
theorem bilinear_sum_power_saving (hF : ringChar F ≠ 2) (A B : Finset F) (δ : ℝ)
    (hsize : (Fintype.card F : ℝ) ^ (1 + 2 * δ) ≤ (A.card : ℝ) * B.card) :
    |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ) ^ (-δ) * ((A.card : ℝ) * B.card) := by
  simpa only [norm_quadCharC_sum] using mulChar_sum_power_saving (quadCharC_ne_one hF) A B δ hsize

/-- The campaign's unconditional Stepanov fourth moment gives cancellation for thin `B`
whenever `|A||B|²` exceeds `17q`, including some pairs with `|A||B| < q`. -/
theorem quadratic_sum_fourth_le (hF : ringChar F ≠ 2) (A B : Finset F)
    (hsmall : (B.card : ℝ) ^ 4 ≤ Fintype.card F) :
    |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)| ^ 4 ≤
      (A.card : ℝ) ^ 3 * (17 * (B.card : ℝ) ^ 2 * Fintype.card F) := by
  classical
  let W : F → ℂ := fun a => ∑ b ∈ B, quadCharC F (a + b)
  have hB : ((B.map (Equiv.neg F).toEmbedding).card : ℝ) ^ 4 ≤ Fintype.card F := by
    simpa using hsmall
  have hfour := R23ParameterChoice.fourthMoment_quadChar_unconditional hF _ hB
  have htotal : ∑ a : F, ‖W a‖ ^ 4 ≤ 17 * (B.card : ℝ) ^ 2 * Fintype.card F := by
    simpa [shiftedCharSum, W, R20QuadFaceBridge.quadCharC_apply, quadCharC_apply] using hfour
  rw [← norm_quadCharC_sum]
  calc
    ‖∑ a ∈ A, W a‖ ^ 4 ≤ (∑ a ∈ A, ‖W a‖) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ (A.card : ℝ) ^ 3 * ∑ a ∈ A, ‖W a‖ ^ 4 :=
      pow_sum_le_card_mul_sum_pow (fun a _ => norm_nonneg (W a)) 3
    _ ≤ (A.card : ℝ) ^ 3 * (∑ a : F, ‖W a‖ ^ 4) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun a _ _ => pow_nonneg (norm_nonneg (W a)) 4)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (by positivity)

/-- Relative power saving in the asymmetric range of the quadratic fourth moment. -/
theorem quadratic_sum_fourth_power_saving (hF : ringChar F ≠ 2) (A B : Finset F) (δ : ℝ)
    (hsmall : (B.card : ℝ) ^ 4 ≤ Fintype.card F)
    (hsize : 17 * (Fintype.card F : ℝ) ^ (1 + 4 * δ) ≤ (A.card : ℝ) * (B.card : ℝ) ^ 2) :
    |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ) ^ (-δ) * ((A.card : ℝ) * B.card) := by
  let q : ℝ := Fintype.card F
  let a : ℝ := A.card
  let b : ℝ := B.card
  let S : ℤ := ∑ x ∈ A, ∑ y ∈ B, quadraticChar F (x + y)
  have hq : 0 < q := by dsimp [q]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ht : 17 * (q * (q ^ δ) ^ 4) ≤ a * b ^ 2 := by
    change 17 * q ^ ((1 : ℝ) + 4 * δ) ≤ a * b ^ 2 at hsize
    rwa [Real.rpow_add hq, Real.rpow_one, mul_comm (4 : ℝ) δ, Real.rpow_mul hq.le,
      show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] at hsize
  change |(S : ℝ)| ≤ q ^ (-δ) * (a * b)
  rw [Real.rpow_neg hq.le, inv_mul_eq_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq δ)).mpr
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (by positivity)
  calc
    (|(S : ℝ)| * q ^ δ) ^ 4 = |(S : ℝ)| ^ 4 * (q ^ δ) ^ 4 := mul_pow _ _ _
    _ ≤ (a ^ 3 * (17 * b ^ 2 * q)) * (q ^ δ) ^ 4 :=
      mul_le_mul_of_nonneg_right (quadratic_sum_fourth_le hF A B hsmall) (by positivity)
    _ = (a ^ 3 * b ^ 2) * (17 * (q * (q ^ δ) ^ 4)) := by ring
    _ ≤ (a ^ 3 * b ^ 2) * (a * b ^ 2) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (a * b) ^ 4 := by ring

/-- Some fixed-size sample has absolute mean at least the absolute mean on the full set.
Count each point in all samples, then take the sample with largest absolute sum. -/
private theorem exists_sample_abs {α : Type*} [DecidableEq α] (B : Finset α) (r : ℕ)
    (hr : 0 < r) (hrB : r ≤ B.card) (f : α → ℝ) :
    ∃ T ⊆ B, T.card = r ∧
      (r : ℝ) * |∑ b ∈ B, f b| ≤ (B.card : ℝ) * |∑ b ∈ T, f b| := by
  classical
  let D := B.powersetCard r
  let c : ℝ := (B.card - 1).choose (r - 1)
  have hD : D.Nonempty := powersetCard_nonempty.mpr hrB
  have hDp : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hcount (g : α → ℝ) : ∑ T ∈ D, ∑ b ∈ T, g b = c * ∑ b ∈ B, g b := by
    have hind (T : Finset α) (hT : T ∈ D) :
        ∑ b ∈ T, g b = ∑ b ∈ B, if b ∈ T then g b else 0 := by
      have hsub := (Finset.mem_powersetCard.mp hT).1
      rw [← Finset.sum_filter]
      congr 1
      ext b
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hsub h, h⟩, And.right⟩
    rw [Finset.sum_congr rfl hind, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    dsimp only [D, c]
    have h := Finset.card_filter_powersetCard_subset ({b} : Finset α) B r
      (by simpa using hb) (by simp only [Finset.card_singleton]; omega)
    simpa using h
  have hcoeff : (D.card : ℝ) * r = c * B.card := by
    have heq : ∑ T ∈ D, ∑ _b ∈ T, (1 : ℝ) = ∑ _T ∈ D, (r : ℝ) := by
      apply Finset.sum_congr rfl
      intro T hT
      simp [(Finset.mem_powersetCard.mp hT).2]
    have h := hcount (fun _ => 1)
    rw [heq] at h
    simpa using h
  obtain ⟨T, hT, hmax⟩ := D.exists_max_image (fun U => |∑ b ∈ U, f b|) hD
  refine ⟨T, (mem_powersetCard.mp hT).1, (mem_powersetCard.mp hT).2, ?_⟩
  have hsum : c * |∑ b ∈ B, f b| ≤ (D.card : ℝ) * |∑ b ∈ T, f b| := by
    have hc : 0 ≤ c := by dsimp [c]; positivity
    calc
      _ = |c * ∑ b ∈ B, f b| := by rw [abs_mul, abs_of_nonneg hc]
      _ = |∑ U ∈ D, ∑ b ∈ U, f b| := congrArg _ (hcount f).symm
      _ ≤ ∑ U ∈ D, |∑ b ∈ U, f b| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _U ∈ D, |∑ b ∈ T, f b| := Finset.sum_le_sum hmax
      _ = _ := by simp
  apply le_of_mul_le_mul_left (a := (D.card : ℝ)) _ hDp
  calc
    _ = (D.card * r : ℝ) * |∑ b ∈ B, f b| := (mul_assoc _ _ _).symm
    _ = B.card * (c * |∑ b ∈ B, f b|) := by rw [hcoeff]; ring
    _ ≤ B.card * (D.card * |∑ b ∈ T, f b|) := by gcongr
    _ = _ := by ring

private theorem exists_quadratic_sample (A B : Finset F) {r : ℕ}
    (hr : 0 < r) (hrB : r ≤ B.card) :
    ∃ T ⊆ B, T.card = r ∧
      (r : ℝ) * |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)| ≤
        B.card * |((∑ a ∈ A, ∑ b ∈ T, quadraticChar F (a + b) : ℤ) : ℝ)| := by
  let f : F → ℝ := fun b => ((∑ a ∈ A, quadraticChar F (a + b) : ℤ) : ℝ)
  have hsum (U : Finset F) : ∑ b ∈ U, f b =
      ((∑ a ∈ A, ∑ b ∈ U, quadraticChar F (a + b) : ℤ) : ℝ) := by
    simp only [f, Int.cast_sum]
    exact Finset.sum_comm
  obtain ⟨T, hT, hcard, h⟩ := exists_sample_abs B r hr hrB f
  exact ⟨T, hT, hcard, by simpa only [hsum] using h⟩

/-- A uniform sample of `r` elements extends the fourth-moment estimate to all `B`.
The normalized fourth power is at most `17q / (|A|r²)` for nonempty `A`. -/
theorem quadratic_sum_sampled_fourth_le (hF : ringChar F ≠ 2) (A B : Finset F) {r : ℕ}
    (hr : 0 < r) (hrB : r ≤ B.card) (hsmall : (r : ℝ) ^ 4 ≤ Fintype.card F) :
    |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)| ^ 4 * (r : ℝ) ^ 2 ≤
      17 * Fintype.card F * (A.card : ℝ) ^ 3 * (B.card : ℝ) ^ 4 := by
  obtain ⟨T, _, hT, hsample⟩ := exists_quadratic_sample A B hr hrB
  have hfour := quadratic_sum_fourth_le hF A T (by simpa only [hT] using hsmall)
  rw [hT] at hfour
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  apply le_of_mul_le_mul_left (a := (r : ℝ) ^ 2) _ (by positivity)
  calc
    _ = ((r : ℝ) * |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)|) ^ 4 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hsample 4
    _ = (B.card : ℝ) ^ 4 * |((∑ a ∈ A, ∑ b ∈ T, quadraticChar F (a + b) : ℤ) : ℝ)| ^ 4 :=
      mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hfour (by positivity : (0 : ℝ) ≤ (B.card : ℝ) ^ 4)
    _ = _ := by ring

/-- Choose the sample size up to `min(|B|, q^(1/4))` in the asymmetric power saving. -/
theorem quadratic_sum_sampled_power_saving (hF : ringChar F ≠ 2) (A B : Finset F) {r : ℕ}
    (δ : ℝ) (hr : 0 < r) (hrB : r ≤ B.card) (hsmall : (r : ℝ) ^ 4 ≤ Fintype.card F)
    (hsize : 17 * (Fintype.card F : ℝ) ^ (1 + 4 * δ) ≤ (A.card : ℝ) * (r : ℝ) ^ 2) :
    |((∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a + b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ) ^ (-δ) * ((A.card : ℝ) * B.card) := by
  obtain ⟨T, _, hT, hsample⟩ := exists_quadratic_sample A B hr hrB
  have hpow := quadratic_sum_fourth_power_saving hF A T δ (by simpa only [hT] using hsmall)
    (by simpa only [hT] using hsize)
  rw [hT] at hpow
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  apply le_of_mul_le_mul_left (a := (r : ℝ)) _ hrpos
  exact hsample.trans ((mul_le_mul_of_nonneg_left hpow (by positivity :
    (0 : ℝ) ≤ B.card)).trans_eq (by ring))

#print axioms mulChar_sum_sq_le
#print axioms mulChar_sum_power_saving
#print axioms bilinear_sum_sq_le
#print axioms bilinear_sum_power_saving
#print axioms quadratic_sum_fourth_le
#print axioms quadratic_sum_fourth_power_saving
#print axioms quadratic_sum_sampled_fourth_le
#print axioms quadratic_sum_sampled_power_saving

end ArkLib.ProximityGap.Frontier.PaleyBilinearDiscrepancy
