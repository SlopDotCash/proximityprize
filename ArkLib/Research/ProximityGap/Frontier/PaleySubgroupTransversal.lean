/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._R16DiagonalExactValue
import ArkLib.Research.ProximityGap.Frontier._R16LegendreCosetFace
import ArkLib.Research.ProximityGap.Frontier._R23ParameterChoice
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Paley discrepancy for sets with bounded multiplicative coset occupancy

For a subgroup `H` in a finite field of odd characteristic, the magnitude of the quadratic
character row on `H` is constant on every multiplicative `H`-coset. A nonzero set `A`
meeting each coset in at most `K` points therefore satisfies
`|S(A,H)|² ≤ K |A| (q−|H|)`. Transversals have `K=1`. The argument also treats any
column set preserved by `H`. A fourth-moment estimate gives a relative power saving
for `A` and `H` of sizes above `q^(1/4+ε)` when `K` is bounded.
-/

namespace ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal

open Finset R16DiagonalExactValue R16LegendreCosetFace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The multiplicative coset at `x`, represented as a finite set of field elements. -/
def coset (H : Finset F) (x : F) : Finset F := H.image (· * x)

private theorem mem_coset_symm {H : Finset F} (hH : IsMulSubgroup H) {a x : F}
    (hx : x ∈ coset H a) : a ∈ coset H x := by
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
  exact mem_image.mpr ⟨u⁻¹, hH.inv_mem u hu, inv_mul_cancel_left₀ (ne_zero_of_mem hH hu) a⟩

/-- For an invariant column set `B`, the full row energy bounds the energy sampled by `A`.
The factor `K` counts the maximum number of sample points in a multiplicative coset. -/
theorem stabilized_sum_sq_le (hF : ringChar F ≠ 2) (A B H : Finset F)
    (hH : IsMulSubgroup H) (hB : Stabilizes H B) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) :
    (H.card : ℤ) * (∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a - b)) ^ 2 ≤
      A.card * (K : ℤ) * B.card * ((Fintype.card F : ℤ) - B.card) := by
  classical
  let W := shiftedCharSum (quadraticChar F) B
  have hrow (a x : F) (hx : x ∈ coset H a) : W x ^ 2 = W a ^ 2 := by
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    have hu₀ := ne_zero_of_mem hH hu
    have hstable (y : F) : u * y ∈ B ↔ y ∈ B := by
      refine ⟨fun hy => ?_, hB u hu y⟩
      simpa only [inv_mul_cancel_left₀ hu₀] using hB u⁻¹ (hH.inv_mem u hu) (u*y) hy
    dsimp only [W]
    rw [shiftedCharSum_mul_left _ _ _ _ hu₀ hstable, mul_pow, quadraticChar_sq_one hu₀, one_mul]
  have hcount (a : F) (ha : a ∈ A) :
      (H.card : ℤ) * W a ^ 2 = ∑ x : F, if a ∈ coset H x then W x ^ 2 else 0 := by
    have ha₀ : a ≠ 0 := fun he => hA (he ▸ ha)
    have hcard : (coset H a).card = H.card :=
      card_image_of_injective _ (mul_left_injective₀ ha₀)
    have hflip (x : F) : a ∈ coset H x ↔ x ∈ coset H a :=
      ⟨mem_coset_symm hH, mem_coset_symm hH⟩
    simp_rw [hflip]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_congr rfl (fun x hx => hrow a x hx), Finset.sum_const, nsmul_eq_mul, hcard]
  have henergy : (H.card : ℤ) * (∑ a ∈ A, W a ^ 2) ≤
      K * ((B.card : ℤ) * ((Fintype.card F : ℤ) - B.card)) := calc
    _ = ∑ a ∈ A, ∑ x : F, if a ∈ coset H x then W x ^ 2 else 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hcount
    _ = ∑ x : F, ((A ∩ coset H x).card : ℤ) * W x ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x : F, (K : ℤ) * W x ^ 2 := by
      exact Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast hK x) (sq_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum, show ∑ x : F, W x ^ 2 =
        (B.card : ℤ) * (Fintype.card F : ℤ) - (B.card : ℤ)^2 from sum_sq_shiftedQuadSum hF B]
      ring
  calc
    _ ≤ (H.card : ℤ) * ((A.card : ℤ) * ∑ a ∈ A, W a ^ 2) :=
      mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq (by positivity)
    _ = (A.card : ℤ) * ((H.card : ℤ) * ∑ a ∈ A, W a ^ 2) := by ring
    _ ≤ (A.card : ℤ) * (K * ((B.card : ℤ) * ((Fintype.card F : ℤ) - B.card))) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

/-- Fixed-placement discrepancy with a subgroup on one side and coset occupancy at most `K`. -/
theorem subgroup_sum_sq_le (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) :
    (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a - b)) ^ 2 ≤
      A.card * (K : ℤ) * ((Fintype.card F : ℤ) - H.card) := by
  have hp : (0 : ℤ) < H.card := by exact_mod_cast card_pos.mpr ⟨1, hH.one_mem⟩
  apply le_of_mul_le_mul_left (a := (H.card : ℤ)) _ hp
  calc
    _ ≤ (A.card : ℤ) * K * H.card * ((Fintype.card F : ℤ) - H.card) :=
      stabilized_sum_sq_le hF A H H hH hH.mul_mem hA K hK
    _ = _ := by ring

/-- A partial transversal of the nonzero multiplicative cosets satisfies the `K=1` bound. -/
theorem transversal_sum_sq_le (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A)
    (htrans : ∀ x : F, (A ∩ coset H x).card ≤ 1) :
    (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a - b)) ^ 2 ≤
      (A.card : ℤ) * ((Fintype.card F : ℤ) - H.card) := by
  simpa using subgroup_sum_sq_le hF A H hH hA 1 htrans

/-- Exact signed recovery of a subgroup row from the rows of any sample inside the subgroup. -/
theorem sum_weighted_sample_rows (H T : Finset F) (hH : IsMulSubgroup H) (hT : T ⊆ H) (a : F) :
    ∑ u ∈ H, quadraticChar F u * shiftedCharSum (quadraticChar F) T (u * a) =
      (T.card : ℤ) * shiftedCharSum (quadraticChar F) H a := by
  classical
  simp_rw [shiftedCharSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (b : F) (hb : b ∈ T) :
      ∑ u ∈ H, quadraticChar F u * quadraticChar F (u * a - b) =
        ∑ y ∈ H, quadraticChar F (a - y) := by
    have hbH := hT hb
    have hb₀ := ne_zero_of_mem hH hbH
    refine Finset.sum_nbij' (fun u => b / u) (fun y => b / y) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      exact div_eq_mul_inv b u ▸ hH.mul_mem _ hbH _ (hH.inv_mem u hu)
    · intro y hy
      exact div_eq_mul_inv b y ▸ hH.mul_mem _ hbH _ (hH.inv_mem y hy)
    · intro u hu
      field_simp [hb₀, ne_zero_of_mem hH hu]
    · intro y hy
      field_simp [hb₀, ne_zero_of_mem hH hy]
    · intro u hu
      have hu₀ := ne_zero_of_mem hH hu
      rw [show u*a - b = u*(a - b/u) by field_simp [hu₀], map_mul,
        ← mul_assoc, ← pow_two, quadraticChar_sq_one hu₀, one_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]

/-- The fourth-moment constant supplied by the campaign's finite-field Stepanov estimate. -/
def fourthConstant (q : ℕ) : ℕ := if 3251 ≤ q then 11 else 17

/-- The integer-valued fourth moment for an arbitrary sample of at most fourth-root size. -/
theorem fourth_moment (hF : ringChar F ≠ 2) (T : Finset F)
    (hsmall : T.card ^ 4 ≤ Fintype.card F) :
    ∑ x : F, (shiftedCharSum (quadraticChar F) T x) ^ 4 ≤
      (fourthConstant (Fintype.card F) : ℤ) * (T.card : ℤ) ^ 2 * Fintype.card F := by
  have ht : (T.card : ℝ) ^ 4 ≤ (Fintype.card F : ℝ) := by exact_mod_cast hsmall
  have hm : ∑ x : F, ‖shiftedCharSum (R20QuadFaceBridge.quadCharC F) T x‖ ^ 4 ≤
      (fourthConstant (Fintype.card F) : ℝ) * (T.card : ℝ)^2 * Fintype.card F := by
    by_cases hq : 3251 ≤ Fintype.card F
    · simpa [fourthConstant, hq] using
        R23ParameterChoice.fourthMoment_quadChar_tight_of_large hF hq T ht
    · simpa [fourthConstant, hq] using
        R23ParameterChoice.fourthMoment_quadChar_unconditional hF T ht
  have hterm (x : F) : ‖shiftedCharSum (R20QuadFaceBridge.quadCharC F) T x‖ ^ 4 =
      ((shiftedCharSum (quadraticChar F) T x : ℤ) : ℝ)^4 := by
    have heq : shiftedCharSum (R20QuadFaceBridge.quadCharC F) T x =
        ((shiftedCharSum (quadraticChar F) T x : ℤ) : ℂ) := by
      simp only [shiftedCharSum, R20QuadFaceBridge.quadCharC_apply, Int.cast_sum]
    rw [heq, Complex.norm_intCast, (show Even 4 by decide).pow_abs]
  simp only [hterm] at hm
  exact_mod_cast hm

/-- Signed row weights survive the subgroup sampling identity and disappear from its fourth moment. -/
theorem weighted_subgroup_sum_fourth_le (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) (r : ℕ)
    (hr : 0 < r) (hrH : r ≤ H.card) (hsmall : r ^ 4 ≤ Fintype.card F)
    (w : F → ℤ) (hw : ∀ a ∈ A, w a ^ 4 = 1) :
    (∑ a ∈ A, w a * ∑ b ∈ H, quadraticChar F (a - b)) ^ 4 * (r : ℤ)^2 ≤
      ((A.card : ℤ) * H.card)^3 * K * fourthConstant (Fintype.card F) * Fintype.card F := by
  classical
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hrH
  let W := shiftedCharSum (quadraticChar F) T
  let G (z : F × F) := w z.1 * (quadraticChar F z.2 * W (z.2 * z.1))
  let S := ∑ a ∈ A, w a * ∑ b ∈ H, quadraticChar F (a-b)
  let D := A ×ˢ H
  have hrecover : (r : ℤ) * S = ∑ z ∈ D, G z := by
    rw [Finset.sum_product]
    dsimp only [S]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      simp only [G, ← Finset.mul_sum]
      rw [mul_left_comm]
      congr 1
      simpa only [W, hcard, shiftedCharSum] using (sum_weighted_sample_rows H T hH hT a).symm
  have hcover : ∑ z ∈ D, G z ^ 4 ≤ (K : ℤ) * ∑ x : F, W x ^ 4 := calc
    _ = ∑ a ∈ A, ∑ u ∈ H, W (u*a)^4 := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro u hu
      change (w a * (quadraticChar F u * W (u*a)))^4 = W (u*a)^4
      rw [mul_pow, hw a ha, one_mul]
      rcases quadraticChar_dichotomy (ne_zero_of_mem hH hu) with hc | hc <;> rw [hc] <;> ring
    _ = ∑ a ∈ A, ∑ x : F, if a ∈ coset H x then W x ^ 4 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha₀ : a ≠ 0 := fun he => hA (he ▸ ha)
      have hflip (x : F) : a ∈ coset H x ↔ x ∈ coset H a :=
        ⟨mem_coset_symm hH, mem_coset_symm hH⟩
      simp_rw [hflip]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      unfold coset
      rw [Finset.sum_image (mul_left_injective₀ ha₀).injOn]
    _ = ∑ x : F, ((A ∩ coset H x).card : ℤ) * W x ^ 4 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hK x) ((show Even 4 by decide).pow_nonneg _)
  have hfour : (∑ z ∈ D, G z)^4 ≤ (D.card : ℤ)^3 * ∑ z ∈ D, G z ^ 4 := calc
    _ = |∑ z ∈ D, G z|^4 := ((show Even 4 by decide).pow_abs _).symm
    _ ≤ (∑ z ∈ D, |G z|)^4 :=
      pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs ..) 4
    _ ≤ (D.card : ℤ)^3 * ∑ z ∈ D, |G z|^4 := pow_sum_le_card_mul_sum_pow (fun _ _ => abs_nonneg _) 3
    _ = _ := by simp only [(show Even 4 by decide).pow_abs]
  have hmoment : ∑ x : F, W x ^ 4 ≤
      (fourthConstant (Fintype.card F) : ℤ) * (r : ℤ)^2 * Fintype.card F := by
    simpa only [W, hcard] using fourth_moment hF T (by rwa [hcard])
  have hrpos : 0 < (r : ℤ)^2 := by positivity
  apply le_of_mul_le_mul_right (a := (r : ℤ)^2) _ hrpos
  calc
    _ = ((r : ℤ) * S)^4 := by ring
    _ = (∑ z ∈ D, G z)^4 := by rw [hrecover]
    _ ≤ (D.card : ℤ)^3 * ∑ z ∈ D, G z ^ 4 := hfour
    _ ≤ (D.card : ℤ)^3 * ((K : ℤ) * ∑ x : F, W x ^ 4) :=
      mul_le_mul_of_nonneg_left hcover (by positivity)
    _ ≤ (D.card : ℤ)^3 * ((K : ℤ) *
        ((fourthConstant (Fintype.card F) : ℤ) * (r : ℤ)^2 * Fintype.card F)) := by
      gcongr
    _ = _ := by simp only [D, Finset.card_product, Nat.cast_mul]; ring

/-- A fixed set with coset occupancy `K` against a subgroup, by signed amplification of
a sample of size `r` and the quadratic fourth moment. -/
theorem subgroup_sum_fourth_le (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) (r : ℕ)
    (hr : 0 < r) (hrH : r ≤ H.card) (hsmall : r ^ 4 ≤ Fintype.card F) :
    (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a - b)) ^ 4 * (r : ℤ)^2 ≤
      ((A.card : ℤ) * H.card)^3 * K * fourthConstant (Fintype.card F) * Fintype.card F := by
  simpa using weighted_subgroup_sum_fourth_le hF A H hH hA K hK r hr hrH hsmall
    (fun _ => 1) (by simp)

/-- A relative power saving whenever `K C q^(1+4δ) ≤ |A||H| r²`. -/
theorem power_saving_of_fourth_estimate (A H : Finset F) (K r : ℕ) (δ : ℝ)
    (hr : 0 < r)
    (hbound : (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b))^4 * (r : ℤ)^2 ≤
      ((A.card : ℤ) * H.card)^3 * K * fourthConstant (Fintype.card F) * Fintype.card F)
    (hsize : (K : ℝ) * fourthConstant (Fintype.card F) *
        (Fintype.card F : ℝ) ^ (1 + 4*δ) ≤ (A.card : ℝ) * H.card * (r : ℝ)^2) :
    |((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a - b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ)^(-δ) * ((A.card : ℝ) * H.card) := by
  let q : ℝ := Fintype.card F
  let m : ℝ := (A.card : ℝ) * H.card
  let C : ℝ := fourthConstant (Fintype.card F)
  let S : ℤ := ∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a - b)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast hr
  have hfour : (S : ℝ)^4 * (r : ℝ)^2 ≤ m^3 * K * C * q := by
    dsimp only [S, m, C, q]
    exact_mod_cast hbound
  have ht : (K : ℝ) * C * (q*(q^δ)^4) ≤ m*(r : ℝ)^2 := by
    change (K : ℝ) * C * q^((1 : ℝ) + 4*δ) ≤ m*(r : ℝ)^2 at hsize
    rwa [Real.rpow_add hq, Real.rpow_one, mul_comm (4 : ℝ) δ,
      Real.rpow_mul hq.le, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] at hsize
  change |(S : ℝ)| ≤ q^(-δ) * m
  rw [Real.rpow_neg hq.le, inv_mul_eq_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq δ)).mpr
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) hm
  apply le_of_mul_le_mul_right (a := (r : ℝ)^2) _ (sq_pos_of_pos hr₀)
  calc
    _ = ((S : ℝ)^4 * (r : ℝ)^2) * (q^δ)^4 := by
      rw [mul_pow, (show Even 4 by decide).pow_abs]; ring
    _ ≤ (m^3 * K * C * q) * (q^δ)^4 :=
      mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = m^3 * (K * C * (q * (q^δ)^4)) := by ring
    _ ≤ m^3 * (m*(r : ℝ)^2) := mul_le_mul_of_nonneg_left ht (pow_nonneg hm _)
    _ = _ := by ring

/-- The subgroup fourth moment gives an explicit relative power saving. -/
theorem subgroup_power_saving (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) (r : ℕ) (δ : ℝ)
    (hr : 0 < r) (hrH : r ≤ H.card) (hsmall : r ^ 4 ≤ Fintype.card F)
    (hsize : (K : ℝ) * fourthConstant (Fintype.card F) *
        (Fintype.card F : ℝ) ^ (1 + 4*δ) ≤ (A.card : ℝ) * H.card * (r : ℝ)^2) :
    |((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a - b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ)^(-δ) * ((A.card : ℝ) * H.card) :=
  power_saving_of_fourth_estimate A H K r δ hr
    (subgroup_sum_fourth_le hF A H hH hA K hK r hr hrH hsmall) hsize

/-- Sampling at the floor of the real fourth root gives a relative power saving from
a uniform family of finite fourth-moment estimates at the supplied coordinates. -/
theorem quarter_power_saving_of_fourth_estimates (A H : Finset F) (K : ℕ)
    (hbound : ∀ r : ℕ, 0 < r → r ≤ H.card → r^4 ≤ Fintype.card F →
      (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b))^4 * (r : ℤ)^2 ≤
        ((A.card : ℤ) * H.card)^3 * K * fourthConstant (Fintype.card F) * Fintype.card F)
    (ε : ℝ) (hε : 0 < ε)
    (ha : (Fintype.card F : ℝ)^(1/4+ε) ≤ A.card)
    (hh : (Fintype.card F : ℝ)^(1/4+ε) ≤ H.card)
    (hc : 4 * (fourthConstant (Fintype.card F) : ℝ) * K ≤ (Fintype.card F : ℝ)^ε) :
    |((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ)^(-(ε/4)) * ((A.card : ℝ) * H.card) := by
  let q : ℝ := Fintype.card F
  let t := q^(1/4 : ℝ)
  let r := ⌊t⌋₊
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (Fintype.card_pos (α := F))
  have hqpos : 0 < q := by linarith
  have ht : 1 ≤ t := Real.one_le_rpow hq (by norm_num)
  have hr : 0 < r := Nat.floor_pos.mpr ht
  have hr_le : (r : ℝ) ≤ t := Nat.floor_le (by linarith)
  have ht_le : t ≤ 2*(r : ℝ) := by
    have hnear := Nat.lt_floor_add_one t
    have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    change t < (r : ℝ) + 1 at hnear
    linarith
  have ht4 : t^4 = q := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
    norm_num
  have hrsmall : r^4 ≤ Fintype.card F := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r) hr_le 4
    rw [ht4] at h
    dsimp only [q] at h
    exact_mod_cast h
  have htH : t ≤ H.card := le_trans (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) hh
  have hrH : r ≤ H.card := by exact_mod_cast hr_le.trans htH
  apply power_saving_of_fourth_estimate A H K r (ε/4) hr (hbound r hr hrH hrsmall)
  change (K : ℝ) * fourthConstant (Fintype.card F) * q^(1+4*(ε/4)) ≤ _
  let v := q^ε
  have hv : 0 < v := Real.rpow_pos_of_pos hqpos _
  change 4 * (fourthConstant (Fintype.card F) : ℝ) * K ≤ v at hc
  have ha' : t*v ≤ A.card := by simpa only [t, v, q, ← Real.rpow_add hqpos] using ha
  have hh' : t*v ≤ H.card := by simpa only [t, v, q, ← Real.rpow_add hqpos] using hh
  have hrr : t^2 ≤ 4*(r : ℝ)^2 := by
    nlinarith only [sq_le_sq' (by linarith : -(2*(r : ℝ)) ≤ t) ht_le]
  rw [show (1:ℝ)+4*(ε/4)=1+ε by ring, Real.rpow_add hqpos, Real.rpow_one]
  change _ * _ * (q*v) ≤ _
  apply (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 4)).mp
  calc
    _ = (4*(fourthConstant (Fintype.card F) : ℝ)*K) * (q*v) := by ring
    _ ≤ v * (q*v) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (t*v)*(t*v)*t^2 := by rw [← ht4]; ring
    _ ≤ (A.card : ℝ)*H.card*(4*(r : ℝ)^2) := by
      apply mul_le_mul _ hrr (sq_nonneg _) (by positivity)
      exact mul_le_mul ha' hh' (by positivity) (by positivity)
    _ = _ := by ring

/-- Quarter-scale cancellation under the pointwise occupancy bound. -/
theorem subgroup_quarter_power_saving (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (hK : ∀ x : F, (A ∩ coset H x).card ≤ K) (ε : ℝ) (hε : 0 < ε)
    (ha : (Fintype.card F : ℝ)^(1/4+ε) ≤ A.card)
    (hh : (Fintype.card F : ℝ)^(1/4+ε) ≤ H.card)
    (hc : 4 * (fourthConstant (Fintype.card F) : ℝ) * K ≤ (Fintype.card F : ℝ)^ε) :
    |((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ)^(-(ε/4)) * ((A.card : ℝ) * H.card) :=
  quarter_power_saving_of_fourth_estimates A H K
    (subgroup_sum_fourth_le hF A H hH hA K hK) ε hε ha hh hc

/-- Half the trivial bound on a prescribed transversal, using the entire subgroup as
the fourth-moment sample. Both named production fields meet the size assumptions with
`H.card = 2^30` and `A.card = 2^77`. -/
theorem transversal_half_bound (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A)
    (htrans : ∀ x : F, (A ∩ coset H x).card ≤ 1)
    (hsmall : H.card ^ 4 ≤ Fintype.card F) (hq : 3251 ≤ Fintype.card F)
    (hsize : 176 * Fintype.card F ≤ A.card * H.card ^ 3) :
    2 * |∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b)| ≤ (A.card : ℤ) * H.card := by
  let S := ∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b)
  have hpos : 0 < H.card := card_pos.mpr ⟨1, hH.one_mem⟩
  have hfour := subgroup_sum_fourth_le hF A H hH hA 1 htrans H.card hpos le_rfl hsmall
  simp only [fourthConstant, hq, ↓reduceIte, Nat.cast_one, mul_one] at hfour
  change S^4 * (H.card : ℤ)^2 ≤ ((A.card : ℤ) * H.card)^3 * 11 * Fintype.card F at hfour
  have hs : 176 * (Fintype.card F : ℤ) ≤ (A.card : ℤ) * H.card^3 := by exact_mod_cast hsize
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (by positivity)
  apply le_of_mul_le_mul_right (a := (H.card : ℤ)^2) _ (by positivity)
  calc
    _ = 16*(S^4*(H.card : ℤ)^2) := by rw [mul_pow, (show Even 4 by decide).pow_abs]; ring
    _ ≤ 16*(((A.card : ℤ)*H.card)^3 * 11 * Fintype.card F) := by gcongr
    _ = ((A.card : ℤ)*H.card)^3 * (176*Fintype.card F) := by ring
    _ ≤ ((A.card : ℤ)*H.card)^3 * (A.card*H.card^3) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Numerical hypotheses of the half-discrepancy bound on the two named prize moduli. -/
theorem named_prime_sizes {q : ℕ}
    (hp : q = 365375409332725729550921208179070755120141565953 ∨
          q = 730750818665451459101842416358141509841924915201) :
    (2^30)^4 ≤ q ∧ 3251 ≤ q ∧ 176*q ≤ 2^77*(2^30)^3 ∧ (2^77)^2 < q := by
  rcases hp with rfl | rfl <;> decide

/-- Actual prescribed rectangles at the two production moduli have at most half their
trivial discrepancy for any transversal of size at least `2^77`. -/
theorem named_prime_half (hF : ringChar F ≠ 2)
    (hp : Fintype.card F = 365375409332725729550921208179070755120141565953 ∨
          Fintype.card F = 730750818665451459101842416358141509841924915201)
    (A H : Finset F) (hH : IsMulSubgroup H) (hh : H.card = 2^30)
    (hA : (0 : F) ∉ A) (ha : 2^77 ≤ A.card)
    (htrans : ∀ x : F, (A ∩ coset H x).card ≤ 1) :
    2 * |∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b)| ≤ (A.card : ℤ)*H.card := by
  obtain ⟨hr, hq, hc, _⟩ := named_prime_sizes hp
  apply transversal_half_bound hF A H hH hA htrans (by rwa [hh]) hq
  rw [hh]
  exact hc.trans (Nat.mul_le_mul_right _ ha)

end ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.stabilized_sum_sq_le
#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.subgroup_sum_sq_le
#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.transversal_sum_sq_le

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.sum_weighted_sample_rows
#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.subgroup_sum_fourth_le
#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.subgroup_power_saving

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.subgroup_quarter_power_saving

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.transversal_half_bound
#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.named_prime_sizes

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal.named_prime_half
