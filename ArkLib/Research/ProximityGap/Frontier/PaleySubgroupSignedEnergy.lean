/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleySubgroupTransversal
import Mathlib.Analysis.MeanInequalities

/-!
# Paley discrepancy from the signed occupancies of multiplicative cosets

A coset's contribution depends on the difference between its numbers of square
and nonsquare sites. The fourth moment allows high occupancy on exceptional cosets
if the total squared signed occupancy is small.
-/

namespace ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy

open Finset R16DiagonalExactValue R16LegendreCosetFace PaleySubgroupTransversal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Sum of site signs in `A ∩ xH`, indexed by field elements. Consequently each
nonzero coset occurs `H.card` times in a sum over the index. -/
def signedOccupancy (A H : Finset F) (x : F) : ℤ :=
  ∑ a ∈ A ∩ coset H x, quadraticChar F a

private theorem flip (H : Finset F) (hH : IsMulSubgroup H) (x a : F) :
    a ∈ coset H x ↔ x ∈ coset H a := by
  have symm {x a : F} (h : a ∈ coset H x) : x ∈ coset H a := by
    obtain ⟨u,hu,rfl⟩ := mem_image.mp h
    exact mem_image.mpr ⟨u⁻¹,hH.inv_mem u hu,inv_mul_cancel_left₀ (ne_zero_of_mem hH hu) x⟩
  exact ⟨symm,symm⟩

/-- Grouping the amplified rows by field site gives the signed occupancies
times one quadratic sign per output site. -/
theorem signed_recovery (A H T : Finset F) (hH : IsMulSubgroup H) (hT : T ⊆ H)
    (hA : (0 : F) ∉ A) :
    (T.card : ℤ) * (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b)) =
      ∑ x : F, signedOccupancy A H x *
        (quadraticChar F x * shiftedCharSum (quadraticChar F) T x) := by
  classical
  let W := shiftedCharSum (quadraticChar F) T
  have hrow (a : F) (ha : a ∈ A) :
      (∑ u ∈ H, quadraticChar F u * W (u*a)) =
      ∑ x : F, if a ∈ coset H x then quadraticChar F a * (quadraticChar F x * W x) else 0 := by
    have ha₀ : a ≠ 0 := fun he => hA (he ▸ ha)
    simp_rw [flip H hH _ a]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    unfold coset
    rw [Finset.sum_image (mul_left_injective₀ ha₀).injOn]
    apply Finset.sum_congr rfl
    intro u _
    rw [map_mul, show ∀ v w t : ℤ, v*((w*v)*t)=v^2*(w*t) by intros; ring,
      quadraticChar_sq_one ha₀, one_mul]
  rw [Finset.mul_sum]
  change (∑ a ∈ A, (T.card : ℤ) * shiftedCharSum (quadraticChar F) H a) = _
  simp_rw [← sum_weighted_sample_rows H T hH hT]
  change (∑ a ∈ A, ∑ u ∈ H, quadraticChar F u * W (u*a)) = _
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, signedOccupancy, Finset.sum_mul]

/-- A repeated weighted Cauchy–Schwarz inequality over integers. -/
private theorem fourth_weighted {ι : Type*} (s : Finset ι) (d w : ι → ℤ) :
    (∑ x ∈ s, d x * w x)^4 ≤ (∑ x ∈ s, |d x|)^2 *
      (∑ x ∈ s, d x^2) * ∑ x ∈ s, w x^4 := by
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (r := fun x => d x*w x)
    (f := fun x => |d x|) (g := fun x => |d x| * w x^2)
    (fun x _ => abs_nonneg _) (fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun x _ => (by rw [mul_pow, ← mul_assoc, ← pow_two, sq_abs]))
  have ht := Finset.sum_mul_sq_le_sq_mul_sq s (fun x => |d x|) (fun x => w x^2)
  simp only [sq_abs, ← pow_mul] at ht
  calc
    _ = ((∑ x ∈ s, d x*w x)^2)^2 := by ring
    _ ≤ ((∑ x ∈ s, |d x|) * ∑ x ∈ s, |d x| * w x^2)^2 :=
      pow_le_pow_left₀ (sq_nonneg _) hs 2
    _ = (∑ x ∈ s, |d x|)^2 * (∑ x ∈ s, |d x| * w x^2)^2 := mul_pow _ _ _
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ht (sq_nonneg _)

private theorem char_fourth_le (x : F) (w : ℤ) :
    (quadraticChar F x * w)^4 ≤ w^4 := by
  by_cases hx : x = 0
  · simp only [hx, quadraticChar_zero, zero_mul, zero_pow (by decide : 4 ≠ 0)]
    exact (show Even 4 by decide).pow_nonneg _
  · rcases quadraticChar_dichotomy hx with h|h <;> rw [h] <;> apply le_of_eq <;> ring

private theorem twisted_fourth_moment (hF : ringChar F ≠ 2) (T : Finset F) {r : ℕ}
    (hcard : T.card = r) (hr : r^4 ≤ Fintype.card F) :
    ∑ x : F, (quadraticChar F x * shiftedCharSum (quadraticChar F) T x)^4 ≤
      (fourthConstant (Fintype.card F) : ℤ) * (r : ℤ)^2 * Fintype.card F := by
  refine (Finset.sum_le_sum (fun x _ => char_fourth_le x _)).trans ?_
  simpa only [hcard] using fourth_moment hF T (by rwa [hcard])

/-- Fourth moment using the actual signed mass and energy. All three sums of
occupancies and rows are over field elements, including representatives of empty cosets. -/
theorem fourth_signed_energy (hF : ringChar F ≠ 2) (A H : Finset F) (hH : IsMulSubgroup H)
    (hA : (0 : F) ∉ A) (r : ℕ) (hr : 0 < r) (hrH : r ≤ H.card)
    (hsmall : r^4 ≤ Fintype.card F) :
    (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b))^4 * (r : ℤ)^2 ≤
      (∑ x : F, |signedOccupancy A H x|)^2 * (∑ x : F, signedOccupancy A H x^2) *
      fourthConstant (Fintype.card F) * Fintype.card F := by
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hrH
  let S := ∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b)
  let d := signedOccupancy A H
  let W := shiftedCharSum (quadraticChar F) T
  let w := fun x => quadraticChar F x * W x
  have hs : (r : ℤ)*S = ∑ x, d x*w x := by
    simpa only [hcard] using signed_recovery A H T hH hT hA
  have hmoment : ∑ x : F, w x^4 ≤
      (fourthConstant (Fintype.card F) : ℤ) * (r : ℤ)^2 * Fintype.card F :=
    twisted_fourth_moment hF T hcard hsmall
  apply le_of_mul_le_mul_right (a := (r : ℤ)^2) _ (by positivity)
  calc
    _ = ((r : ℤ) * S)^4 := by ring
    _ = (∑ x : F, d x*w x)^4 := by rw [hs]
    _ ≤ (∑ x : F, |d x|)^2 * (∑ x : F, d x^2) * ∑ x : F, w x^4 :=
      fourth_weighted univ d w
    _ ≤ (∑ x : F, |d x|)^2 * (∑ x : F, d x^2) *
        ((fourthConstant (Fintype.card F) : ℤ) * (r : ℤ)^2 * Fintype.card F) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by dsimp only [d]; ring

/-- Each nonzero sample site belongs to exactly the subgroup size many
field-indexed cosets. -/
theorem sum_occupancies (A H : Finset F) (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) :
    (∑ x : F, ((A ∩ coset H x).card : ℤ)) = (H.card : ℤ) * A.card := by
  classical
  calc
    _ = ∑ a ∈ A, ∑ x : F, if a ∈ coset H x then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
      simp
    _ = _ := by
      have hrow (a : F) (ha : a ∈ A) :
          (∑ x : F, if a ∈ coset H x then (1 : ℤ) else 0) = H.card := by
        have ha₀ : a ≠ 0 := fun he => hA (he ▸ ha)
        simp_rw [flip H hH _ a]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        simp [coset, card_image_of_injective _ (mul_left_injective₀ ha₀)]
      rw [Finset.sum_congr rfl hrow]
      simp [mul_comm]

/-- Summed over field elements, the signed mass is at most the subgroup size times
the number of sample points. -/
theorem signed_mass_le (A H : Finset F) (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) :
    (∑ x : F, |signedOccupancy A H x|) ≤ (H.card : ℤ) * A.card := by
  classical
  calc
    _ ≤ ∑ x : F, ((A ∩ coset H x).card : ℤ) := by
      apply Finset.sum_le_sum
      intro x _
      apply (Finset.abs_sum_le_sum_abs ..).trans
      calc
        _ ≤ ∑ _a ∈ A ∩ coset H x, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro a ha
          have ha₀ : a ≠ 0 := fun he => hA (he ▸ (mem_inter.mp ha).1)
          rcases quadraticChar_dichotomy ha₀ with hs|hs <;> rw [hs] <;> decide
        _ = _ := by simp
    _ = _ := sum_occupancies A H hH hA

/-- The occupied cosets may be arbitrarily large when their collective signed energy is
small. This gives the same fourth-moment estimate as a pointwise occupancy cap. -/
theorem fourth_of_signed_energy (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (henergy : ∑ x : F, signedOccupancy A H x^2 ≤ (K : ℤ)*H.card*A.card)
    (r : ℕ) (hr : 0 < r) (hrH : r ≤ H.card) (hsmall : r^4 ≤ Fintype.card F) :
    (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b))^4 * (r : ℤ)^2 ≤
      ((A.card : ℤ)*H.card)^3 * K * fourthConstant (Fintype.card F) * Fintype.card F := by
  apply (fourth_signed_energy hF A H hH hA r hr hrH hsmall).trans
  have hmass := signed_mass_le A H hH hA
  calc
    _ ≤ ((H.card : ℤ)*A.card)^2 * ((K : ℤ)*H.card*A.card) *
        fourthConstant (Fintype.card F) * Fintype.card F := by gcongr
    _ = _ := by ring

private theorem fourth_holder {ι : Type*} (s : Finset ι) (d w : ι → ℝ) :
    (∑ x ∈ s, d x * w x)^4 ≤ (∑ x ∈ s, |d x| ^ (4/3 : ℝ))^3 * ∑ x ∈ s, w x^4 := by
  have hc : Real.HolderConjugate (4/3) 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq s (fun x => |d x|) (fun x => |w x|) hc
  simp only [abs_abs, ← abs_mul] at h
  have habs := (Finset.abs_sum_le_sum_abs (fun i => d i * w i) s).trans h
  have hpower (x : ℝ) (hx : 0 ≤ x) (c : ℝ) : (x^c)^4 = x^(c*(4:ℝ)) := by
    calc
      _ = (x^c)^(4:ℝ) := (Real.rpow_natCast _ 4).symm
      _ = _ := (Real.rpow_mul hx _ _).symm
  have h4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
  rw [(show Even 4 by decide).pow_abs, mul_pow, hpower _ (by positivity), hpower _ (by positivity)]
    at h4
  convert h4 using 1
  congr 1
  · rw [show ((1/(4/3:ℝ))*4) = 3 by norm_num, ← Real.rpow_natCast]
    norm_num
  · rw [show ((1/(4:ℝ))*4) = 1 by norm_num, Real.rpow_one]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (4:ℝ) = (4:ℕ) by norm_num, Real.rpow_natCast, (show Even 4 by decide).pow_abs]

/-- The dual fourth-moment bound uses the exact ℓ^(4/3) norm of the signed occupancies.
No bound on the cardinality of an individual intersection `A ∩ xH` is required. -/
theorem fourth_signed_holder (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A)
    (r : ℕ) (hr : 0 < r) (hrH : r ≤ H.card) (hsmall : r^4 ≤ Fintype.card F) :
    ((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b) : ℤ) : ℝ)^4 * (r : ℝ)^2 ≤
      (∑ x : F, |(signedOccupancy A H x : ℝ)| ^ (4/3 : ℝ))^3 *
        fourthConstant (Fintype.card F) * Fintype.card F := by
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hrH
  let d := signedOccupancy A H
  let w (x : F) := quadraticChar F x * shiftedCharSum (quadraticChar F) T x
  let S := ∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b)
  have hs : (r : ℝ) * S = ∑ x : F, (d x : ℝ) * w x := by
    exact_mod_cast (show (r : ℤ) * S = ∑ x : F, d x * w x by
      simpa only [hcard] using signed_recovery A H T hH hT hA)
  have hmoment : ∑ x : F, (w x : ℝ)^4 ≤
      (fourthConstant (Fintype.card F) : ℝ) * (r : ℝ)^2 * Fintype.card F := by
    exact_mod_cast twisted_fourth_moment hF T hcard hsmall
  let D := ∑ x : F, |(d x : ℝ)| ^ (4/3 : ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
  apply le_of_mul_le_mul_right (a := (r : ℝ)^2) _ (by positivity)
  calc
    _ = ((r : ℝ) * S)^4 := by ring
    _ = (∑ x : F, (d x : ℝ)*w x)^4 := by rw [hs]
    _ ≤ D^3 * ∑ x : F, (w x : ℝ)^4 := fourth_holder univ (fun x => d x) (fun x => w x)
    _ ≤ D^3 * ((fourthConstant (Fintype.card F) : ℝ) * (r : ℝ)^2 * Fintype.card F) :=
      mul_le_mul_of_nonneg_left hmoment (pow_nonneg hD _)
    _ = _ := by dsimp only [D,d]; ring

/-- A coset of any size is allowed when its square-minus-nonsquare count has
square at most `K` times its population. Summing gives the signed energy hypothesis. -/
theorem energy_le_of_coset_imbalance (A H : Finset F) (hH : IsMulSubgroup H)
    (hA : (0 : F) ∉ A) (K : ℕ)
    (hs : ∀ x : F, signedOccupancy A H x^2 ≤ (K : ℤ) * (A ∩ coset H x).card) :
    ∑ x : F, signedOccupancy A H x^2 ≤ (K : ℤ) * H.card * A.card := by
  calc
    _ ≤ ∑ x : F, (K : ℤ) * (A ∩ coset H x).card := Finset.sum_le_sum (fun x _ => hs x)
    _ = _ := by rw [← Finset.mul_sum, sum_occupancies A H hH hA, mul_assoc]

/-- Quarter-scale power saving from signed energy, allowing arbitrary pointwise loads. -/
theorem quarter_of_signed_energy (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (K : ℕ)
    (henergy : ∑ x : F, signedOccupancy A H x^2 ≤ (K : ℤ)*H.card*A.card)
    (ε : ℝ) (hε : 0 < ε)
    (ha : (Fintype.card F : ℝ)^(1/4+ε) ≤ A.card)
    (hh : (Fintype.card F : ℝ)^(1/4+ε) ≤ H.card)
    (hc : 4 * (fourthConstant (Fintype.card F) : ℝ) * K ≤ (Fintype.card F : ℝ)^ε) :
    |((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ)^(-(ε/4)) * ((A.card : ℝ) * H.card) :=
  quarter_power_saving_of_fourth_estimates A H K
    (fourth_of_signed_energy hF A H hH hA K henergy) ε hε ha hh hc

/-- The ℓ^(4/3) criterion tolerates exceptional heavily occupied cosets with no
assumption on their signs. Its constant in the fourth moment is `M^3`. -/
theorem quarter_of_holder_mass (hF : ringChar F ≠ 2) (A H : Finset F)
    (hH : IsMulSubgroup H) (hA : (0 : F) ∉ A) (M : ℕ)
    (hmass : (∑ x : F, |(signedOccupancy A H x : ℝ)| ^ (4/3 : ℝ)) ≤
      (M : ℝ) * H.card * A.card)
    (ε : ℝ) (hε : 0 < ε)
    (ha : (Fintype.card F : ℝ)^(1/4+ε) ≤ A.card)
    (hh : (Fintype.card F : ℝ)^(1/4+ε) ≤ H.card)
    (hc : 4 * (fourthConstant (Fintype.card F) : ℝ) * (M:ℝ)^3 ≤ (Fintype.card F : ℝ)^ε) :
    |((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b) : ℤ) : ℝ)| ≤
      (Fintype.card F : ℝ)^(-(ε/4)) * ((A.card : ℝ) * H.card) := by
  apply quarter_power_saving_of_fourth_estimates A H (M^3) _ ε hε ha hh (by exact_mod_cast hc)
  intro r hr hrH hsmall
  have h := fourth_signed_holder hF A H hH hA r hr hrH hsmall
  have h' : ((∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b) : ℤ) : ℝ)^4 * (r:ℝ)^2 ≤
      ((A.card : ℝ)*H.card)^3 * (M:ℝ)^3 * fourthConstant (Fintype.card F) *
        Fintype.card F := calc
    _ ≤ _ := h
    _ ≤ ((M:ℝ)*H.card*A.card)^3 * fourthConstant (Fintype.card F) * Fintype.card F := by
      gcongr
    _ = _ := by ring
  exact_mod_cast h'

/-- Equal numbers of square and nonsquare sites on each occupied coset give
exactly zero discrepancy against the subgroup. -/
theorem sum_eq_zero_of_balanced_cosets (A H : Finset F) (hH : IsMulSubgroup H)
    (hA : (0 : F) ∉ A) (hs : ∀ x : F, signedOccupancy A H x = 0) :
    (∑ a ∈ A, ∑ b ∈ H, quadraticChar F (a-b)) = 0 := by
  have h := signed_recovery A H {1} hH (Finset.singleton_subset_iff.mpr hH.one_mem) hA
  simpa [hs] using h

end ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy.fourth_signed_energy

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy.fourth_of_signed_energy

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy.fourth_signed_holder

#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy.quarter_of_signed_energy
#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy.quarter_of_holder_mass
#print axioms ArkLib.ProximityGap.Frontier.PaleySubgroupSignedEnergy.sum_eq_zero_of_balanced_cosets
