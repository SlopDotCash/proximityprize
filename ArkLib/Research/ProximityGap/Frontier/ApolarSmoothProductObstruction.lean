/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic.LinearCombination
import ArkLib.Research.ProximityGap.Frontier.MobiusStepanov

/-! # Changing the two coordinates in a smooth error-product test -/

set_option autoImplicit false
namespace ProximityGap.ApolarSmoothProductObstruction
open Finset Polynomial
open MobiusStepanov

variable {F : Type*} [Field F] [DecidableEq F]

/-- Count the intersection with any power fiber of positive exponent at most twice the
production domain size. The zero and the pole are two finite distinguished points. -/
theorem power_fiber_card {p m : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^37 < p)
    (hm : 0 < m) (hmu : m ≤ 2^31) {a b K : F} (ha : a ≠ 0) (hab : a ≠ b) (S : Finset F)
    (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a ∧ x ≠ b)
    (hpow : ∀ x ∈ S, x ^ (2^30 : ℕ) = 1)
    (hratio : ∀ x ∈ S, (x-a)^m = K * (x-b)^m) : S.card ≤ 99090433 := by
  by_cases hml : 4096*64 ≤ m
  swap
  · let phi := fun x : F => (x-a)/(x-b)
    have hi : Set.InjOn phi S := by
      intro x hx y hy heq
      have hv := (div_eq_div_iff (sub_ne_zero.mpr (hreg x hx).2.2)
        (sub_ne_zero.mpr (hreg y hy).2.2)).mp heq
      have hw : (a-b)*(x-y) = 0 := by linear_combination hv
      exact sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hab))
    have hs : S.image phi ⊆ (nthRoots m K).toFinset := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      apply Multiset.mem_toFinset.mpr
      apply (mem_nthRoots hm).mpr
      dsimp [phi]
      rw [div_pow, hratio x hx, mul_div_cancel_right₀ _ (pow_ne_zero _ (sub_ne_zero.mpr (hreg x hx).2.2))]
    have hh := (card_le_card hs).trans ((Multiset.toFinset_card_le _).trans (card_nthRoots m K))
    rw [card_image_of_injOn hi] at hh
    omega
  have h := production_exponent_count hp hbig hml ha hab S hreg hpow hratio
  omega

/-- No single power fiber covers all equal-size products of these finite-root ratios
when the smooth domain has more than the intersection bound many eligible sites. -/
theorem no_constant_products {p m j : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^37 < p)
    (hm : 0 < m) (hmu : m ≤ 2^31) {a b : F} (ha : a ≠ 0) (hab : a ≠ b) (S : Finset F)
    (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a ∧ x ≠ b) (hpow : ∀ x ∈ S, x ^ (2^30 : ℕ) = 1)
    (hsize : 99090433 < S.card) (hj : j+1 < S.card) :
    ¬∃ c : F, ∀ E ⊆ S, E.card = j+1 → (∏ x ∈ E, (x-a)/(x-b))^m = c := by
  rintro ⟨c,hc⟩
  let φ := fun x : F => (x-a)/(x-b)
  obtain ⟨z,hz⟩ := card_pos.mp (by omega : 0 < S.card)
  have hcst (x : F) (hx : x ∈ S) : (φ x)^m = (φ z)^m := by
    by_cases hzn : z = x
    · rw [hzn]
    have hze : z ∈ S.erase x := mem_erase.mpr ⟨hzn,hz⟩
    have hj' : j ≤ ((S.erase x).erase z).card := by
      rw [card_erase_of_mem hze,card_erase_of_mem hx]
      omega
    obtain ⟨D,hD,hjD⟩ := exists_subset_card_eq hj'
    have hDS : D ⊆ S := hD.trans (erase_subset _ _ |>.trans (erase_subset _ _))
    have hxD : x ∉ D := fun h => notMem_erase _ _ (mem_of_mem_erase (hD h))
    have hzD : z ∉ D := fun h => notMem_erase _ _ (hD h)
    have hprod (y : F) (hy : y ∈ S) (hnot : y ∉ D) :
        (φ y)^m * (∏ v ∈ D, φ v)^m = c := by
      have h := hc (insert y D) (insert_subset hy hDS) (by simp [hnot,hjD])
      simpa only [prod_insert hnot,mul_pow,φ] using h
    have hn : (∏ v ∈ D, φ v) ≠ 0 := prod_ne_zero_iff.mpr fun y hy =>
      div_ne_zero (sub_ne_zero.mpr (hreg y (hDS hy)).2.1) (sub_ne_zero.mpr (hreg y (hDS hy)).2.2)
    exact mul_right_cancel₀ (pow_ne_zero m hn) ((hprod x hx hxD).trans (hprod z hz hzD).symm)
  apply (not_le_of_gt hsize)
  apply power_fiber_card hp hbig hm hmu ha hab S hreg hpow (K := (φ z)^m)
  intro x hx
  have h := hcst x hx
  change ((x-a)/(x-b))^m = _ at h
  rw [div_pow] at h
  exact (div_eq_iff (pow_ne_zero _ (sub_ne_zero.mpr (hreg x hx).2.2))).mp h

#print axioms power_fiber_card
#print axioms no_constant_products
end ProximityGap.ApolarSmoothProductObstruction
