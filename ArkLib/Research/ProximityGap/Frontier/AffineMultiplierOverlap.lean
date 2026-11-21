/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicSupplyBound
import ArkLib.Data.CodingTheory.ProximityGap.SidonEnergyIff
import ArkLib.Data.CodingTheory.ProximityGap.SidonGVClosure
import ArkLib.Research.ProximityGap.Frontier._R18PlateauLaw

/-! # Nonzero shifts cannot create a dense approximate multiplicative stabilizer. -/

namespace ArkLib.ProximityGap.Frontier.AffineMultiplierOverlap

open Finset R18PlateauLaw AdditiveEnergyRepBound AdditiveEnergySidonModNeg
variable {F : Type*} [Field F] [DecidableEq F]

/-- The points of the domain that remain in the domain after an affine change. -/
def overlap (H : Finset F) (a t : F) : Finset F := H.filter (fun x ↦ a*x+t ∈ H)

/-- Count the ordered unequal pairs by the ratio of their two affine images.
A nonidentity ratio forces a nonzero additive representation inside the original group. -/
theorem overlap_pairs {H : Finset F} (hH : IsMulSubgroup H) (hneg : ∀ x ∈ H, -x ∈ H)
    (a t : F) (ha : a ≠ 0) :
    (overlap H a t).card * ((overlap H a t).card - 1) ≤
      ∑ z ∈ H.erase 1, repCount H ((z-1)*t/a) := by
  classical
  let S := overlap H a t
  let f (q : F × F) := (a*q.1+t)/(a*q.2+t)
  have hm {x : F} (hx : x ∈ S) : x ∈ H ∧ a*x+t ∈ H := by
    exact mem_filter.mp hx
  have hne {u : F} (hu : u ∈ H) : u ≠ 0 := fun h ↦ hH.zero_notMem (h ▸ hu)
  have hf : (S.offDiag : Set (F×F)).MapsTo f (H.erase 1) := by
    intro q hq
    obtain ⟨hx, hy, hxy⟩ := mem_offDiag.mp hq
    have hy₀ := hne (hm hy).2
    apply mem_erase.mpr
    constructor
    · intro he
      have hxy' := (div_eq_iff hy₀).mp he
      apply hxy
      apply mul_left_cancel₀ ha
      simpa using add_right_cancel (show a*q.1+t=a*q.2+t by simpa using hxy')
    · simpa only [f, div_eq_mul_inv] using hH.mul_mem _ (hm hx).2 _ (hH.inv_mem _ (hm hy).2)
  have hcard (z : F) (hz : z ∈ H.erase 1) :
      (S.offDiag.filter (fun q ↦ f q = z)).card ≤ repCount H ((z-1)*t/a) := by
    obtain ⟨hz1, hzH⟩ := mem_erase.mp hz
    have hz₀ := hne hzH
    have he {q : F×F} (hq : q ∈ S.offDiag.filter (fun q ↦ f q = z)) :
        q.1 ∈ H ∧ q.2 ∈ H ∧ a*q.1+t=z*(a*q.2+t) := by
      obtain ⟨hh, heq⟩ := mem_filter.mp hq
      obtain ⟨hi, hj, _⟩ := mem_offDiag.mp hh
      exact ⟨(hm hi).1, (hm hj).1, (div_eq_iff (hne (hm hj).2)).mp heq⟩
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro q hq
      obtain ⟨hx, hy, heq⟩ := he hq
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      have hid : (z-1)*t/a - q.1 = -(z*q.2) := by
        field_simp
        linear_combination -heq
      rw [hid]
      exact hneg _ (hH.mul_mem _ hzH _ hy)
    · intro q hq r hr hfst
      apply Prod.ext hfst
      have hq' := (he hq).2.2
      rw [hfst] at hq'
      have heq := mul_left_cancel₀ hz₀ (hq'.symm.trans (he hr).2.2)
      exact mul_left_cancel₀ ha (add_right_cancel heq)
  calc
    _ = S.offDiag.card := by rw [offDiag_card, Nat.mul_sub_one]
    _ = ∑ z ∈ H.erase 1, (S.offDiag.filter fun q ↦ f q = z).card :=
      Finset.card_eq_sum_card_fiberwise hf
    _ ≤ _ := Finset.sum_le_sum hcard

/-- The sharp fourth additive energy translates into a square-root upper bound
on overlap with every nonsingular affine transformation having nonzero translation. -/
theorem from_fourth_floor {H : Finset F} (hH : IsMulSubgroup H) (hneg : ∀ x ∈ H, -x ∈ H)
    (h₂ : (2 : F) ≠ 0) (hE : additiveEnergy H = 3 * H.card^2 - 3*H.card)
    (a t : F) (ha : a ≠ 0) (ht : t ≠ 0) :
    (overlap H a t).card * ((overlap H a t).card - 1) ≤ 2 * (H.card - 1) := by
  have hs := sidonModNeg_of_additiveEnergy_eq_energyIff h₂ hH.zero_notMem hneg hE
  apply (overlap_pairs hH hneg a t ha).trans
  calc
    _ ≤ ∑ _z ∈ H.erase 1, 2 := by
      apply Finset.sum_le_sum
      intro z hz
      apply repCount_le_two_of_sidonModNeg hs
      exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr (mem_erase.mp hz).1) ht) ha
    _ = _ := by simp [card_erase_of_mem hH.one_mem, Nat.mul_comm]

/-- The production-length ceiling applies to all nonzero slopes and nonzero shifts. -/
theorem production {H : Finset F} (hH : IsMulSubgroup H) (hneg : ∀ x ∈ H, -x ∈ H)
    (h₂ : (2 : F) ≠ 0) (hcard : H.card = 2^30)
    (hE : additiveEnergy H = 3 * H.card^2 - 3*H.card)
    (a t : F) (ha : a ≠ 0) (ht : t ≠ 0) :
    (overlap H a t).card ≤ 46341 := by
  have hh := from_fourth_floor hH hneg h₂ hE a t ha ht
  rw [hcard] at hh
  by_contra! h
  have hu := Nat.mul_le_mul (show 46342 ≤ (overlap H a t).card by omega)
    (show 46341 ≤ (overlap H a t).card - 1 by omega)
  omega

/-- A transverse set of shifts consumes a weighted mixed difference count. -/
theorem transversal_weighted_pairs {H : Finset F} (hH : IsMulSubgroup H)
    (hneg : ∀ x ∈ H, -x ∈ H) (a : F) (T : Finset F)
    (htrans : Set.InjOn (fun q : F×F ↦ q.1*q.2) (↑(T ×ˢ H) : Set (F×F))) :
    H.card * (∑ t ∈ T, (overlap H a t).card * ((overlap H a t).card - 1)) ≤
      ∑ q ∈ H.offDiag, repCount H (a*(q.1-q.2)) := by
  classical
  let A := (T ×ˢ H).sigma fun q ↦ (overlap H a q.1).offDiag
  let R (q : F×F) := H.filter fun y ↦ a*(q.1-q.2)-y ∈ H
  let B := H.offDiag.sigma R
  let f (w : Σ _ : F×F, F×F) : Σ _ : F×F, F :=
    ⟨(w.1.2*w.2.1, w.1.2*w.2.2), w.1.2*(a*w.2.1+w.1.1)⟩
  have hne {u : F} (hu : u ∈ H) : u ≠ 0 := fun h ↦ hH.zero_notMem (h ▸ hu)
  have hmap : Set.MapsTo f (↑A) (↑B) := by
    rintro ⟨⟨t,h⟩,x,y⟩ hw
    obtain ⟨hth, hxy⟩ := mem_sigma.mp hw
    obtain ⟨_, hh⟩ := mem_product.mp hth
    obtain ⟨hx, hy, hxy⟩ := mem_offDiag.mp hxy
    obtain ⟨hxH, hax⟩ := mem_filter.mp hx
    obtain ⟨hyH, hay⟩ := mem_filter.mp hy
    apply mem_sigma.mpr
    constructor
    · exact mem_offDiag.mpr ⟨hH.mul_mem _ hh _ hxH, hH.mul_mem _ hh _ hyH,
        fun he ↦ hxy (mul_left_cancel₀ (hne hh) he)⟩
    · apply mem_filter.mpr
      refine ⟨hH.mul_mem _ hh _ hax, ?_⟩
      change a*(h*x-h*y)-h*(a*x+t) ∈ H
      rw [show a*(h*x-h*y)-h*(a*x+t) = -(h*(a*y+t)) by ring]
      exact hneg _ (hH.mul_mem _ hh _ hay)
  have hfinj : Set.InjOn f (↑A) := by
    rintro ⟨⟨t,h⟩,x,y⟩ hw ⟨⟨u,k⟩,v,z⟩ hr he
    obtain ⟨hth, _⟩ := mem_sigma.mp hw
    obtain ⟨huk, _⟩ := mem_sigma.mp hr
    have hx : h*x = k*v := congrArg (fun w ↦ w.1.1) he
    have hy : h*y = k*z := congrArg (fun w ↦ w.1.2) he
    have hq : h * (a*x+t) = k * (a*v+u) := congrArg (fun w ↦ w.2) he
    have htk : (t,h) = (u,k) := htrans hth huk (by
      change t*h=u*k
      linear_combination hq - a*hx)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htk
    have hn := hne (mem_product.mp hth).2
    obtain rfl := mul_left_cancel₀ hn hx
    obtain rfl := mul_left_cancel₀ hn hy
    rfl
  have hcard := Finset.card_le_card_of_injOn f hmap hfinj
  have hleft : A.card = H.card * ∑ t ∈ T, (overlap H a t).card * ((overlap H a t).card-1) := by
    rw [show A = _ from rfl, card_sigma, sum_product, mul_sum]
    apply sum_congr rfl
    intro t _
    simp [offDiag_card, Nat.mul_sub_one]
  rw [hleft] at hcard
  simpa only [B, R, repCount, card_sigma] using hcard

/-- Joint ordered-pair budget for shifts in distinct multiplicative cosets.
Each scaled unequal pair determines the scale and the shift from its first affine image. -/
theorem transversal_pair_budget {H : Finset F} (hH : IsMulSubgroup H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hs : SidonModNeg H) (a : F) (ha : a ≠ 0) (T : Finset F)
    (htrans : Set.InjOn (fun q : F×F ↦ q.1*q.2) (↑(T ×ˢ H) : Set (F×F))) :
    ∑ t ∈ T, (overlap H a t).card * ((overlap H a t).card - 1) ≤ 2*(H.card-1) := by
  classical
  have hcard := transversal_weighted_pairs hH hneg a T htrans
  have hright : (∑ q ∈ H.offDiag, repCount H (a*(q.1-q.2))) ≤ H.card * (2*(H.card-1)) := by
    calc
      _ ≤ ∑ _q ∈ H.offDiag, 2 := by
        apply sum_le_sum
        intro q hq
        apply repCount_le_two_of_sidonModNeg hs
        exact mul_ne_zero ha (sub_ne_zero.mpr (mem_offDiag.mp hq).2.2)
      _ = _ := by simp [offDiag_card, ← Nat.mul_sub_one]; ring
  exact Nat.le_of_mul_le_mul_left (hcard.trans hright) (card_pos.mpr ⟨1,hH.one_mem⟩)

/-- Cauchy-Schwarz converts the joint ordered-pair budget to a total incidence count. -/
theorem transversal_incidence {H : Finset F} (hH : IsMulSubgroup H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hs : SidonModNeg H) (a : F) (ha : a ≠ 0) (T : Finset F)
    (htrans : Set.InjOn (fun q : F×F ↦ q.1*q.2) (↑(T ×ˢ H) : Set (F×F))) :
    (∑ t ∈ T, (overlap H a t).card)^2 ≤
      T.card * ((∑ t ∈ T, (overlap H a t).card) + 2*(H.card-1)) := by
  apply (sq_sum_le_card_mul_sum_sq (s := T) (f := fun t ↦ (overlap H a t).card)).trans
  apply Nat.mul_le_mul_left
  have hid (c : ℕ) : c^2 = c + c*(c-1) := by
    cases c <;> simp
    ring
  simpa only [hid, sum_add_distrib, add_le_add_iff_left] using
    (show (∑ t ∈ T, (overlap H a t).card) + ∑ t ∈ T, (overlap H a t).card*((overlap H a t).card-1)
        ≤ (∑ t ∈ T, (overlap H a t).card) + 2*(H.card-1)
      from Nat.add_le_add_left (transversal_pair_budget hH hneg hs a ha T htrans) _)

/-- Production-size transverse windows cover fewer than 4.47% of the subgroup. -/
theorem production_transversal {H : Finset F} (hH : IsMulSubgroup H)
    (hneg : ∀ x ∈ H, -x ∈ H) (h₂ : (2 : F) ≠ 0) (hcard : H.card = 2^30)
    (hE : additiveEnergy H = 3 * H.card^2 - 3*H.card)
    (a : F) (ha : a ≠ 0) (T : Finset F) (hB : T.card ≤ 2^20)
    (htrans : Set.InjOn (fun q : F×F ↦ q.1*q.2) (↑(T ×ˢ H) : Set (F×F))) :
    ∑ t ∈ T, (overlap H a t).card ≤ 47980317 := by
  let M := ∑ t ∈ T, (overlap H a t).card
  have hs := sidonModNeg_of_additiveEnergy_eq_energyIff h₂ hH.zero_notMem hneg hE
  have hh := (transversal_incidence hH hneg hs a ha T htrans).trans (Nat.mul_le_mul_right _ hB)
  change M^2 ≤ 2^20 * (M + 2*(H.card-1)) at hh
  rw [hcard] at hh
  change M ≤ _
  by_contra! h
  have hpos : 47980318 ≤ M := by omega
  have hl : 0 ≤ ((M : ℤ) - 47980318) := by
    apply sub_nonneg.mpr
    exact_mod_cast hpos
  norm_num at hh
  zify at hh
  nlinarith [sq_nonneg ((M : ℤ)-47980318)]

/-- Distinct power residues certify transversality. The conclusion permits an arbitrary
common nonzero scaling of the shift set. -/
theorem transversal_of_power_injective {H T : Finset F} (n : ℕ) (hpow : ∀ h ∈ H, h^n = 1)
    (hnonzero : ∀ t ∈ T, t ≠ 0) (hdistinct : Set.InjOn (fun t : F ↦ t^n) T)
    (v : F) (hv : v ≠ 0) :
    Set.InjOn (fun q : F×F ↦ q.1*q.2) (↑(T.image (v * ·) ×ˢ H) : Set (F×F)) := by
  rintro ⟨t,h⟩ hth ⟨u,k⟩ huk he
  obtain ⟨ht, hh⟩ := mem_product.mp hth
  obtain ⟨hu, hk⟩ := mem_product.mp huk
  obtain ⟨t, hto, rfl⟩ := mem_image.mp ht
  obtain ⟨u, huo, rfl⟩ := mem_image.mp hu
  change v*t*h=v*u*k at he
  rw [mul_assoc, mul_assoc] at he
  have heq := mul_left_cancel₀ hv he
  have hp := congrArg (fun z : F ↦ z^n) heq
  simp only [mul_pow, hpow h hh, hpow k hk, mul_one] at hp
  obtain rfl := hdistinct hto huo hp
  exact Prod.ext rfl (mul_left_cancel₀ (hnonzero _ hto) heq)

/-- A nonzero dilation permutes the difference profile. Its mixed fourth energy
is bounded by the additive energy, and its diagonal contributes exactly the square size. -/
theorem scaled_offDiag_energy [Fintype F] {H : Finset F} (hneg : ∀ x ∈ H, -x ∈ H)
    (a : F) (ha : a ≠ 0) :
    H.card^2 + ∑ q ∈ H.offDiag, repCount H (a*(q.1-q.2)) ≤ additiveEnergy H := by
  classical
  let R : F×F → ℕ := fun q ↦ repCount H (a*(q.1-q.2))
  have hdiag : ∑ q ∈ H.diag, R q = H.card^2 := by
    calc
      _ = ∑ _q ∈ H.diag, H.card := by
        apply sum_congr rfl
        intro q hq
        obtain ⟨_,he⟩ := mem_diag.mp hq
        simp [R, he, repCount_zero_eq_card hneg]
      _ = _ := by simp [sq]
  have hfull : ∑ q ∈ H ×ˢ H, R q = ∑ s : F, repCount H (a*s) * repCount H s := by
    rw [sum_product]
    calc
      _ = ∑ x ∈ H, ∑ y ∈ H, repCount H (a*(x+y)) := by
        apply sum_congr rfl
        intro x _
        apply sum_nbij' (fun y : F ↦ -y) (fun y : F ↦ -y) hneg hneg
          (fun y _ ↦ neg_neg _) (fun y _ ↦ neg_neg _) (fun y _ ↦ ?_)
        simp [R, sub_eq_add_neg]
      _ = ∑ x ∈ H, ∑ y ∈ H, ∑ s : F, repCount H (a*s) * (if x+y=s then 1 else 0) := by
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro y _
        simp [mul_ite]
      _ = ∑ s : F, ∑ x ∈ H, ∑ y ∈ H, repCount H (a*s) * (if x+y=s then 1 else 0) := by
        symm
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [sum_comm]
      _ = _ := by
        apply sum_congr rfl
        intro s _
        rw [repCount_eq_sum_pairs H s, mul_sum]
        apply sum_congr rfl
        intro x _
        rw [mul_sum]
  have hperm : (∑ s : F, repCount H (a*s)^2) = ∑ s : F, repCount H s^2 :=
    Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun s ↦ repCount H s^2)
  have ham (b c : ℕ) : 2*(b*c) ≤ b^2+c^2 := by
    zify
    nlinarith [sq_nonneg ((b : ℤ) - c)]
  have havg := sum_le_sum (s := (univ : Finset F))
    (fun s _ ↦ ham (repCount H (a*s)) (repCount H s))
  rw [← mul_sum, sum_add_distrib, hperm, ← additiveEnergy_eq_sum_repCount_sq] at havg
  change H.card^2 + ∑ q ∈ H.offDiag, R q ≤ _
  rw [← hdiag, ← sum_union H.disjoint_diag_offDiag, H.diag_union_offDiag, hfull]
  omega

/-- A fourth-energy upper bound on admissible affine pairs for arbitrary finite fields. -/
theorem transversal_energy [Fintype F] {H : Finset F} (hH : IsMulSubgroup H)
    (hneg : ∀ x ∈ H, -x ∈ H) (a : F) (ha : a ≠ 0) (T : Finset F)
    (htrans : Set.InjOn (fun q : F×F ↦ q.1*q.2) (↑(T ×ˢ H) : Set (F×F))) :
    H.card^2 + H.card * (∑ t ∈ T, (overlap H a t).card * ((overlap H a t).card - 1)) ≤
      additiveEnergy H :=
  (Nat.add_le_add_left (transversal_weighted_pairs hH hneg a T htrans) _).trans
    (scaled_offDiag_energy hneg a ha)

#print axioms transversal_energy
#print axioms transversal_of_power_injective
#print axioms transversal_pair_budget
#print axioms production_transversal
#print axioms overlap_pairs
#print axioms from_fourth_floor
#print axioms production

end ArkLib.ProximityGap.Frontier.AffineMultiplierOverlap
