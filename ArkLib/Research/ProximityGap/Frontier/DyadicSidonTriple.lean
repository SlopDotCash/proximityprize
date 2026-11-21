/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment
import ArkLib.Data.CodingTheory.ProximityGap.SidonEnergyIff
import ArkLib.Data.CodingTheory.ProximityGap.SidonGVClosure
import ArkLib.Research.ProximityGap.Frontier._R18PlateauLaw
import ArkLib.Research.ProximityGap.Frontier._G105ZeroTripleQuantizationFence

/-! # Vanishing of the signed third moment under the dyadic fourth-energy floor -/
namespace ArkLib.ProximityGap.Frontier.DyadicSidonTriple
open Finset R18PlateauLaw AdditiveEnergyRepBound AdditiveEnergySidonModNeg
variable {F : Type*} [Field F] [DecidableEq F]

/-- The order-three fractional linear transformation permutes the normalized additive
representations. Its fixed points require a cube root of unity or characteristic three. -/
theorem repCount_one_zero {H : Finset F} (hH : IsMulSubgroup H) (hneg : ∀ x ∈ H, -x ∈ H)
    {n : ℕ} (hpow : ∀ x ∈ H, x^n = 1) (hcop : n.Coprime 3)
    (h₃ : (3 : F) ≠ 0) (hcount : repCount H 1 ≤ 2) : repCount H 1 = 0 := by
  classical
  let R := H.filter fun x ↦ 1-x ∈ H
  let f (x : F) := (1-x)⁻¹
  have hne {y : F} (hy : y ∈ H) : y ≠ 0 := fun he ↦ hH.zero_notMem (he ▸ hy)
  have hmap {x : F} (hx : x ∈ R) : f x ∈ R := by
    obtain ⟨hxH,h1x⟩ := mem_filter.mp hx
    have hx1 := hne h1x
    have hid : 1-f x = -(x*(1-x)⁻¹) := by
      dsimp [f]
      field_simp
      ring
    exact mem_filter.mpr ⟨hH.inv_mem _ h1x, hid ▸ hneg _ (hH.mul_mem _ hxH _ (hH.inv_mem _ h1x))⟩
  have h3cycle {x : F} (hx : x ∈ R) : f (f (f x)) = x := by
    obtain ⟨hxH,h1x⟩ := mem_filter.mp hx
    have hx0 := hne hxH
    have hx1 := hne h1x
    dsimp [f]
    field_simp
    ring_nf
    simp [hx0]
  have hfree {x : F} (hx : x ∈ R) : f x ≠ x := by
    intro hf
    obtain ⟨hxH,h1x⟩ := mem_filter.mp hx
    have hx1 := hne h1x
    have he : (1-x)*x = 1 := calc
      _ = (1-x)*(1-x)⁻¹ := congrArg ((1-x)* ·) hf.symm
      _ = 1 := mul_inv_cancel₀ hx1
    have hc : (-x)^3 = 1 := by linear_combination (x+1)*he
    have hdiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hpow _ (hneg _ hxH)))
      (orderOf_dvd_of_pow_eq_one hc)
    rw [hcop.gcd_eq_one] at hdiv
    have hone := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdiv)
    apply h₃
    linear_combination -he + (x-2)*hone
  change R.card = 0
  by_contra h
  obtain ⟨x,hx⟩ := card_pos.mp (Nat.pos_of_ne_zero h)
  have hfx := hmap hx
  have hffx := hmap hfx
  have hA : x ≠ f x := (hfree hx).symm
  have hB : x ≠ f (f x) := by
    intro hh
    apply hA
    simpa only [h3cycle hx] using (congrArg f hh).symm
  have hC : f x ≠ f (f x) := (hfree hfx).symm
  have hsub : ({x,f x,f (f x)} : Finset F) ⊆ R := by
    intro y hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have h3 := card_le_card hsub
  rw [card_triple_eq_three_iff.mpr ⟨hA,hB,hC⟩] at h3
  change R.card ≤ 2 at hcount
  omega

/-- The fourth-energy computation discharges the zero-triple hypothesis for dyadic root sets. -/
theorem zeroTriple_of_fourth_floor {H : Finset F} (hH : IsMulSubgroup H)
    (hneg : ∀ x ∈ H, -x ∈ H) (k : ℕ) (hHpow : ∀ x, x ∈ H ↔ x^(2^k) = 1)
    (h₂ : (2 : F) ≠ 0) (h₃ : (3 : F) ≠ 0)
    (hE : additiveEnergy H = 3*H.card^2 - 3*H.card) :
    G104DepthSixStratifiedConsumer.zeroTripleCount H = 0 := by
  have hs := sidonModNeg_of_additiveEnergy_eq_energyIff h₂ hH.zero_notMem hneg hE
  have hc := repCount_one_zero hH hneg (fun x hx ↦ (hHpow x).mp hx)
    ((by decide : Nat.Coprime 2 3).pow_left k) h₃ (repCount_le_two_of_sidonModNeg hs one_ne_zero)
  rw [G105ZeroTripleQuantizationFence.zeroTripleCount_eq_card_mul_repCount_one
    (n := 2^k) (Nat.one_le_pow _ _ (by decide)) hHpow hneg, hc, Nat.mul_zero]

open SubgroupGaussSumRawMoment SubgroupGaussSumSecondMoment

/-- The signed third moment over nonzero frequencies is the negative cube of the subgroup
size. All nonzero-frequency periods are counted with their field multiplicities. -/
theorem signed_third_moment [Fintype F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (H : Finset F)
    (hzero : G104DepthSixStratifiedConsumer.zeroTripleCount H = 0) :
    ∑ b ∈ (univ : Finset F).erase 0, eta ψ H b ^ 3 = -(H.card : ℂ)^3 := by
  classical
  have hN : N0 H 3 = 0 := by
    unfold N0
    apply sum_eq_zero
    intro v hv
    apply ite_eq_right_iff.mpr
    intro he
    exfalso
    rw [Fin.sum_univ_three] at he
    have hm := Fintype.mem_piFinset.mp hv
    have ht : (v 0,v 1,v 2) ∈ ((H ×ˢ H ×ˢ H).filter fun t ↦ t.1+t.2.1+t.2.2=0) :=
      mem_filter.mpr ⟨mem_product.mpr ⟨hm 0, mem_product.mpr ⟨hm 1,hm 2⟩⟩,he⟩
    exact (Nat.ne_of_gt (card_pos.mpr ⟨_,ht⟩)) hzero
  have htot := subgroup_gaussSum_rawMoment hψ H 3
  rw [hN, Nat.cast_zero, mul_zero] at htot
  have hz : eta ψ H 0 = (H.card : ℂ) := by simp [eta]
  have hu := sum_erase_add (univ : Finset F) (fun b ↦ eta ψ H b ^ 3) (mem_univ 0)
  rw [htot, hz] at hu
  linear_combination hu

#print axioms signed_third_moment
#print axioms repCount_one_zero
#print axioms zeroTriple_of_fourth_floor
end ArkLib.ProximityGap.Frontier.DyadicSidonTriple
