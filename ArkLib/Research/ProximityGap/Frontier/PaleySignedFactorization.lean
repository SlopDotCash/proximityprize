/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyVirtualSign
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftFactorization

/-!
# Recovering signed Paley discrepancy as a difference of polynomial root orders

Adding a virtual sign selects one of two normalized derivative determinants.
Their orders determine the signed character sum at each specified field shift.
-/

namespace ProximityGap.PaleySignedFactorization

open Finset Polynomial PaleyInterpolationContact PaleyShiftMultiplicityBudget
open PaleyShiftFactorization PaleyHankelDegree PaleyDefectMinor
open scoped Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The determinant with real sign label supplied through its constant term. -/
noncomputable def signed (A : Finset (ZMod p)) (σ : ℤ) : (ZMod p)[X] :=
  let D := p/2+(A.card-1)
  (normalizedHankel (powerSum A A D - C (σ : ZMod p)) D ((A.card+1)/2-1)).det

private theorem degree_signed (hp : p ≠ 2) (A : Finset (ZMod p)) (σ : ℤ)
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) :
    signed A σ ≠ 0 ∧ (signed A σ).natDegree = (A.card+1)/2*(p/2+1-(A.card+1)/2) := by
  let D := p/2+(A.card-1)
  let h := (A.card+1)/2-1
  let F := powerSum A A D - C (σ : ZMod p)
  obtain ⟨v,hv⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hd : D < p := by dsimp [D]; omega
  have ht : F.natDegree = p/2 := by
    dsimp [F]
    rw [natDegree_sub_C, (powerSum_degree A ha (D := D) (by dsimp [D]; omega) hd).1]
    dsimp [D]; omega
  have hprime := (Fact.out : p.Prime).two_le
  have hF : F ≠ 0 := by intro he; rw [he,natDegree_zero] at ht; omega
  have hl : 2*h ≤ F.natDegree := by rw [ht]; dsimp [h]; omega
  have hupper : F.natDegree ≤ D := by rw [ht]; dsimp [D]; omega
  have hgap : h ≤ D-F.natDegree := by rw [ht]; dsimp [h,D]; omega
  refine ⟨normalizedHankel_det_ne_zero F hF D h hl hupper hgap hd, ?_⟩
  change (normalizedHankel F D h).det.natDegree = _
  rw [normalizedHankel_det_degree F hF D h hl hupper hgap hd, ht]
  dsimp [h]; congr 1 <;> omega

private theorem signed_dvd (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) (b : ZMod p) (σ : ℤ)
    (hs : σ=1 ∨ σ=-1) :
    (X-C b)^(((shiftSum A b+σ)^2/4).toNat) ∣ signed A σ := by
  classical
  let W := shiftSum A b
  let τ : ℤ := if 0 ≤ W+σ then 1 else -1
  have ht : τ=1 ∨ τ=-1 := by unfold τ; split <;> simp
  have hnt : -τ=1 ∨ -τ=-1 := by rcases ht with h|h <;> simp [h]
  let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -τ
  let z : ℕ := if -b ∈ A then 1 else 0
  let extra : ℕ := if τ=σ then 0 else 1
  let w := τ*(W+σ)
  have hw0 : 0 ≤ w := by dsimp [w,τ]; split <;> simp_all; omega
  have hsq : w^2 = (W+σ)^2 := by dsimp [w]; rcases ht with h|h <;> rw [h] <;> ring
  have hsign : τ*σ = 1-2*(extra : ℤ) := by
    dsimp only [extra]
    rcases ht with h|h <;> rcases hs with g|g <;> simp [h,g]
  have he := PaleyShiftListRecovery.agreement_excess A b hnt
  have hrow : τ*W = (A.card : ℤ)-z-2*E.card := by
    change -τ*W = _ at he
    simp only [PaleyShiftListRecovery.agreements, add_comm] at he
    dsimp only [E,z]
    split_ifs at he ⊢ <;> push_cast <;> linarith
  have hw : w = ((A.card+1 : ℕ) : ℤ)-z-2*(E.card+extra : ℕ) := by
    dsimp [w]; rw [mul_add, hsign, hrow]; ring
  have hz : z ≤ 1 := by dsimp [z]; split <;> decide
  have hquota := quota_of_minority (a := A.card+1) (by omega) hz hw hw0
  let h := (A.card+1)/2-1
  let ν := if -b ∈ A then A.card-1 else A.card-1+1
  have hnu : (A.card+1)-1-z=ν := by dsimp [z,ν]; split <;> omega
  have hh : 2*h ≤ ν := by dsimp [h,ν]; split <;> omega
  obtain ⟨v,hv⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hd : p/2+(A.card-1) < p := by omega
  change (X-C b)^(((W+σ)^2/4).toNat) ∣ _
  rw [hsq,hnu] at hquota
  rw [hquota]
  by_cases hmatch : τ=σ
  · have H := minority_determinant hp A b (k := A.card-1) (h := h) (by omega) hd hh ht
    simpa [signed, h, ν, E, extra, hmatch] using H
  · have H := minority_determinant_add_const hp A b (k := A.card-1) (h := h)
      (by omega) hd hh ht ((τ : ZMod p)-(σ : ZMod p))
    have heq (F : (ZMod p)[X]) : F-C (τ : ZMod p)+C ((τ : ZMod p)-(σ : ZMod p)) = F-C (σ : ZMod p) := by
      rw [map_sub]; ring
    simpa [signed, h, ν, E, extra, hmatch, heq] using H

/-- Complete factorization with the character sum shifted by the chosen sign. -/
theorem signed_factorization (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) {σ : ℤ} (hs : σ=1 ∨ σ=-1) :
    signed A σ = C (signed A σ).leadingCoeff *
      ∏ b : ZMod p, (X-C b)^(((shiftSum A b+σ)^2/4).toNat) := by
  apply eq_leadingCoeff_mul_prod_of_local_dvd
  · rw [sum_signed_multiplicity hp A σ hs, (degree_signed hp A σ ha ha').2]
  · exact fun b _ => signed_dvd hp A ha ha' b σ hs

/-- The order at a single shift has no residual factor. -/
theorem signed_order (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) {σ : ℤ} (hs : σ=1 ∨ σ=-1) (b : ZMod p) :
    (signed A σ).rootMultiplicity b = ((shiftSum A b+σ)^2/4).toNat := by
  have hd := degree_signed hp A σ ha ha'
  have hle (c : ZMod p) : ((shiftSum A c+σ)^2/4).toNat ≤ (signed A σ).rootMultiplicity c :=
    (le_rootMultiplicity_iff hd.1).mpr (signed_dvd hp A ha ha' c σ hs)
  apply le_antisymm _ (hle b)
  by_contra! hbad
  have hstrict := Finset.sum_lt_sum (s := (univ : Finset (ZMod p))) (fun c _ => hle c)
    ⟨b,mem_univ b,hbad⟩
  have hcap := Polynomial.sum_rootMultiplicity_le_natDegree (W := signed A σ) univ
  rw [sum_signed_multiplicity hp A σ hs] at hstrict
  omega

/-- The signed discrepancy equals a difference of root orders at the prescribed shift. -/
theorem shiftSum_eq_order_sub_order (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) (b : ZMod p) :
    shiftSum A b = ((signed A 1).rootMultiplicity b : ℤ) - (signed A (-1)).rootMultiplicity b := by
  rw [signed_order hp A ha ha' (Or.inl rfl),signed_order hp A ha ha' (Or.inr rfl)]
  let w := shiftSum A b
  have H : ∀ t : ℤ, 0 ≤ t^2 / 4 := fun t => Int.ediv_nonneg (sq_nonneg _) (by decide)
  simp only [Int.toNat_of_nonneg (H _)]
  change w = (w+1)^2 / 4 - (w + -1)^2/4
  rw [show (w+1)^2 = (w + -1)^2+4*w by ring]
  omega

/-- Prescribed rectangle discrepancy from the total root orders over the second set. -/
theorem rectangle_eq_orders (hp : p ≠ 2) (A B : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) :
    ∑ b ∈ B, ∑ u ∈ A, quadraticChar (ZMod p) (u+b) =
      (∑ b ∈ B, ((signed A 1).rootMultiplicity b : ℤ)) -
      ∑ b ∈ B, ((signed A (-1)).rootMultiplicity b : ℤ) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => shiftSum_eq_order_sub_order hp A ha ha' b

end ProximityGap.PaleySignedFactorization

#print axioms ProximityGap.PaleySignedFactorization.signed_factorization
#print axioms ProximityGap.PaleySignedFactorization.shiftSum_eq_order_sub_order

#print axioms ProximityGap.PaleySignedFactorization.rectangle_eq_orders
