/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftFactorization
import Mathlib.Data.Finset.Powerset

/-! # Pair factors of the central Paley determinant

Every central interpolation determinant is recovered from determinants on two
coordinates. At each shift one subtracts from the count of equally signed
pairs a correction depending only on the number of nonzero symbols.
-/
namespace ProximityGap.PaleyPairDeterminants
open Finset Polynomial PaleyShiftFactorization PaleyShiftMultiplicityBudget
variable {p : ℕ} [Fact p.Prime]

/-- The number of same-sign pairs in a maximally balanced string of length `s`. -/
def baseline (s : ℕ) : ℕ := (s/2)*((s-1)/2)

private theorem twice_choose (n : ℕ) : 2*(n.choose 2 : ℤ)=(n:ℤ)^2-n := by
  cases n with
  | zero => norm_num
  | succ n =>
    have hh := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (n+1))
    rw [← Nat.choose_two_right] at hh
    simp only [Nat.add_one_sub_one] at hh
    have hg : (((n+1).choose 2 : ℕ):ℤ)*2=((n:ℤ)+1)*n := by exact_mod_cast hh
    push_cast
    nlinarith only [hg]

private theorem pair_arithmetic (a b : ℕ) :
    a.choose 2+b.choose 2 = (((a:ℤ)-b)^2/4).toNat+baseline (a+b) := by
  have hc := twice_choose a
  have hd := twice_choose b
  let s := a+b
  let h := s/2
  let w := (a:ℤ)-b
  have ht : 0≤w^2/4 := Int.ediv_nonneg (sq_nonneg _) (by decide)
  change a.choose 2+b.choose 2 = (w^2/4).toNat+baseline s
  apply Int.ofNat_inj.mp
  push_cast
  rw [Int.toNat_of_nonneg ht]
  rcases Nat.mod_two_eq_zero_or_one s with he|ho
  · have hs : s=2*h := by dsimp [h]; omega
    have hw : w=2*((a:ℤ)-h) := by dsimp [w,h,s] at *; omega
    have heq : w^2=4*((a:ℤ)-h)^2 := by rw [hw]; ring
    rw [heq, Int.mul_ediv_cancel_left _ (by decide : (4:ℤ)≠0)]
    by_cases hz : h=0
    · have ha : a=0 := by dsimp [s] at hs; omega
      have hb : b=0 := by dsimp [s] at hs; omega
      subst a; subst b; norm_num [baseline,s,h]
    · have hb : baseline s=h*(h-1) := by unfold baseline; congr 1; dsimp [h]; omega
      rw [hb, Nat.cast_mul, Nat.cast_sub (by omega : 1≤h)]
      dsimp [s] at hs
      have hs' : (a:ℤ)+b=2*h := by exact_mod_cast hs
      push_cast
      nlinarith only [hc,hd,hs',congrArg (fun v : ℤ => v^2) hs',congrArg (fun v : ℤ => v*(a:ℤ)) hs']
  · have hs : s=2*h+1 := by dsimp [h]; omega
    have hw : w=2*((a:ℤ)-h)-1 := by dsimp [w,h,s] at *; omega
    have heq : w^2=4*(((a:ℤ)-h)^2-((a:ℤ)-h))+1 := by rw [hw]; ring
    have hediv : w^2/4=((a:ℤ)-h)^2-((a:ℤ)-h) := by rw [heq]; omega
    have hb : baseline s=h*h := by unfold baseline; congr 1; dsimp [h]; omega
    rw [hediv,hb,Nat.cast_mul]
    dsimp [s] at hs
    have hs' : (a:ℤ)+b=2*h+1 := by exact_mod_cast hs
    nlinarith only [hc,hd,hs',congrArg (fun v : ℤ => v^2) hs',congrArg (fun v : ℤ => v*(a:ℤ)) hs']

/-- The monic normalization removes the scalar chosen by the interpolation weights. -/
noncomputable def monicCentral (A : Finset (ZMod p)) : (ZMod p)[X] :=
  C (central A).leadingCoeff⁻¹ * central A

/-- The two-coordinate determinant is the ordinary divided difference of the two Euler powers. -/
theorem central_pair (u v : ZMod p) (huv : u≠v) :
    central {u,v} = C (u-v)⁻¹ * ((X+C u)^(p/2) - (X+C v)^(p/2)) := by
  classical
  have hc : ({u,v} : Finset (ZMod p)).card=2 := by simp [huv]
  unfold central
  rw [hc]
  change (PaleyDefectMinor.normalizedHankel (PaleyInterpolationContact.powerSum {u,v} {u,v} (p/2)) (p/2) 0).det = _
  rw [Matrix.det_fin_one]
  change C ((Nat.descFactorial (p/2) 0 : ZMod p)⁻¹) * PaleyInterpolationContact.powerSum {u,v} {u,v} (p/2) = _
  have hother : (v-u)⁻¹ = -(u-v)⁻¹ := by rw [neg_inv,neg_sub]
  have herb : ({u,v} : Finset (ZMod p)).erase v={u} := by
    rw [Finset.pair_comm,Finset.erase_insert (by simpa using huv.symm)]
  simp only [Nat.descFactorial_zero,Nat.cast_one,inv_one,C_1,one_mul,PaleyInterpolationContact.powerSum,
    sum_insert (show u∉({v}:Finset (ZMod p)) by simpa using huv),sum_singleton,Lagrange.nodalWeight,
    erase_insert (show u∉({v}:Finset (ZMod p)) by simpa using huv),herb,prod_singleton,id_eq,hother,map_neg]
  ring

private theorem monic_factors (hp : p≠2) (A : Finset (ZMod p)) (ha : 2≤A.card)
    (hu : A.card≤p/2+1) :
    monicCentral A=∏ b : ZMod p, (X-C b)^(multiplicity A b) := by
  unfold monicCentral
  conv_lhs => rhs; rw [central_factorization hp A ha hu]
  rw [← mul_assoc,← C_mul,inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr (central_degree hp A ha hu).1),
    C_1,one_mul]

private theorem pair_profile (A S : Finset (ZMod p)) (hS : S∈A.powersetCard 2) (b : ZMod p) :
    multiplicity S b = (if S⊆A.filter (fun x => quadraticChar (ZMod p) (x+b)=1) then 1 else 0) +
      (if S⊆A.filter (fun x => quadraticChar (ZMod p) (x+b)= -1) then 1 else 0) := by
  classical
  obtain ⟨hsub,hs⟩ := mem_powersetCard.mp hS
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hs
  have hx := hsub (mem_insert_self x {y})
  have hy := hsub (mem_insert_of_mem (mem_singleton_self y))
  have cases' (z : ZMod p) : quadraticChar (ZMod p) z=0 ∨ quadraticChar (ZMod p) z=1 ∨
      quadraticChar (ZMod p) z= -1 := by
    by_cases h : z=0
    · simp [h]
    · exact Or.inr (quadraticChar_dichotomy h)
  have hmem : x ∉ ({y} : Finset (ZMod p)) := by simpa using hxy
  rcases cases' (x+b) with ha|ha|ha <;> rcases cases' (y+b) with hb|hb|hb <;>
    simp only [PaleyShiftMultiplicityBudget.multiplicity,shiftSum,sum_insert hmem,sum_singleton,insert_subset_iff,singleton_subset_iff,mem_filter,hx,hy,true_and,ha,hb] <;> decide

/-- The multiplicities of all two-coordinate determinants at one shift recover
the central multiplicity up to a size-only correction. -/
theorem pair_multiplicities (A : Finset (ZMod p)) (b : ZMod p) :
    ∑ S ∈ A.powersetCard 2, multiplicity S b =
      multiplicity A b + baseline (A.card-(if -b∈A then 1 else 0)) := by
  classical
  let U := A.filter (fun x => quadraticChar (ZMod p) (x+b)=1)
  let V := A.filter (fun x => quadraticChar (ZMod p) (x+b)= -1)
  have count (T : Finset (ZMod p)) (hT : T⊆A) :
      (∑ S ∈ A.powersetCard 2, (if S⊆T then 1 else 0 : ℕ)) = T.card.choose 2 := by
    have he : (A.powersetCard 2).filter (fun S => S⊆T)=T.powersetCard 2 := by
      ext S
      simp only [mem_filter,mem_powersetCard]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans hT,h.2⟩,h.1⟩⟩
    simp [he]
  rw [sum_congr rfl (fun S hS => pair_profile A S hS b),sum_add_distrib]
  change (∑ S∈A.powersetCard 2, (if S⊆U then 1 else 0:ℕ)) +
    (∑ S∈A.powersetCard 2, (if S⊆V then 1 else 0:ℕ)) = _
  rw [count U (filter_subset ..),count V (filter_subset ..),pair_arithmetic]
  have plus := PaleyShiftListRecovery.agreement_excess A b (Or.inl rfl : (1:ℤ)=1 ∨ 1= -1)
  have minus := PaleyShiftListRecovery.agreement_excess A b (Or.inr rfl : (-1:ℤ)=1 ∨ -1= -1)
  change 1*shiftSum A b=2*(U.card:ℤ)-A.card+_ at plus
  change -1*shiftSum A b=2*(V.card:ℤ)-A.card+_ at minus
  have hw : shiftSum A b=(U.card:ℤ)-V.card := by omega
  have hs : U.card+V.card=A.card-(if -b∈A then 1 else 0) := by split_ifs at * <;> omega
  rw [PaleyShiftMultiplicityBudget.multiplicity,hw,hs]

/-- The complete polynomial identity reconstructing the central determinant
from pair determinants on every admissible puncturing. -/
theorem pair_factorization (hp : p≠2) (A : Finset (ZMod p)) (ha : 2≤A.card)
    (hu : A.card≤p/2+1) :
    ∏ S ∈ A.powersetCard 2, monicCentral S = monicCentral A *
      ∏ b : ZMod p, (X-C b)^baseline (A.card-(if -b∈A then 1 else 0)) := by
  classical
  rw [monic_factors hp A ha hu,← Finset.prod_mul_distrib]
  calc
    _ = ∏ S ∈ A.powersetCard 2, ∏ b : ZMod p, (X-C b)^(multiplicity S b) := by
      apply prod_congr rfl
      intro S hS
      obtain ⟨hsub,hs⟩ := mem_powersetCard.mp hS
      exact monic_factors hp S hs.ge ((card_le_card hsub).trans hu)
    _ = _ := by
      rw [prod_comm]
      apply prod_congr rfl
      intro b _
      rw [Finset.prod_pow_eq_pow_sum,← pow_add,pair_multiplicities]

#print axioms pair_factorization
end ProximityGap.PaleyPairDeterminants
