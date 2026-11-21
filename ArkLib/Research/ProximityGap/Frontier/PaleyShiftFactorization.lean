/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.ToMathlib.Polynomial.RootMultiplicity
import ArkLib.Research.ProximityGap.Frontier.PaleyHankelDegree
import ArkLib.Research.ProximityGap.Frontier.PaleyInterpolationContact
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftMultiplicityBudget

/-!
# An interpolation determinant for quadratic-character shift sums

At every shift the sign imbalance forces a square-sized root multiplicity.
-/

namespace ProximityGap.PaleyShiftFactorization

open Finset Polynomial PaleyInterpolationContact PaleyShiftMultiplicityBudget
open scoped Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- Degree and width are chosen so the local orders consume the whole determinant. -/
noncomputable def central (A : Finset (ZMod p)) : (ZMod p)[X] :=
  let D := p/2+(A.card-2)
  (PaleyDefectMinor.normalizedHankel (powerSum A A D) D (A.card/2-1)).det

private theorem int_toNat_eq {v : ℤ} {j : ℕ} (h : v=(j : ℤ)) : v.toNat=j := by simp [h]

private theorem quarter_square {a e z : ℕ} (ha : 2 ≤ a) (hz : z ≤ 1)
    {w : ℤ} (hw : w = (a : ℤ) - z - 2*e) (hw0 : 0 ≤ w) :
    let h := a/2-1
    let r := h+1-e
    let ν := a-1-z
    (w^2 / 4).toNat = r*(ν-2*h)+r*(r-1) := by
  let h := a/2-1
  let r := h+1-e
  let ν := a-1-z
  change _ = r*(ν-2*h)+r*(r-1)
  have hr : (r : ℤ) = (a/2 : ℕ) - (e : ℤ) := by dsimp [r,h]; omega
  rcases Nat.mod_two_eq_zero_or_one a with hev|hod <;>
    rcases (show z = 0 ∨ z = 1 by omega) with rfl|rfl
  · have hs : ν - 2*h = 1 := by dsimp [ν,h]; omega
    have heq : w = 2 * (r : ℤ) := by omega
    rw [hs, heq, show (2*(r : ℤ))^2 = 4*((r : ℤ)^2) by ring]
    cases r <;> simp
    apply int_toNat_eq
    push_cast
    ring
  · have hs : ν - 2*h = 0 := by dsimp [ν,h]; omega
    have heq : w = 2 * (r : ℤ) - 1 := by omega
    obtain ⟨v,hv⟩ : ∃ v, r=v+1 := ⟨r-1,by omega⟩
    rw [hs, heq, hv]
    push_cast
    rw [show (2*((v:ℤ)+1)-1)^2 = 4*((v:ℤ)^2+v)+1 by ring]
    simp [Int.add_ediv_of_dvd_left]
    apply int_toNat_eq
    push_cast
    ring
  · have hs : ν - 2*h = 2 := by dsimp [ν,h]; omega
    have heq : w = 2 * (r : ℤ) + 1 := by omega
    rw [hs, heq, show (2*(r : ℤ)+1)^2 = 4*((r : ℤ)^2+r)+1 by ring]
    cases r <;> simp [Int.add_ediv_of_dvd_left]
    apply int_toNat_eq
    push_cast
    ring
  · have hs : ν - 2*h = 1 := by dsimp [ν,h]; omega
    have heq : w = 2 * (r : ℤ) := by omega
    rw [hs, heq, show (2*(r : ℤ))^2 = 4*((r : ℤ)^2) by ring]
    cases r <;> simp
    apply int_toNat_eq
    push_cast
    ring

/-- The interpolation determinant has the predicted root at every prescribed shift. -/
theorem shift_dvd (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) (b : ZMod p) :
    (X-C b)^(multiplicity A b) ∣ central A := by
  classical
  let W := shiftSum A b
  let σ : ℤ := if 0 ≤ W then 1 else -1
  have hs : σ=1 ∨ σ=-1 := by unfold σ; split <;> simp
  have hns : -σ=1 ∨ -σ=-1 := by rcases hs with h|h <;> simp [h]
  let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -σ
  let z : ℕ := if -b ∈ A then 1 else 0
  let w := σ * W
  have hw0 : 0 ≤ w := by dsimp [w,σ]; split <;> simp_all; omega
  have hsign : w^2 = W^2 := by dsimp [w]; rcases hs with h|h <;> simp [h]
  have he := PaleyShiftListRecovery.agreement_excess A b hns
  have hw : w = (A.card : ℤ) - z - 2*E.card := by
    change -σ * W = _ at he
    simp only [PaleyShiftListRecovery.agreements, add_comm] at he
    dsimp only [w, E, z]
    split_ifs at he ⊢ <;> push_cast <;> linarith
  have hz : z ≤ 1 := by dsimp [z]; split <;> decide
  have hquota := quarter_square ha hz hw hw0
  let h := A.card/2-1
  let ν := if -b ∈ A then A.card-2 else A.card-2+1
  have hnu : A.card-1-z=ν := by dsimp [z,ν]; split <;> omega
  have hmid : 2*h ≤ ν := by dsimp [h,ν]; split <;> omega
  rw [hsign,hnu] at hquota
  change (X-C b)^( (W^2/4).toNat ) ∣ _
  rw [hquota]
  have hdet := minority_determinant hp A b (k := A.card-2) (h := h)
    (by omega) (by omega) hmid hs
  simpa [central, h, ν, E, show A.card-2 ≠ A.card-1 by omega] using hdet

/-- Nonvanishing and exact degree of the central determinant, including degree zero. -/
theorem central_degree (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) :
    central A ≠ 0 ∧ (central A).natDegree = A.card/2*((p-1)/2-A.card/2) := by
  let D := p/2+(A.card-2)
  let h := A.card/2-1
  let F := powerSum A A D
  have hprime := (Fact.out : p.Prime).two_le
  obtain ⟨u,hu⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hd : D < p := by dsimp [D]; omega
  obtain ⟨hdeg,hF⟩ := powerSum_degree A ha (D := D) (by dsimp [D]; omega) hd
  have ht : F.natDegree = p/2-1 := by change (powerSum A A D).natDegree = _; rw [hdeg]; dsimp [D]; omega
  have hl : 2*h ≤ F.natDegree := by rw [ht]; dsimp [h]; omega
  have hupper : F.natDegree ≤ D := by rw [ht]; dsimp [D]; omega
  have hgap : h ≤ D-F.natDegree := by rw [ht]; dsimp [D,h]; omega
  refine ⟨PaleyHankelDegree.normalizedHankel_det_ne_zero F hF D h hl hupper hgap hd, ?_⟩
  change (PaleyDefectMinor.normalizedHankel F D h).det.natDegree = _
  rw [PaleyHankelDegree.normalizedHankel_det_degree F hF D h hl hupper hgap hd, ht]
  dsimp [h]
  congr 1 <;> omega

/-- The prime-field determinant factors completely, with the precise multiplicity
encoded by the integer quadratic-character sum at each shift. -/
theorem central_factorization (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) :
    central A = C (central A).leadingCoeff * ∏ b : ZMod p, (X-C b)^(multiplicity A b) := by
  apply eq_leadingCoeff_mul_prod_of_local_dvd
  · rw [sum_multiplicity hp, (central_degree hp A ha ha').2]
  · exact fun b _ => shift_dvd hp A ha ha' b

/-- The exact order at a chosen field element can be read without factoring. -/
theorem rootMultiplicity_central (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) (b : ZMod p) :
    (central A).rootMultiplicity b = ((shiftSum A b)^2/4).toNat := by
  have hd := central_degree hp A ha ha'
  have hle (c : ZMod p) : multiplicity A c ≤ (central A).rootMultiplicity c :=
    (le_rootMultiplicity_iff hd.1).mpr (shift_dvd hp A ha ha' c)
  apply le_antisymm _ (hle b)
  by_contra! hbad
  have hstrict := Finset.sum_lt_sum (s := (univ : Finset (ZMod p))) (fun c _ => hle c)
    ⟨b,mem_univ b,hbad⟩
  have hcap := Polynomial.sum_rootMultiplicity_le_natDegree (W := central A) univ
  rw [sum_multiplicity hp] at hstrict
  omega

end ProximityGap.PaleyShiftFactorization

#print axioms ProximityGap.PaleyShiftFactorization.shift_dvd

#print axioms ProximityGap.PaleyShiftFactorization.central_factorization

#print axioms ProximityGap.PaleyShiftFactorization.rootMultiplicity_central
