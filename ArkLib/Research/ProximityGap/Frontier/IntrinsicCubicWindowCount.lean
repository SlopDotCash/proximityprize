/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeUnrestrictedJetBudget

/-! # Actual dimensions for the unrestricted production cubic auxiliary

The input and quotient scalar/coordinate/value windows are finite index types.
The stated uniform bound on the canonical multiplicity sum implies that their
actual dimension difference exceeds all simultaneous polynomial jet constraints.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace ArkLib.ProximityGap.Frontier.IntrinsicCubicWindowCount
open SecondPrimeQuarticInterpolation SecondPrimeUnrestrictedJetBudget

private def nslots (v d k : ℕ) := ∑ j ∈ range k, (v-j*d)

private theorem lower_card (s b d t : ℕ) : (s+1-b)*nslots t d (b+1) ≤
    Fintype.card (Monomials s b d t) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,nslots,Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => (s+1-j)*(t-j*d))]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (by have := Finset.mem_range.mp hi; omega) _)

private theorem upper_card (s b d t : ℕ) : Fintype.card (Monomials s b d t) ≤
    (s+1)*nslots t d (b+1) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,nslots,Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => (s+1-j)*(t-j*d))]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (Nat.sub_le ..)

private theorem cast_slots (v d k : ℕ) (hk : (k-1)*d ≤ v) :
    (nslots v d k : ℤ) = slots v d k := by
  simp only [nslots,slots,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hh : i*d ≤ v := (Nat.mul_le_mul_right _ (by have := Finset.mem_range.mp hi; omega)).trans hk
  rw [Nat.cast_sub hh,Nat.cast_mul]

abbrev T : ℕ := 32*357913943
abbrev d : ℕ := 67108863
abbrev s : ℕ := 400000000
abbrev ProductionWindow := Monomials s 170 d T
def quotientRows (w : ℕ) := (T-w-1)/d+1

theorem quotient_rows (w : ℕ) (hw : w ≤ 290805098) :
    0 < quotientRows w ∧ (quotientRows w-1)*d ≤ T-w ∧ T-w ≤ quotientRows w*d := by
  unfold quotientRows T d
  omega

private theorem assemble {u q c l J B A : ℕ} (hr : u ≤ J+c) (hq : q ≤ B)
    (hs : B+c<A) (hl : A ≤ l) : u+q<l+J := by omega

set_option maxRecDepth 4096 in
/-- Positivity for the actual window and all of its possible quotient multiples,
given the ordinary-polar bound for the actual site multiplicities. -/
theorem strict_count {I : Type*} [Fintype I] (r : I → ℕ) (w : ℕ)
    (hn : Fintype.card I = 1073741824) (hr : ∀ i, r i ≤ 3)
    (hl : 201326589 ≤ w) (hu : w ≤ 290805098)
    (hR : 3*(∑ i, (r i : ℤ)) ≤ 2*1073741824+16*(w:ℤ)-35*67108863+532) :
    Fintype.card I*(528*400000001) + Fintype.card (Monomials s (quotientRows w-1) d (T-w)) <
      Fintype.card ProductionWindow + ∑ i, ((32-r i)*(32-r i+1)/2)*399999967 := by
  let k := quotientRows w
  let R := ∑ i, r i
  have hk := quotient_rows w hu
  have hkp : 0 < k := hk.1
  have hkw : (k-1)*d ≤ T-w := hk.2.1
  have hkw' : T-w ≤ k*d := hk.2.2
  have leT : w ≤ T := by unfold T; omega
  have hsum : (R : ℤ) = ∑ i, (r i : ℤ) := Nat.cast_sum ..
  have hinc := jet_surplus (w:ℤ) (R:ℤ) (by exact_mod_cast hl) (by exact_mod_cast hu) (by rwa [hsum])
  have slots1 := slot_and_resultant_bounds.1
  have slots2 := slot_difference_lower (T:ℤ) (w:ℤ) (d:ℤ) 171 k (by decide) (by exact_mod_cast hl.trans' (by decide : d ≤ 201326589))
    (by decide) (by decide) (by
      have h' : 1 ≤ k := by omega
      exact_mod_cast (show (((k:ℤ)-1)*(d:ℤ)) ≤ (T:ℤ)-(w:ℤ) by
        simpa only [Nat.cast_mul,Nat.cast_sub h',Nat.cast_sub leT,Nat.cast_one] using
          (Nat.cast_le.mpr hkw : (((k-1)*d:ℕ):ℤ) ≤ ((T-w:ℕ):ℤ)))) (by
      simpa only [Nat.cast_mul,Nat.cast_sub leT] using
        (Nat.cast_le.mpr hkw' : ((T-w:ℕ):ℤ) ≤ ((k*d:ℕ):ℤ)))
  have slotsQ : (nslots (T-w) d k : ℤ) = slots ((T:ℤ)-(w:ℤ)) (d:ℤ) k := by
    rw [cast_slots _ _ _ hkw,Nat.cast_sub leT]
  have slotsS : (nslots T d 171 : ℤ) = 983077772391 := by
    rw [cast_slots _ _ _ (by decide)]
    exact slots1
  have hcost : (s+1)*nslots (T-w) d k + ((s+1)-34)*(31*R+1073741824)+34*1073741824*528 <
      (s+1-170)*nslots T d 171 := by
    zify
    rw [slotsQ,slotsS]
    norm_num only [T,d,s] at slots2 ⊢
    change slots 11453246176 67108863 171 = 983077772391 at slots1
    rw [slots1] at slots2
    nlinarith only [hinc,mul_le_mul_of_nonneg_left slots2 (by decide : (0:ℤ) ≤ 400000001)]
  have low := lower_card s 170 d T
  have up := upper_card s (k-1) d (T-w)
  conv at up => rhs; rw [show k-1+1=k by omega]
  have hb (i : I) : 528*400000001 ≤ ((32-r i)*(32-r i+1)/2)*399999967 +
      399999967*(31*r i+1)+34*528 := by
    have hh := hr i
    interval_cases h' : r i <;> decide
  have hrow := Finset.sum_le_sum (s:= (Finset.univ : Finset I)) fun i _ => hb i
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ← Finset.mul_sum, hn] at hrow
  change 1073741824*(528*400000001) ≤ (∑ i, ((32-r i)*(32-r i+1)/2)*399999967) +
    399999967*(31*R+1073741824*1)+1073741824*(34*528) at hrow
  change Fintype.card I*(528*400000001) + Fintype.card (Monomials s (k-1) d (T-w)) <
    Fintype.card (Monomials s 170 d T) + _
  rw [hn]
  apply assemble (u := 1073741824*(528*400000001)) (q := Fintype.card (Monomials s (k-1) d (T-w)))
    (l := Fintype.card (Monomials s 170 d T)) (J := ∑ i, ((32-r i)*(32-r i+1)/2)*399999967)
    (c := 399999967*(31*R+1073741824)+34*1073741824*528)
    (B := (s+1)*nslots (T-w) d k) (A := (s+1-170)*nslots T d 171)
  · simpa only [Nat.mul_one,Nat.add_assoc] using hrow
  · exact up
  · simpa only [Nat.add_assoc,show s+1-34=399999967 by decide] using hcost
  · exact low

end ArkLib.ProximityGap.Frontier.IntrinsicCubicWindowCount

open ArkLib.ProximityGap.Frontier.IntrinsicCubicWindowCount in
#print axioms strict_count
