/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadFibers

/-! # Three disjoint cubic coincidence fibers over arbitrary fields -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.SmoothCosetCubicSeed
open SmoothFourHeadFibers (bucket)

variable {K : Type} [Field K]

/-- Splitting of the difference of the two cubic locators at a sixteenth root. -/
theorem split (w t : K) (h : w^8 = -1) :
    (t-1)*(t-w)*(t-w^8) - w^2*((t-w^2)*(t-w^9)*(t-w^10)) =
      (1-w^2)*((t-w^3)*(t-w^5)*(t-w^7)) := by
  have hzero : w^8+1=0 := by rw [h]; ring
  linear_combination (w^15-w^9 + (w-w^13)*t + (w^4+w^3-w-1)*t^2)*hzero

def values (w t : K) : Fin 3 → K :=
  ![0, (t-1)*(t-w)*(t-w^8), w^2*((t-w^2)*(t-w^9)*(t-w^10))]

/-- On an order-`16*r` subgroup the three pairs are equal at precisely their three exponent classes. -/
theorem table {r q : ℕ} (hr : 0<r) (hq : q=16*r) (v : K) (hv : orderOf v=q)
    (i : Fin q) (a b : Fin 3) :
    values (v^r) (v^i.val) a = values (v^r) (v^i.val) b ↔
      SmoothFourHeadFibers.coincide (bucket r i.val) a b := by
  let w := v^r
  have poweq (a : ℕ) (ha : a<16) : v^i.val = w^a ↔ i.val=a*r := by
    change v^i.val=(v^r)^a ↔ _
    rw [← pow_mul, mul_comm r a]
    have bnd : a*r < orderOf v := by
      rw [hv,hq]; exact Nat.mul_lt_mul_of_pos_right ha hr
    exact ⟨pow_injOn_Iio_orderOf (hv ▸ i.isLt) bnd,fun h => by rw [h]⟩
  have ord : orderOf w = 16 := by
    change orderOf (v^r)=16
    rw [orderOf_pow_of_dvd (by omega : r≠0) (hv ▸ hq ▸ dvd_mul_left r 16), hv,hq,
      Nat.mul_div_cancel _ hr]
  have h8 : w^8 = -1 := by
    have h : (w^8)^2=1 := by
      rw [← pow_mul, show 8*2=orderOf w by omega, pow_orderOf_eq_one]
    exact (sq_eq_one_iff.mp h).resolve_left (fun he => by
      have hd := orderOf_dvd_of_pow_eq_one he
      rw [ord] at hd; exact (by decide : ¬16 ∣ 8) hd)
  have h2 : 1-w^2≠0 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp h).symm
    rw [ord] at hd; exact (by decide : ¬16 ∣ 2) hd
  have hw : w ≠ 0 := by intro h; simp [h] at h8
  let t := v^i.val
  have h01 : values w t 0=values w t 1 ↔ i.val=0 ∨ i.val=r ∨ i.val=8*r := by
    change 0=(t-1)*(t-w)*(t-w^8) ↔ _
    have p0 := poweq 0 (by decide)
    have p1 := poweq 1 (by decide)
    simp only [pow_zero,zero_mul] at p0
    simp only [pow_one,one_mul] at p1
    rw [eq_comm (a:=(0:K)) (b:=_ * _)]
    simp only [mul_eq_zero,sub_eq_zero,t,p0,p1,poweq _ (by decide : 8<16),or_assoc]
  have h02 : values w t 0=values w t 2 ↔ i.val=2*r ∨ i.val=9*r ∨ i.val=10*r := by
    change 0=w^2*((t-w^2)*(t-w^9)*(t-w^10)) ↔ _
    rw [eq_comm (a:=(0:K)) (b:=_ * _)]
    simp only [mul_eq_zero,pow_ne_zero _ hw,false_or,sub_eq_zero,t,
      poweq _ (by decide : 2<16),poweq _ (by decide : 9<16),poweq _ (by decide : 10<16),or_assoc]
  have h12 : values w t 1=values w t 2 ↔ i.val=3*r ∨ i.val=5*r ∨ i.val=7*r := by
    rw [← sub_eq_zero]
    change (t-1)*(t-w)*(t-w^8)-w^2*((t-w^2)*(t-w^9)*(t-w^10))=0 ↔ _
    simp only [split w t h8,mul_eq_zero,h2,false_or,sub_eq_zero,t,
      poweq _ (by decide : 3<16),poweq _ (by decide : 5<16),poweq _ (by decide : 7<16),or_assoc]
  change values w t a=values w t b ↔ _
  have h10 := (eq_comm (a:=values w t 1) (b:=values w t 0)).trans h01
  have h20 := (eq_comm (a:=values w t 2) (b:=values w t 0)).trans h02
  have h21 := (eq_comm (a:=values w t 2) (b:=values w t 1)).trans h12
  fin_cases a <;> fin_cases b
  all_goals try exact iff_of_true rfl (Or.inl rfl)
  · change values w t 0=values w t 1 ↔ SmoothFourHeadFibers.coincide (bucket r i.val) 0 1
    rw [h01]
    unfold bucket
    split_ifs <;> simp [SmoothFourHeadFibers.coincide] <;> omega
  · change values w t 0=values w t 2 ↔ SmoothFourHeadFibers.coincide (bucket r i.val) 0 2
    rw [h02]
    unfold bucket
    split_ifs <;> simp [SmoothFourHeadFibers.coincide] <;> omega
  · change values w t 1=values w t 0 ↔ SmoothFourHeadFibers.coincide (bucket r i.val) 1 0
    rw [h10]
    unfold bucket
    split_ifs <;> simp [SmoothFourHeadFibers.coincide] <;> omega
  · change values w t 1=values w t 2 ↔ SmoothFourHeadFibers.coincide (bucket r i.val) 1 2
    rw [h12]
    unfold bucket
    split_ifs <;> simp [SmoothFourHeadFibers.coincide] <;> omega
  · change values w t 2=values w t 0 ↔ SmoothFourHeadFibers.coincide (bucket r i.val) 2 0
    rw [h20]
    unfold bucket
    split_ifs <;> simp [SmoothFourHeadFibers.coincide] <;> omega
  · change values w t 2=values w t 1 ↔ SmoothFourHeadFibers.coincide (bucket r i.val) 2 1
    rw [h21]
    unfold bucket
    split_ifs <;> simp [SmoothFourHeadFibers.coincide] <;> omega

private def factor (s : ℕ) (c a : K) : K[X] :=
  (C c * (Polynomial.X : K[X]))^s - C a

private def cubic (s : ℕ) (c a b d : K) : K[X] :=
  factor s c a * factor s c b * factor s c d

/-- The power substitution includes the inverse of the coset representative. -/
def seed (s : ℕ) (c w : K) : Fin 3 → K[X] :=
  ![0, cubic s c 1 w (w^8), C (w^2)*cubic s c (w^2) (w^9) (w^10)]

theorem degree (s : ℕ) (c w : K) (j : Fin 3) : (seed s c w j).natDegree ≤ 3*s := by
  have hf (a : K) : (factor s c a).natDegree ≤ s := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_pow_le.trans
      have h := (natDegree_C_mul_le c (Polynomial.X : K[X])).trans natDegree_X_le
      simpa using Nat.mul_le_mul_left s h
    · simp
  have hc (a b d : K) : (cubic s c a b d).natDegree ≤ 3*s := by
    have h := (natDegree_mul_le (p:=factor s c a) (q:=factor s c b)).trans (add_le_add (hf a) (hf b))
    have ht := (natDegree_mul_le (p:=factor s c a * factor s c b) (q:=factor s c d)).trans
      (add_le_add h (hf d))
    unfold cubic
    omega
  fin_cases j
  · simp [seed]
  · exact hc _ _ _
  · exact (natDegree_C_mul_le _ _).trans (hc _ _ _)

private theorem eval_seed (s : ℕ) (c w x : K) (j : Fin 3) :
    (seed s c w j).eval x = values w ((c*x)^s) j := by
  fin_cases j <;> simp [seed,cubic,factor,values]

/-- On any multiplicative coset the power substitution pulls back exactly the same
three pair-coincidence fibers. -/
theorem eval_iff {s q r : ℕ} (hs : 0<s) (hr : 0<r) (hq : q=16*r) (c g : K) (hc : c≠0)
    (hg : orderOf g=s*q) (dom : Fin (s*q) ↪ K) (hd : ∀ i, dom i=c*g^i.val) (i : Fin (s*q)) (a b : Fin 3) :
    let w := (g^s)^r
    (seed s c⁻¹ w a).eval (dom i)=(seed s c⁻¹ w b).eval (dom i) ↔
      SmoothFourHeadFibers.coincide (bucket r (i.val%q)) a b := by
  dsimp only
  let v := g^s
  have hv : orderOf v=q := by
    change orderOf (g^s)=q
    rw [orderOf_pow_of_dvd (by omega : s≠0) (hg ▸ dvd_mul_right s q),hg,Nat.mul_div_cancel_left _ hs]
  have hvq : v^q=1 := hv ▸ pow_orderOf_eq_one v
  have hpow : (c⁻¹*dom i)^s=v^(i.val%q) := by
    rw [hd, inv_mul_cancel_left₀ hc, ← pow_mul, mul_comm, pow_mul]
    change v^i.val=_
    calc
      _=v^(i.val%q+q*(i.val/q)) := congrArg (v^·) (Nat.mod_add_div _ _).symm
      _=_ := by rw [pow_add,pow_mul,hvq,one_pow,mul_one]
  rw [eval_seed,eval_seed,hpow]
  exact table hr hq v hv ⟨_,Nat.mod_lt _ (by omega)⟩ a b

#print axioms eval_iff
#print axioms table
end ArkLib.ProximityGap.Frontier.SmoothCosetCubicSeed
