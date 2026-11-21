/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldPeriodAlignment
import Mathlib.NumberTheory.LucasPrimality
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# A nonprincipal dyadic Gaussian period above the binary-log constant 2.1

The field element is a root of the plastic polynomial modulo the prime norm of
`1 + α^128`. The final theorem uses a direct integer residue certificate, and
does not require algebraic number theory or numerical cosine evaluation.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.PlasticDyadicPeriod
open Finset SubgroupGaussSumSecondMoment Round8CosetConcentration
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

abbrev P : ℕ := 4283494302159617
abbrev g : ZMod P := 3800919073425889
abbrev b : ZMod P := 4275064871947385

private theorem aux_prime : Nat.Prime 184784261 := by norm_num

theorem prime : P.Prime := by
  apply lucas_primality P 3 (by rw [←binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show P-1 = 2^8*(23*(31*(127*184784261))) by decide] at hd
  simp only [hq.dvd_mul] at hd
  rcases hd with h | h | h | h | h
  · replace h := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst q; rw [←binaryPow_eq_pow]; decide
  · replace h := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23)).mp h
    subst q; rw [←binaryPow_eq_pow]; decide
  · replace h := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31)).mp h
    subst q; rw [←binaryPow_eq_pow]; decide
  · replace h := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 127)).mp h
    subst q; rw [←binaryPow_eq_pow]; decide
  · replace h := (Nat.prime_dvd_prime_iff_eq hq aux_prime).mp h
    subst q; rw [←binaryPow_eq_pow]; decide

instance : Fact P.Prime := ⟨prime⟩

theorem primitive : IsPrimitiveRoot g 256 := by
  have h0 : g^256=1 := by decide
  have h1 : g^128≠1 := by decide
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have hd := orderOf_dvd_of_pow_eq_one h0
  obtain ⟨a,ha,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf g ∣ 2^8 from hd)
  by_contra hh
  have h7 : a≤7 := by
    by_contra hj
    have h8 : a=8 := by omega
    subst a
    exact hh he
  have hd' : orderOf g ∣ 128 := by rw [he]; exact pow_dvd_pow _ h7
  exact h1 (orderOf_dvd_iff_pow_eq_one.mp hd')

def scaledLower {q : ℕ} (x : ZMod q) : ℤ :=
  max ((q:ℤ)^2-20*x.valMinAbs^2) (-(q:ℤ)^2)

private theorem centered_bound {q : ℕ} [Fact q.Prime] (x : ZMod q) :
    (scaledLower x:ℝ) ≤ (q:ℝ)^2*(ZMod.stdAddChar x).re := by
  have hq : (0:ℝ)<q := by exact_mod_cast (Fact.out : q.Prime).pos
  let a := x.valMinAbs
  have hr : (ZMod.stdAddChar x).re = Real.cos (2*Real.pi*a/q) := by
    conv_lhs => rw [←x.coe_valMinAbs,ZMod.stdAddChar_coe]
    have he : (2*Real.pi*Complex.I*(a:ℂ)/q:ℂ) = ((2*Real.pi*a/q : ℝ):ℂ)*Complex.I := by
      push_cast; ring
    rw [show (2*Real.pi*Complex.I*(x.valMinAbs:ℂ)/q:ℂ)=_ from he, Complex.exp_ofReal_mul_I_re]
  rw [hr,scaledLower,Int.cast_max]
  simp only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_neg]
  apply max_le
  · have hc := Real.one_sub_sq_div_two_le_cos (x:=2*Real.pi*a/q)
    have hpi : 2*Real.pi^2 ≤ 20 := by nlinarith [Real.pi_pos, Real.pi_lt_d2, mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2]
    calc (q:ℝ)^2-20*(x.valMinAbs:ℝ)^2 ≤ (q:ℝ)^2-2*Real.pi^2*(a:ℝ)^2 :=
          by dsimp [a]; nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (sq_nonneg (x.valMinAbs:ℝ))]
      _ = (q:ℝ)^2*(1-(2*Real.pi*a/q)^2/2) := by field_simp
      _ ≤ (q:ℝ)^2 * Real.cos (2*Real.pi*a/q) := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  · have hh := Real.neg_one_le_cos (2*Real.pi*a/q)
    nlinarith [mul_nonneg (sq_nonneg (q:ℝ)) (show 0≤1+Real.cos (2*Real.pi*a/q) by linarith)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem scaled_sum :
    223*(P:ℤ)^2 < ∑ i ∈ range 256, scaledLower (b*g^i) := by decide

noncomputable def H : Subgroup (ZMod P)ˣ := Subgroup.zpowers (Units.mk0 g (by decide))

open scoped Classical

set_option maxRecDepth 100000

theorem card_H : (sgFinset H).card=256 := by
  rw [sgFinset_card,←Nat.card_eq_fintype_card,H,Nat.card_zpowers,←orderOf_units]
  exact primitive.eq_orderOf.symm

private theorem pow_image_eq {q k : ℕ} [Fact q.Prime] {z : ZMod q}
    (hz : z ≠ 0) (h : IsPrimitiveRoot z k) :
    (range k).image (fun i : ℕ ↦ z^i) = sgFinset (Subgroup.zpowers (Units.mk0 z hz)) := by
  classical
  let u := Units.mk0 z hz
  have hinj : Set.InjOn (fun i : ℕ ↦ z^i) (range k) :=
    fun _ hi _ hj he ↦ h.pow_inj (mem_range.mp hi) (mem_range.mp hj) he
  have hcard : (sgFinset (Subgroup.zpowers u)).card=k := by
    rw [sgFinset_card,←Nat.card_eq_fintype_card,Nat.card_zpowers,←orderOf_units]
    exact h.eq_orderOf.symm
  exact eq_of_subset_of_card_le (fun x hx ↦ by
    obtain ⟨j,_,rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨⟨u^j,Subgroup.npow_mem_zpowers _ _⟩,mem_univ _,Units.val_pow_eq_pow_val u j⟩)
    (by rw [hcard,card_image_of_injOn hinj,card_range])

/-- An integer certificate on centered residues gives a real lower bound for the period
of the entire cyclic subgroup at the specified frequency. -/
theorem period_re_of_scaled_sum {q k : ℕ} [Fact q.Prime] {z y : ZMod q}
    (hz : z ≠ 0) (h : IsPrimitiveRoot z k) (c : ℕ)
    (hc : (c:ℤ)*(q:ℤ)^2 < ∑ i ∈ range k, scaledLower (y*z^i)) :
    (c:ℝ) < (eta ZMod.stdAddChar (sgFinset (Subgroup.zpowers (Units.mk0 z hz))) y).re := by
  have hq : (0:ℝ)<q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hsum := sum_le_sum (s := range k) (fun i _ ↦ centered_bound (y*z^i))
  rw [← mul_sum] at hsum
  have hcert := (Int.cast_lt (R := ℝ)).mpr hc
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_sum] at hcert
  have hh := lt_of_lt_of_le hcert hsum
  rw [mul_comm (c:ℝ)] at hh
  have hi := lt_of_mul_lt_mul_left hh (sq_nonneg (q:ℝ))
  rw [eta, ←pow_image_eq hz h, sum_image, Complex.re_sum]
  · exact hi
  · intro i hi j hj he
    exact h.pow_inj (mem_range.mp hi) (mem_range.mp hj) he

/-- Actual nonprincipal period on the 256-element subgroup. -/
theorem period_re : 223 < (eta ZMod.stdAddChar (sgFinset H) b).re :=
  period_re_of_scaled_sum (by decide) primitive 223 scaled_sum

/-- A dyadic sparse instance exceeds the binary-log upper bound with coefficient 2.1. -/
theorem period_gt_logarithmic :
    21/10 * Real.sqrt (256 * Real.logb 2 ((P:ℝ)/256)) <
      ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  have hlog : Real.logb 2 ((P:ℝ)/256) ≤ 44 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num [P])]
    norm_num [P, show (44:ℝ)=(44:ℕ) by norm_num, Real.rpow_natCast]
  have hrad := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤256))
  have hnum : (21/10:ℝ)*Real.sqrt (256*44)<223 := by
    rw [mul_comm, ← lt_div_iff₀ (by norm_num)]
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
    norm_num
  have hh : 21/10 * Real.sqrt (256 * Real.logb 2 ((P:ℝ)/256)) < 223 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrad (by norm_num)) hnum
  exact hh.trans (period_re.trans_le (Complex.re_le_norm _))

/-- Primality, dyadic cardinality, sparsity, frequency and coefficient in a single statement. -/
theorem sparse_dyadic_witness :
    P.Prime ∧ (sgFinset H).card = 2^8 ∧ (sgFinset H).card^2 ≤ P ∧ b ≠ 0 ∧
    21/10 * Real.sqrt ((sgFinset H).card * Real.logb 2 ((P:ℝ)/(sgFinset H).card)) <
      ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  rw [card_H]
  exact ⟨prime,by decide,by decide,by decide,period_gt_logarithmic⟩

#print axioms sparse_dyadic_witness
#print axioms period_re
#print axioms period_gt_logarithmic
#print axioms prime
#print axioms primitive
#print axioms scaled_sum

end ArkLib.ProximityGap.Frontier.PlasticDyadicPeriod
