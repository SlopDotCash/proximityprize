/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PlasticDyadicPeriod
import Mathlib.Tactic

/-!
# A 237-bit prime-field dyadic period above the coefficient 2.05

Pratt subcertificates establish primality. The orbit inequality uses ordinary
Lean kernel reduction over 1024 modular residues.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ArkLib.ProximityGap.Frontier.DyadicLogWitness237
open ArkLib.ProximityGap.BinaryPower (binaryPow binaryPow_eq_pow)
open Finset SubgroupGaussSumSecondMoment Round8CosetConcentration
open scoped Classical

private def factorProduct (v : ℕ×ℕ) := v.1^v.2

private theorem find_factor {q : ℕ} (hq : Nat.Prime q) (L : List (ℕ×ℕ))
    (hd : q ∣ (L.map factorProduct).prod) : ∃ v∈L, q∣v.1 := by
  induction L with
  | nil => simp [hq.not_dvd_one] at hd
  | cons v l ih =>
    change q ∣ v.1^v.2 * _ at hd
    rcases hq.dvd_mul.mp hd with hv|hl
    · exact ⟨v,by simp,hq.dvd_of_dvd_pow hv⟩
    · obtain ⟨a,ha,hh⟩ := ih hl
      exact ⟨a,by simp [ha],hh⟩

private theorem pratt (p a : ℕ) (L : List (ℕ×ℕ))
    (prod : (L.map factorProduct).prod=p-1)
    (hsub : ∀v∈L,Nat.Prime v.1)
    (hmain : binaryPow (a:ZMod p) (p-1)=1)
    (hroot : L.all (fun v ↦ decide (binaryPow (a:ZMod p) ((p-1)/v.1) ≠ 1)) = true) : p.Prime := by
  apply lucas_primality p (a:ZMod p) (by rwa [←binaryPow_eq_pow])
  intro q hq hd
  obtain ⟨v,hv,hqd⟩ := find_factor hq L (prod ▸ hd)
  have he := (Nat.prime_dvd_prime_iff_eq hq (hsub v hv)).mp hqd
  have hr := of_decide_eq_true ((List.all_eq_true.mp hroot) v hv)
  rwa [he, ←binaryPow_eq_pow]

abbrev P : ℕ := 126205134105047729256068842055334737587878534445324289139206048206460929
abbrev g : ZMod P := 50329493603183882829305332600678170099788838530533491465177960535524808
abbrev b : ZMod P := 100685202267360666308840825564462321244913838955279264336631534863815633

private theorem prime_123007 : Nat.Prime 123007 := by
  refine pratt _ 3 [(2,1), (3,1), (13,1), (19,1), (83,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | norm_num

private theorem prime_220931 : Nat.Prime 220931 := by
  refine pratt _ 2 [(2,1), (5,1), (22093,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | hfalse <;> first | contradiction | norm_num

private theorem prime_287789 : Nat.Prime 287789 := by
  refine pratt _ 2 [(2,2), (71947,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | hfalse <;> first | contradiction | norm_num

private theorem prime_575579 : Nat.Prime 575579 := by
  refine pratt _ 2 [(2,1), (287789,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | hfalse <;> first | contradiction | exact prime_287789 | norm_num

private theorem prime_2207939 : Nat.Prime 2207939 := by
  refine pratt _ 2 [(2,1), (37,1), (29837,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | hfalse <;> first | contradiction | norm_num

private theorem prime_11511581 : Nat.Prime 11511581 := by
  refine pratt _ 2 [(2,2), (5,1), (575579,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | hfalse <;> first | contradiction | exact prime_575579 | norm_num

private theorem prime_12161189 : Nat.Prime 12161189 := by
  refine pratt _ 2 [(2,2), (13,1), (17,1), (13757,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | norm_num

private theorem prime_97289513 : Nat.Prime 97289513 := by
  refine pratt _ 3 [(2,3), (12161189,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | hfalse <;> first | contradiction | exact prime_12161189 | norm_num

private theorem prime_194579027 : Nat.Prime 194579027 := by
  refine pratt _ 2 [(2,1), (97289513,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | hfalse <;> first | contradiction | exact prime_97289513 | norm_num

private theorem prime_14734823681 : Nat.Prime 14734823681 := by
  refine pratt _ 6 [(2,8), (5,1), (11511581,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | hfalse <;> first | contradiction | exact prime_11511581 | norm_num

private theorem prime_15860741028112573 : Nat.Prime 15860741028112573 := by
  refine pratt _ 2 [(2,2), (3,1), (271,1), (331,1), (14734823681,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | exact prime_14734823681 | norm_num

private theorem prime_24374842154549147809 : Nat.Prime 24374842154549147809 := by
  refine pratt _ 19 [(2,5), (3,2), (197,1), (2207939,1), (194579027,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | exact prime_2207939 | exact prime_194579027 | norm_num

private theorem prime_75392215528653768844262507 : Nat.Prime 75392215528653768844262507 := by
  refine pratt _ 6 [(2,1), (7,1), (220931,1), (24374842154549147809,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | exact prime_220931 | exact prime_24374842154549147809 | norm_num

private theorem prime_114794534979419968223398044278125666483249057 : Nat.Prime 114794534979419968223398044278125666483249057 := by
  refine pratt _ 5 [(2,5), (3,1), (15860741028112573,1), (75392215528653768844262507,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | exact prime_15860741028112573 | exact prime_75392215528653768844262507 | norm_num

theorem prime : Nat.Prime P := by
  refine pratt _ 13 [(2,11), (3,1), (19,1), (709,1), (20143,1), (72893,1), (73547,1), (123007,1), (114794534979419968223398044278125666483249057,1)] (by decide) ?_ (by decide) (by decide)
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | exact prime_123007 | exact prime_114794534979419968223398044278125666483249057 | norm_num

instance : Fact P.Prime := ⟨prime⟩

theorem primitive : IsPrimitiveRoot g 1024 := by
  have h0 : g^1024=1 := by rw [←binaryPow_eq_pow]; decide
  have h1 : g^512≠1 := by rw [←binaryPow_eq_pow]; decide
  apply IsPrimitiveRoot.iff_orderOf.mpr
  obtain ⟨a,ha,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf g ∣ 2^10 from orderOf_dvd_of_pow_eq_one h0)
  by_contra hh
  have h9 : a≤9 := by
    by_contra hj
    have h10 : a=10 := by omega
    subst a
    exact hh he
  have hd : orderOf g ∣ 512 := by rw [he]; exact pow_dvd_pow _ h9
  exact h1 (orderOf_dvd_iff_pow_eq_one.mp hd)

noncomputable def H : Subgroup (ZMod P)ˣ := Subgroup.zpowers (Units.mk0 g (by decide))

theorem card_H : (sgFinset H).card = 1024 := by
  rw [sgFinset_card,←Nat.card_eq_fintype_card,H,Nat.card_zpowers,←orderOf_units]
  exact primitive.eq_orderOf.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem orbit :
    990*(P:ℤ)^2 < ∑ i ∈ range 1024, PlasticDyadicPeriod.scaledLower (b*binaryPow g i) := by decide

theorem period_re : 990 < (eta ZMod.stdAddChar (sgFinset H) b).re := by
  apply PlasticDyadicPeriod.period_re_of_scaled_sum (by decide : g≠0) primitive 990
  simpa only [binaryPow_eq_pow,Nat.cast_ofNat] using orbit

theorem period_gt_logarithmic :
    41/20 * Real.sqrt (1024*Real.logb 2 ((P:ℝ)/1024)) <
      ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  have hlog : Real.logb 2 ((P:ℝ)/1024) ≤ 227 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num [P])]
    norm_num [P,show (227:ℝ)=(227:ℕ) by norm_num,Real.rpow_natCast]
  have hrad := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤1024))
  have hnum : (41/20:ℝ)*Real.sqrt (1024*227)<990 := by
    rw [mul_comm,←lt_div_iff₀ (by norm_num)]
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
    norm_num
  exact (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrad (by norm_num)) hnum).trans
    (period_re.trans_le (Complex.re_le_norm _))

/-- A nonprincipal frequency on a dyadic subgroup inside the 128-to-256-bit field window. -/
theorem sparse_dyadic_witness :
    P.Prime ∧ 2^128 ≤ P ∧ P < 2^256 ∧ (sgFinset H).card = 2^10 ∧
    (sgFinset H).card^2 ≤ P ∧ b ≠ 0 ∧
    41/20 * Real.sqrt ((sgFinset H).card * Real.logb 2 ((P:ℝ)/(sgFinset H).card)) <
      ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  rw [card_H]
  exact ⟨prime,by decide,by decide,by decide,by decide,by decide,period_gt_logarithmic⟩

#print axioms sparse_dyadic_witness
#print axioms period_re
#print axioms period_gt_logarithmic
#print axioms prime
#print axioms card_H

end ArkLib.ProximityGap.Frontier.DyadicLogWitness237
