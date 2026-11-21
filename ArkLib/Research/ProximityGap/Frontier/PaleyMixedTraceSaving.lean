/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleySubgroupTransversal
import ArkLib.Research.ProximityGap.Frontier.MobiusSubgroupBound
import ArkLib.Research.ProximityGap.Frontier.PaleyMixedProductTraces
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality

/-! # Fractional-linear images in mixed trace discrepancy

The sum and difference of the two exponent indices turn a mixed product
difference into a linear polynomial in one subgroup variable, whose root is
fractional-linear in the other. Stepanov interpolation controls its occupancy
in every multiplicative coset.
-/
namespace ProximityGap.PaleyMixedTraceSaving
open Finset PaleyInversionTrace
open ArkLib.ProximityGap.Frontier.PaleySubgroupTransversal
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
variable {F : Type*} [Field F]

/-- Bilinear numerator in ratio and product coordinates, including the pole row. -/
theorem ratio_product_identity (s t : F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (productTrace s x-productTrace t y)*x =
      (x/y-1)*(x*y) - t*(x/y)+s := by
  unfold productTrace
  field_simp
  ring

/-- Removing the zero and pole leaves this fractional linear coordinate. -/
def fractional (c a b x : F) := c*(x-a)/(x-b)

variable [DecidableEq F]

/-- The occupancy bound needed in the fourth moment follows from the finite
rectangular Stepanov theorem. No assumption on the target coset is required. -/
theorem occupancy {p N u : ℕ} [CharP F p] (hp : p.Prime) (hu : 0<u)
    (hn : 2*u^3≤N) (hchar : 2*u^2-1+N*(u-1)<p)
    (Z H : Finset F) {c a b : F} (hc : c ≠ 0) (ha : a ≠ 0) (hab : a ≠ b)
    (hreg : ∀ x∈Z, x≠0 ∧ x≠a ∧ x≠b)
    (hz : ∀ x∈Z, x^N=1) (hh : ∀ y∈H, y^N=1) (v : F) :
    ((Z.image (fractional c a b)) ∩ coset H v).card ≤
      (2*u^2-1+N*(u-1)+N*(2*u-1))/u^2 := by
  classical
  let S := Z.filter fun x => fractional c a b x ∈ coset H v
  have hsub : Z.image (fractional c a b) ∩ coset H v ⊆ S.image (fractional c a b) := by
    intro y hy
    obtain ⟨hin,hcos⟩ := mem_inter.mp hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hin
    exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx,hcos⟩, rfl⟩
  have hratio (x : F) (hx : x∈S) : (x-a)^N=(v/c)^N*(x-b)^N := by
    obtain ⟨hxZ,hxc⟩ := mem_filter.mp hx
    obtain ⟨z,hzH,he⟩ := mem_image.mp hxc
    have hxb := sub_ne_zero.mpr (hreg x hxZ).2.2
    have hef : x-a=(v/c)*(x-b)*z := by
      unfold fractional at he
      field_simp [hxb] at he ⊢
      linear_combination -he
    rw [hef, mul_pow, mul_pow, hh z hzH, mul_one]
  have hstep := MobiusSubgroupBound.cubic_scale hp hu hn hchar ha hab S
    (fun x hx => hreg x (mem_filter.mp hx).1)
    (fun x hx => hz x (mem_filter.mp hx).1) hratio
  apply (card_le_card hsub).trans
  apply card_image_le.trans
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  simpa [Nat.mul_comm] using hstep

/-- The signed rectangle moment after substituting fractional-linear incidence. -/
theorem fractional_fourth [Fintype F] {p N u : ℕ} [CharP F p] (hp : p.Prime)
    (hF : ringChar F ≠ 2) (hu : 0<u) (hn : 2*u^3≤N)
    (hchar : 2*u^2-1+N*(u-1)<p) (Z H : Finset F) (hH : IsMulSubgroup H)
    {c a b : F} (hc : c ≠ 0) (ha : a ≠ 0) (hab : a ≠ b)
    (hreg : ∀ x∈Z, x≠0 ∧ x≠a ∧ x≠b) (hz : ∀ x∈Z, x^N=1) (hh : ∀ y∈H, y^N=1)
    {r : ℕ} (hr : 0<r) (hrH : r≤H.card) (hsmall : r^4≤Fintype.card F)
    (w : F→ℤ) (hw : ∀ y∈Z.image (fractional c a b), w y ^ 4=1) :
    (∑ z ∈ Z.image (fractional c a b), w z * ∑ y∈H, quadraticChar F (z-y))^4 * (r:ℤ)^2 ≤
      ((Z.card:ℤ)*H.card)^3 *
        (((2*u^2-1+N*(u-1)+N*(2*u-1))/u^2 : ℕ):ℤ) * fourthConstant (Fintype.card F) *
          Fintype.card F := by
  have h₀ : (0:F) ∉ Z.image (fractional c a b) := by
    rintro he
    obtain ⟨x,hx,he⟩ := mem_image.mp he
    have hr := hreg x hx
    exact div_ne_zero (mul_ne_zero hc (sub_ne_zero.mpr hr.2.1)) (sub_ne_zero.mpr hr.2.2) he
  apply (weighted_subgroup_sum_fourth_le hF _ H hH h₀ _
    (occupancy hp hu hn hchar Z H hc ha hab hreg hz hh) r hr hrH hsmall w hw).trans
  have hcard : ((Z.image (fractional c a b)).card:ℤ) ≤ Z.card := by
    exact_mod_cast (card_image_le (s:=Z) (f:=fractional c a b))
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcard (by positivity)) 3

/-- The Goldilocks prime used in the explicit sub-square-root example. -/
abbrev goldilocks : ℕ := 18446744069414584321

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem goldilocks_prime : Nat.Prime goldilocks := by
  refine lucas_primality goldilocks 7 ?_ ?_
  · rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
  · intro q hq hdiv
    rw [show goldilocks-1=2^32*(3*(5*(17*(257*65537)))) by decide] at hdiv
    simp only [hq.dvd_mul] at hdiv
    rcases hdiv with h|h|h|h|h|h
    · have := Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
      subst q; rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
    all_goals
      have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst q; rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide

local instance : Fact goldilocks.Prime := ⟨goldilocks_prime⟩

/-- Uniform bound on each signed fractional-linear rectangle in the two parity
classes, in the Goldilocks field at full subgroup length `2^30`. -/
theorem goldilocks_rectangle (Z H : Finset (ZMod goldilocks)) (hH : IsMulSubgroup H)
    (hZ : Z.card≤2^29) (hsize : H.card=2^29)
    {c a b : ZMod goldilocks} (hc : c ≠ 0) (ha : a ≠ 0) (hab : a ≠ b)
    (hreg : ∀ x∈Z, x≠0 ∧ x≠a ∧ x≠b)
    (hz : ∀ x∈Z, x^(2^29:ℕ)=1) (hh : ∀ y∈H, y^(2^29:ℕ)=1)
    (w : ZMod goldilocks → ℤ) (hw : ∀ y∈Z.image (fractional c a b), w y ^ 4=1) :
    |∑ z ∈ Z.image (fractional c a b), w z * ∑ y∈H, quadraticChar _ (z-y)| ≤
      230497831808523881 := by
  let S := ∑ z ∈ Z.image (fractional c a b), w z * ∑ y∈H, quadraticChar _ (z-y)
  change |S| ≤ _
  have hg := fractional_fourth (u:=645) goldilocks_prime (by rw [ZMod.ringChar_zmod_n]; decide)
    (by decide) (by decide) (by decide) Z H hH hc ha hab hreg hz hh
    (r:=65535) (by decide) (by rw [hsize]; decide) (by rw [ZMod.card]; decide) w hw
  change S^4 * _ ≤ _ at hg
  rw [ZMod.card, hsize] at hg
  have hZ' : (Z.card:ℤ) ≤ (2:ℤ)^29 := by exact_mod_cast hZ
  have hupper : S^4 * 65535^2 ≤
      (((2:ℤ)^29)*2^29)^3 * 2494495 * 11 * goldilocks := by
    have hK : (2*645^2-1+(2^29)*(645-1)+(2^29)*(2*645-1))/645^2 = 2494495 := by decide
    have hC : fourthConstant goldilocks = 11 := by decide
    rw [hK, hC] at hg
    push_cast at hg
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hZ' (by positivity)) 3
  by_contra! h
  have hbase : (230497831808523882:ℤ) ≤ |S| := by omega
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℤ)≤230497831808523882) hbase 4
  rw [(show Even 4 by decide).pow_abs] at hpow
  norm_num [goldilocks] at hpow hupper
  omega

private def undo (c a b z : F) := (z*b-c*a)/(z-c)

omit [DecidableEq F] in
private theorem undo_fractional {c a b x : F} (hc : c≠0) (hab : a≠b) (hx : x≠b) :
    undo c a b (fractional c a b x)=x := by
  have hn : fractional c a b x-c ≠ 0 := by
    unfold fractional
    intro he
    field_simp [sub_ne_zero.mpr hx] at he
    have hz : c*(a-b)=0 := by linear_combination -he
    exact mul_ne_zero hc (sub_ne_zero.mpr hab) hz
  unfold undo
  apply (div_eq_iff hn).mpr
  unfold fractional
  field_simp [sub_ne_zero.mpr hx]
  ring

private theorem abs_char_le_one [Fintype F] (x : F) : |quadraticChar F x|≤1 := by
  by_cases hx : x=0
  · simp [hx]
  rcases quadraticChar_dichotomy hx with h|h <;> simp [h]

/-- The complete bilinear sum on a Goldilocks parity class, including its pole and zero rows. -/
theorem goldilocks_parity (H : Finset (ZMod goldilocks)) (hH : IsMulSubgroup H)
    (hsize : H.card=2^29) (hh : ∀ y∈H, y^(2^29:ℕ)=1)
    {s t γ : ZMod goldilocks} (hs : s≠0) (ht : t≠0) (hg : γ≠0) (hst : s≠t) :
    |∑ x∈H, ∑ y∈H, quadraticChar _ ((γ*x-1)*(γ*y)-t*(γ*x)+s)| ≤
      230497832882265705 := by
  classical
  let a := s/(t*γ)
  let b := 1/γ
  let c := t/γ
  have ha : a ≠ 0 := div_ne_zero hs (mul_ne_zero ht hg)
  have hc : c ≠ 0 := div_ne_zero ht hg
  have hab : a ≠ b := by
    intro he
    apply hst
    dsimp [a,b] at he
    field_simp at he
    exact he
  let Z := H.filter fun x => x≠a ∧ x≠b
  have hsub : Z ⊆ H := filter_subset ..
  have hreg (x) (hx : x∈Z) : x≠0 ∧ x≠a ∧ x≠b :=
    ⟨ne_zero_of_mem hH (hsub hx), (mem_filter.mp hx).2⟩
  let f := fractional c a b
  let w (z : ZMod goldilocks) := quadraticChar _ ((1-γ*undo c a b z)*γ)
  have hi : Set.InjOn f (↑Z) := by
    intro x hx y hy he
    have hu := congrArg (undo c a b) he
    simpa only [f,undo_fractional hc hab (hreg x hx).2.2,
      undo_fractional hc hab (hreg y hy).2.2] using hu
  have hweight {x} (hx : x∈Z) : w (f x)=quadraticChar _ ((1-γ*x)*γ) := by
    simp [w,f,undo_fractional hc hab (hreg x hx).2.2]
  have hden {x} (hx : x∈Z) : 1-γ*x ≠ 0 := by
    intro he
    apply (hreg x hx).2.2
    apply (eq_div_iff hg).mpr
    linear_combination -he
  have hw (z) (hz : z∈Z.image f) : w z^4=1 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    rw [hweight hx]
    have hh₀ := quadraticChar_sq_one (mul_ne_zero (hden hx) hg)
    rw [show (4:ℕ)=2*2 by decide, pow_mul, hh₀, one_pow]
  have hd : Z.card≤2^29 := hsize ▸ card_le_card hsub
  have hbnd := goldilocks_rectangle Z H hH hd hsize hc ha hab hreg (fun x hx => hh x (hsub hx)) hh w hw
  let G x := ∑ y∈H, quadraticChar _ ((γ*x-1)*(γ*y)-t*(γ*x)+s)
  have hid (x) (hx : x∈Z) (y : ZMod goldilocks) :
      ((1-γ*x)*γ)*(f x-y)=(γ*x-1)*(γ*y)-t*(γ*x)+s := by
    have hfb : f x*(x-b)=c*(x-a) := div_mul_cancel₀ _ (sub_ne_zero.mpr (hreg x hx).2.2)
    have hlin : 1-γ*x = -γ*(x-b) := by dsimp [b]; field_simp; ring
    rw [hlin]
    calc
      _ = -γ^2*(f x*(x-b))+γ^2*(x-b)*y := by ring
      _ = _ := by rw [hfb]; dsimp [a,b,c]; field_simp; ring
  have hblock : ∑ x∈Z,G x=∑ z∈Z.image f,w z*∑ y∈H,quadraticChar _ (z-y) := by
    rw [sum_image hi]
    apply sum_congr rfl
    intro x hx
    rw [hweight hx, mul_sum]
    exact sum_congr rfl (fun y _ => by rw [← map_mul,hid x hx])
  rw [← hblock] at hbnd
  have hexc : H \ Z ⊆ {a,b} := by
    intro x hx
    by_contra hhx
    have hn := (mem_sdiff.mp hx).2
    apply hn
    apply mem_filter.mpr
    exact ⟨(mem_sdiff.mp hx).1, by simpa using hhx⟩
  have hcard : (H \ Z).card≤2 := (card_le_card hexc).trans_eq (card_pair hab)
  have hrow (x : ZMod goldilocks) : |G x| ≤ H.card := calc
    _ ≤ ∑ y∈H, |quadraticChar _ ((γ*x-1)*(γ*y)-t*(γ*x)+s)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _y∈H,(1:ℤ) := sum_le_sum (fun _ _ => abs_char_le_one _)
    _ = _ := by simp
  have herr : |∑ x∈H \ Z,G x|≤2*(H.card:ℤ) := calc
    _ ≤ ∑ x∈H \ Z,|G x| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _x∈H \ Z,(H.card:ℤ) := sum_le_sum (fun x _ => hrow x)
    _ ≤ _ := by simp; gcongr; exact_mod_cast hcard
  have he := sum_sdiff hsub (f:=G)
  change |∑ x∈H,G x| ≤ _
  rw [← he]
  rw [hsize] at herr
  norm_num at herr
  have ht₀ := abs_add_le (∑ x∈H \ Z,G x) (∑ x∈Z,G x)
  omega

end ProximityGap.PaleyMixedTraceSaving

#print axioms ProximityGap.PaleyMixedTraceSaving.occupancy

#print axioms ProximityGap.PaleyMixedTraceSaving.goldilocks_rectangle

#print axioms ProximityGap.PaleyMixedTraceSaving.goldilocks_parity
