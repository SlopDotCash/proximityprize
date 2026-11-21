/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg
import ArkLib.Research.ProximityGap.Frontier.PaleyInversionTrace
import ArkLib.Research.ProximityGap.Frontier.PaleyCosetCancellation

/-! # Quadratic discrepancy between different subgroup product strata

On each ratio diagonal a single shifted square character remains. The
nonzero additive Sidon property classifies which shifts belong to the original
subgroup. At a nonsquare generator, long unions of strata have small discrepancy
even when their two starting subsets are arbitrary.
-/
namespace ProximityGap.PaleyMixedProductTraces
open Finset PaleyInversionTrace PaleyCosetCancellation
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Every common-summand pair on two distinct products is a different ordered pair. -/
theorem common_summand_injective {s t : F} (hst : s ≠ t) :
    Set.InjOn (fun x => (productTrace s x, productTrace t x)) {x : F | x ≠ 0} := by
  intro x hx y hy heq
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj heq
  rcases (productTrace_eq_iff hx hy).mp h₁ with h|h
  · exact h
  rcases (productTrace_eq_iff hx hy).mp h₂ with hh|hh
  · exact hh
  · exact False.elim (hst (h.symm.trans hh))

/-- The signed character on the full common-summand matching. -/
theorem common_summand_character [Fintype F] (s t : F) {x : F} (hx : x ≠ 0) :
    quadraticChar F (productTrace s x-productTrace t x) =
      quadraticChar F (s-t)*quadraticChar F x := by
  have he : (productTrace s x-productTrace t x)*x=s-t := by
    unfold productTrace
    field_simp
    ring
  calc
    _ = quadraticChar F (productTrace s x-productTrace t x) * (quadraticChar F x)^2 := by
      rw [quadraticChar_sq_one hx, mul_one]
    _ = _ := by rw [pow_two, ← mul_assoc, ← map_mul, he]

/-- The remaining shift on the diagonal with second lift equal to `h*x`. -/
def diagonalShift (s t h : F) := (t/h-s)/(1-h)

omit [DecidableEq F] in
private theorem diagonal_relation {s t h : F} (h₀ : h ≠ 0) (h₁ : h ≠ 1) :
    t + diagonalShift s t h * h^2 = s*h + diagonalShift s t h*h := by
  unfold diagonalShift
  field_simp [sub_ne_zero.mpr h₁.symm]
  ring

/-- The stored subgroup character spectrum applies on a mixed diagonal only
when the two product parameters differ by the square of its ratio. -/
theorem mixed_shift_mem_iff (H : Finset F) (hsidon : SidonModNeg H)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a*b ∈ H) (hne : ∀ a ∈ H, a ≠ 0)
    {s t h : F} (hs : s ∈ H) (ht : t ∈ H) (hh : h ∈ H)
    (hneg : -s ∈ H) (hst : s ≠ t) (h₁ : h ≠ 1) :
    diagonalShift s t h ∈ H ↔ t=s*h^2 := by
  let c := diagonalShift s t h
  have hh₀ := hne h hh
  have he : t+c*h^2 = s*h+c*h := diagonal_relation hh₀ h₁
  constructor
  · intro hc
    change c ∈ H at hc
    have hc₂ : c*h^2 ∈ H := hmul _ hc _ (by simpa [pow_two] using hmul h hh h hh)
    rcases hsidon _ ht _ hc₂ _ (hmul s hs h hh) _ (hmul c hc h hh) he with hA|hB|hZ
    · have hvan : (c*h)*(h-1)=0 := by linear_combination hA.2
      exact False.elim (mul_ne_zero (mul_ne_zero (hne c hc) hh₀) (sub_ne_zero.mpr h₁) hvan)
    · apply False.elim
      apply hst
      apply mul_right_cancel₀ hh₀
      calc s*h = c*h^2 := hB.2.symm
           _ = (c*h)*h := by ring
           _ = t*h := by rw [hB.1]
    · have hroot : (c+s)*h = 0 := by linear_combination hZ-he
      have hcs := (mul_eq_zero.mp hroot).resolve_right hh₀
      linear_combination hZ - h^2*hcs
  · intro heq
    have hroot : (c+s)*(h*(h-1))=0 := by linear_combination he-heq
    have hcs := (mul_eq_zero.mp hroot).resolve_right (mul_ne_zero hh₀ (sub_ne_zero.mpr h₁))
    have hc : c = -s := by linear_combination hcs
    change c ∈ H
    rwa [hc]

omit [DecidableEq F] in
/-- The two subgroup summands of a nonzero sum determine its product. -/
theorem product_unique {H : Finset F} (hS : SidonModNeg H) {x y u v : F}
    (hx : x ∈ H) (hy : y ∈ H) (hu : u ∈ H) (hv : v ∈ H)
    (he : x+y=u+v) (h₀ : x+y ≠ 0) : x*y=u*v := by
  rcases hS _ hx _ hy _ hu _ hv he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|h
  · rfl
  · exact mul_comm ..
  · exact False.elim (h₀ h)

omit [DecidableEq F] in
/-- Two distinct values in the same nonzero product stratum and the same subgroup
coset are antipodal. -/
theorem same_product_dilation {H : Finset F} (hS : SidonModNeg H)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a*b ∈ H) {u x y z w : F}
    (hu : u ∈ H) (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H) (hw : w ∈ H)
    (hxy : x*y ≠ 0) (h₀ : z+w ≠ 0) (he : u*(x+y)=z+w) (hp : x*y=z*w) :
    u=1 ∨ u= -1 := by
  rw [mul_add] at he
  have hprod := product_unique hS (hmul u hu x hx) (hmul u hu y hy) hz hw he (he ▸ h₀)
  apply sq_eq_one_iff.mp
  apply mul_right_cancel₀ hxy
  rw [one_mul]
  linear_combination hprod-hp

omit [DecidableEq F] in
/-- The ratio-one and ratio-generator sections have disjoint output cosets
under the nonzero Sidon property. -/
theorem doubled_ne_adjacent {H : Finset F} (hS : SidonModNeg H)
    {g x y : F} (hx : x ∈ H) (hy : y ∈ H) (hgy : g*y ∈ H)
    (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) (h₂ : (2:F) ≠ 0) (hg : g ≠ 1) :
    2*x ≠ (1+g)*y := by
  intro h
  have he : x+x=y+g*y := by linear_combination h
  have hne : x+x ≠ 0 := by simpa only [← two_mul] using mul_ne_zero h₂ hx₀
  rcases hS _ hx _ hx _ hy _ hgy he with ⟨h₁,h₃⟩|⟨h₃,h₁⟩|hn
  · apply hg
    exact mul_right_cancel₀ hy₀ (by rw [one_mul, ← h₃, h₁])
  · apply hg
    exact mul_right_cancel₀ hy₀ (by rw [one_mul, ← h₃, h₁])
  · exact hne hn

/-- Any two multiplicative cosets yield a signed cyclic difference kernel. -/
theorem coset_kernel [Fintype F] (d y : F) {c x : F} (hc : c ≠ 0) (hx : x ≠ 0) :
    quadraticChar F (c*x-d*y) =
      quadraticChar F c * quadraticChar F x * quadraticChar F (1-(d/c)*(y/x)) := by
  rw [← map_mul, ← map_mul]
  congr 1
  field_simp

/-- A mixed diagonal reduces to a character row sampled at subgroup squares. -/
theorem mixed_kernel [Fintype F] (s t : F) {h x : F} (h₀ : h ≠ 0) (h₁ : h ≠ 1) (hx : x ≠ 0) :
    quadraticChar F (productTrace s x - productTrace t (h*x)) =
      quadraticChar F (1-h) * quadraticChar F x * quadraticChar F (x^2-diagonalShift s t h) := by
  have heq : (productTrace s x-productTrace t (h*x))*x=(1-h)*(x^2-diagonalShift s t h) := by
    unfold productTrace diagonalShift
    field_simp [sub_ne_zero.mpr h₁.symm]
    ring
  calc
    _ = quadraticChar F (productTrace s x-productTrace t (h*x)) * (quadraticChar F x)^2 := by
      rw [quadraticChar_sq_one hx, mul_one]
    _ = _ := by rw [pow_two, ← mul_assoc, ← map_mul, heq, map_mul]; ring

/-- Consecutive simultaneous dilations of any seed set. -/
def swept (u : F) (A : Finset F) (k : ℕ) : Finset F :=
  (range k).biUnion fun i => A.image (u^i * ·)

theorem swept_shiftLoss (u : F) (A : Finset F) (k : ℕ) :
    shiftLoss (swept u A k) u ≤ A.card := by
  apply card_le_card
  intro y hy
  obtain ⟨i, hi, a, ha, rfl⟩ := by
    simpa only [swept, mem_biUnion, mem_image, exists_and_left] using (mem_sdiff.mp hy).1
  cases i with
  | zero => simpa using ha
  | succ i =>
    exfalso
    apply (mem_sdiff.mp hy).2
    apply mem_image.mpr
    refine ⟨u^i*a, ?_, ?_⟩
    · apply mem_biUnion.mpr
      exact ⟨i, mem_range.mpr (Nat.lt_of_succ_lt (mem_range.mp hi)), mem_image.mpr ⟨a,ha,rfl⟩⟩
    · rw [pow_succ]; ring

/-- A bound for cross-stratum rectangles obtained by sweeping two independent seeds. -/
theorem swept_discrepancy [Fintype F] {u : F} (hu : quadraticChar F u = -1)
    (A B : Finset F) (k l : ℕ) :
    |∑ a ∈ swept u A k, ∑ b ∈ swept u B l, quadraticChar F (a-b)| ≤
      (A.card:ℤ)*(swept u B l).card + (B.card:ℤ)*(swept u A k).card := by
  apply (discrepancy_le_shiftLoss _ _ hu).trans
  gcongr
  · exact_mod_cast swept_shiftLoss u A k
  · exact_mod_cast swept_shiftLoss u B l

/-- The two directed difference sums obtained from reciprocal dilations have
opposite signs whenever minus the multiplier is a nonsquare. -/
theorem reciprocal_sums [Fintype F] (A : Finset F) {q : F}
    (hq : q ≠ 0) (hsign : quadraticChar F (-q) = -1) :
    (∑ x ∈ A, ∑ y ∈ A.image (q * ·), quadraticChar F (x-y)) =
      -(∑ x ∈ A, ∑ y ∈ A.image (q⁻¹ * ·), quadraticChar F (x-y)) := by
  simp_rw [sum_image (mul_right_injective₀ hq).injOn,
    sum_image (mul_right_injective₀ (inv_ne_zero hq)).injOn]
  rw [sum_comm]
  have hpair (x y : F) : quadraticChar F (y-q*x) = -quadraticChar F (x-q⁻¹*y) := by
    rw [show y-q*x = (-q)*(x-q⁻¹*y) by field_simp; ring, map_mul, hsign, neg_one_mul]
  simp_rw [hpair, sum_neg_distrib]

/-- Every nonzero sum of two subgroup elements with prescribed product. -/
def nonzeroStratum (H : Finset F) (s : F) : Finset F :=
  ((H ×ˢ H).filter (fun k => k.1*k.2=s ∧ k.1+k.2 ≠ 0)).image (fun k => k.1+k.2)

private theorem mem_nonzeroStratum {H : Finset F} {s z : F} :
    z ∈ nonzeroStratum H s ↔ ∃ x ∈ H, ∃ y ∈ H, x*y=s ∧ x+y≠0 ∧ x+y=z := by
  classical
  simp only [nonzeroStratum, mem_image, mem_filter, mem_product, Prod.exists]
  grind

/-- Distinct product strata are disjoint away from zero under the additive Sidon condition. -/
theorem disjoint_strata (H : Finset F) (hS : SidonModNeg H) {s t : F} (hst : s ≠ t) :
    Disjoint (nonzeroStratum H s) (nonzeroStratum H t) := by
  apply disjoint_left.mpr
  intro z hs ht
  obtain ⟨x,hx,y,hy,hxy,hn,he⟩ := mem_nonzeroStratum.mp hs
  obtain ⟨u,hu,v,hv,huv,_,hf⟩ := mem_nonzeroStratum.mp ht
  exact hst (hxy.symm.trans ((product_unique hS hx hy hu hv (he.trans hf.symm) hn).trans huv))

/-- Dilation acts on a product stratum by its square. -/
theorem scale_stratum (H : Finset F) {q : F} (hq : q≠0)
    (hf : ∀ x ∈ H, q*x ∈ H) (hb : ∀ x ∈ H, q⁻¹*x ∈ H) (s : F) :
    (nonzeroStratum H s).image (q * ·) = nonzeroStratum H (q^2*s) := by
  ext z
  constructor
  · intro he
    obtain ⟨_,ha,rfl⟩ := mem_image.mp he
    obtain ⟨x,hx,y,hy,hp,hn,rfl⟩ := mem_nonzeroStratum.mp ha
    exact mem_nonzeroStratum.mpr ⟨q*x,hf x hx,q*y,hf y hy,by rw [←hp]; ring,
      by rw [← mul_add]; exact mul_ne_zero hq hn, (mul_add ..).symm⟩
  · intro he
    obtain ⟨x,hx,y,hy,hp,hn,rfl⟩ := mem_nonzeroStratum.mp he
    refine mem_image.mpr ⟨q⁻¹*x+q⁻¹*y,mem_nonzeroStratum.mpr
      ⟨q⁻¹*x,hb x hx,q⁻¹*y,hb y hy,?_,?_,rfl⟩,?_⟩
    · calc q⁻¹*x*(q⁻¹*y) = q⁻¹^2*(x*y) := by ring
           _ = s := by rw [hp]; field_simp
    · rw [← mul_add]
      exact mul_ne_zero (inv_ne_zero hq) hn
    · rw [← mul_add, mul_inv_cancel_left₀ hq]

/-- A full nonzero stratum against its two reciprocal product strata has
zero discrepancy even when the multiplier fails to preserve the source. -/
theorem reciprocal_strata [Fintype F] (H : Finset F) (hS : SidonModNeg H)
    {q s : F} (hq : q≠0) (hsign : quadraticChar F (-q) = -1)
    (hf : ∀ x ∈ H, q*x ∈ H) (hb : ∀ x ∈ H, q⁻¹*x ∈ H) (hd : q^2*s ≠ q⁻¹^2*s) :
    ∑ x ∈ nonzeroStratum H s, ∑ y ∈ nonzeroStratum H (q^2*s) ∪ nonzeroStratum H (q⁻¹^2*s),
      quadraticChar F (x-y) = 0 := by
  have he := reciprocal_sums (nonzeroStratum H s) hq hsign
  rw [scale_stratum H hq hf hb, scale_stratum H (inv_ne_zero hq) hb (by simpa using hf)] at he
  simp_rw [sum_union (disjoint_strata H hS hd), sum_add_distrib]
  omega

#print axioms reciprocal_strata

section SecondPrime

open ArkLib.ProximityGap.PrizeShapePrimeP30Second

local instance : Fact P.Prime := ⟨prime_P⟩

/-- The order-`2^30` subgroup of the second named prime. -/
def secondDomain : Finset (ZMod P) := univ.filter (fun x => x^(2^30 : ℕ)=1)

/-- On the actual second prime the only externally enumerated premise is
uniqueness of nonzero pair sums. Every odd generator power gives a distinct
pair of target strata and exact signed cancellation on their union. -/
theorem second_reciprocal_strata (hS : SidonModNeg secondDomain) {s : ZMod P} (hs : s ≠ 0) (k : ℕ) :
    let q := g^(2*k+1)
    ∑ x ∈ nonzeroStratum secondDomain s,
      ∑ y ∈ nonzeroStratum secondDomain (q^2*s) ∪ nonzeroStratum secondDomain (q⁻¹^2*s),
        quadraticChar (ZMod P) (x-y) = 0 := by
  let q := g^(2*k+1)
  have hg : g ≠ 0 := by intro he; simpa [he] using second_generator_character
  have hq : q ≠ 0 := pow_ne_zero _ hg
  have hminus : quadraticChar (ZMod P) (-1) = 1 := by
    apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    rw [FiniteField.isSquare_neg_one_iff,ZMod.card]
    decide
  have hqchar : quadraticChar (ZMod P) (-q) = -1 := by
    rw [← neg_one_mul, map_mul, hminus, one_mul, show q=g^(2*k+1) from rfl,
      map_pow,second_generator_character, pow_succ, pow_mul]
    norm_num
  have hgN : g^(2^30 : ℕ) = 1 := by rw [← orderOf_g, pow_orderOf_eq_one]
  have hqN : q^(2^30 : ℕ) = 1 := by
    change (g^(2*k+1))^(2^30 : ℕ)=1
    rw [← pow_mul, Nat.mul_comm, pow_mul, hgN, one_pow]
  have hd : q^2*s ≠ q⁻¹^2*s := by
    intro he
    have heq := mul_right_cancel₀ hs he
    have h₄ : q^4 = 1 := by
      field_simp [hq] at heq
      linear_combination heq
    change (g^(2*k+1))^4=1 at h₄
    rw [←pow_mul] at h₄
    have hdvd := orderOf_dvd_of_pow_eq_one h₄
    rw [orderOf_g] at hdvd
    omega
  apply reciprocal_strata secondDomain hS hq hqchar _ _ hd
  · intro x hx
    simpa only [secondDomain,mem_filter,mem_univ,true_and,mul_pow,hqN,one_mul] using hx
  · intro x hx
    simpa only [secondDomain,mem_filter,mem_univ,true_and,mul_pow,inv_pow,hqN,inv_one,one_mul] using hx

#print axioms second_reciprocal_strata

end SecondPrime

end ProximityGap.PaleyMixedProductTraces

#print axioms ProximityGap.PaleyMixedProductTraces.common_summand_injective
#print axioms ProximityGap.PaleyMixedProductTraces.common_summand_character
#print axioms ProximityGap.PaleyMixedProductTraces.same_product_dilation
#print axioms ProximityGap.PaleyMixedProductTraces.doubled_ne_adjacent
#print axioms ProximityGap.PaleyMixedProductTraces.coset_kernel
#print axioms ProximityGap.PaleyMixedProductTraces.mixed_shift_mem_iff
#print axioms ProximityGap.PaleyMixedProductTraces.mixed_kernel
#print axioms ProximityGap.PaleyMixedProductTraces.swept_discrepancy
