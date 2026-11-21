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

end ProximityGap.PaleyMixedProductTraces

#print axioms ProximityGap.PaleyMixedProductTraces.common_summand_injective
#print axioms ProximityGap.PaleyMixedProductTraces.common_summand_character
#print axioms ProximityGap.PaleyMixedProductTraces.same_product_dilation
#print axioms ProximityGap.PaleyMixedProductTraces.doubled_ne_adjacent
#print axioms ProximityGap.PaleyMixedProductTraces.coset_kernel
#print axioms ProximityGap.PaleyMixedProductTraces.mixed_shift_mem_iff
#print axioms ProximityGap.PaleyMixedProductTraces.mixed_kernel
#print axioms ProximityGap.PaleyMixedProductTraces.swept_discrepancy
