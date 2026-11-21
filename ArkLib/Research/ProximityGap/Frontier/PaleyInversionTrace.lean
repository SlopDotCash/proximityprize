/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Quadratic character on the inversion quotient

The trace coordinate identifies inverse pairs in the multiplicative group.
Its difference kernel factors into one relative and one product coordinate.
-/
namespace ProximityGap.PaleyInversionTrace
open Finset
variable {F : Type*} [Field F]

/-- Equal-product pairs of subgroup elements project to this sum coordinate. -/
def productTrace (s x : F) := x + s/x

theorem productTrace_eq_iff {s x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    productTrace s x = productTrace s y ↔ x = y ∨ x*y = s := by
  have hid : (productTrace s x - productTrace s y)*(x*y) = (x-y)*(x*y-s) := by
    unfold productTrace
    field_simp
    ring
  rw [← sub_eq_zero, ← mul_left_inj' (mul_ne_zero hx hy), zero_mul, hid,
    mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The coordinate on the quotient by inversion. -/
def traceCoord (x : F) := x + x⁻¹

theorem traceCoord_eq_iff {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    traceCoord x = traceCoord y ↔ x = y ∨ x*y = 1 := by
  simpa [productTrace, traceCoord] using (productTrace_eq_iff (s := (1:F)) hx hy)

variable [Fintype F] [DecidableEq F]

/-- The quadratic difference kernel factors on every product stratum. -/
theorem product_kernel (s : F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    quadraticChar F (productTrace s x - productTrace s y) =
      quadraticChar F x * quadraticChar F (x/y-1) * quadraticChar F (x*y-s) := by
  have hid : (productTrace s x - productTrace s y)*x=(x/y-1)*(x*y-s) := by
    unfold productTrace
    field_simp
    ring
  calc
    _ = quadraticChar F (productTrace s x - productTrace s y) * (quadraticChar F x)^2 := by
      rw [quadraticChar_sq_one hx, mul_one]
    _ = _ := by rw [pow_two, ← mul_assoc, ← map_mul, hid, map_mul]; ring

/-- The factorization holds at the two colliding coordinates as well. -/
theorem kernel {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    quadraticChar F (traceCoord x - traceCoord y) =
      quadraticChar F x * quadraticChar F (x/y-1) * quadraticChar F (x*y-1) := by
  simpa [productTrace, traceCoord] using product_kernel (1:F) hx hy

/-- The exceptional trace at a self-inverse unit loses exactly one sign. -/
theorem kernel_at_fixed {x e : F} (hx : x ≠ 0) (he : e^2=1) :
    quadraticChar F (traceCoord x - traceCoord e) =
      if x=e then 0 else quadraticChar F x := by
  have he₀ : e ≠ 0 := by intro h; simp [h] at he
  have hei : e⁻¹=e := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using he)
  by_cases h : x=e
  · simp [h]
  simp only [h, ↓reduceIte]
  have hnum : (traceCoord x - traceCoord e)*x=(x-e)^2 := by
    unfold traceCoord
    rw [hei]
    rw [sub_mul, add_mul, inv_mul_cancel₀ hx, ← he]
    ring
  calc
    _ = quadraticChar F (traceCoord x - traceCoord e) * (quadraticChar F x)^2 := by
      rw [quadraticChar_sq_one hx, mul_one]
    _ = _ := by
      rw [pow_two, ← mul_assoc, ← map_mul, hnum, quadraticChar_sq_one' (sub_ne_zero.mpr h), one_mul]

omit [Fintype F] in
/-- The two lifts of a trace in an inverse-closed set, including coincident lifts. -/
theorem trace_fiber (A : Finset F) (h₀ : ∀ x ∈ A, x ≠ 0)
    (hinv : ∀ x ∈ A, x⁻¹ ∈ A) {x : F} (hx : x ∈ A) :
    A.filter (fun y => traceCoord y = traceCoord x) = {x, x⁻¹} := by
  ext y
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hy, h⟩
    rcases (traceCoord_eq_iff (h₀ y hy) (h₀ x hx)).mp h with rfl | h₁
    · exact Or.inl rfl
    · exact Or.inr (eq_inv_of_mul_eq_one_left h₁)
  · rintro (rfl | rfl)
    · exact ⟨hx, rfl⟩
    · exact ⟨hinv x hx, by simp [traceCoord, add_comm]⟩

omit [Fintype F] in
/-- A trace in the branch locus has one lift. Every other trace has two lifts. -/
theorem weighted_trace (A : Finset F) (h₀ : ∀ x ∈ A, x ≠ 0)
    (hinv : ∀ x ∈ A, x⁻¹ ∈ A) (f : F → ℤ) :
    ∑ x ∈ A, f (traceCoord x) =
      ∑ t ∈ A.image traceCoord, (if t=2 ∨ t= -2 then (1:ℤ) else 2)*f t := by
  classical
  rw [← sum_fiberwise_of_maps_to (fun _ => mem_image_of_mem traceCoord)
    (fun x => f (traceCoord x))]
  apply sum_congr rfl
  intro t ht
  obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
  have hc : (traceCoord x = 2 ∨ traceCoord x = -2) ↔ x=x⁻¹ := by
    have hpos : traceCoord (1:F) = 2 := by simp [traceCoord]; ring
    have hneg : traceCoord (-1:F) = -2 := by simp [traceCoord]; ring
    rw [← hneg, ← hpos, traceCoord_eq_iff (h₀ _ hx) one_ne_zero,
      traceCoord_eq_iff (h₀ _ hx) (neg_ne_zero.mpr one_ne_zero)]
    simp only [mul_one, or_self, mul_neg, neg_eq_iff_eq_neg]
    constructor
    · rintro (rfl | rfl) <;> simp
    · intro h
      exact sq_eq_one_iff.mp (by rw [pow_two, ← inv_mul_cancel₀ (h₀ _ hx), ← h])
  calc
    _ = ∑ _y ∈ A.filter (fun y => traceCoord y = traceCoord x), f (traceCoord x) := by
      apply sum_congr rfl
      intro y hy
      rw [(mem_filter.mp hy).2]
    _ = _ := by
      rw [trace_fiber A h₀ hinv hx]
      simp only [hc]
      by_cases h : x=x⁻¹
      · simp [← h]
      · simp [h, two_mul]

section Cyclic
variable {m : ℕ} [NeZero m]
local notation "C" => ZMod (2*m)

private theorem double_zero (x : C) (hx : x+x=0) : x=0 ∨ x=(m:C) := by
  have hd : 2*m ∣ 2*x.val := (ZMod.natCast_eq_zero_iff _ _).mp (by
    simp only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    exact (two_mul x).trans hx)
  have hm := Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2) hd
  rw [← ZMod.natCast_zmod_val x]
  by_cases h : x.val=0
  · left; simp [h]
  · right; rw [Nat.eq_of_dvd_of_lt_two_mul h hm x.val_lt]

private theorem same_parity (x y : C) : (x-y).val%2=(x+y).val%2 := by
  let π := ZMod.castHom (dvd_mul_right 2 m) (ZMod 2)
  have hp (r : C) : (π r).val = r.val % 2 := calc
    _ = (π (r.val:C)).val := by rw [ZMod.natCast_zmod_val]
    _ = _ := by rw [map_natCast, ZMod.val_natCast]
  rw [← hp, ← hp, map_sub, map_add, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

/-- In sum and difference coordinates, each pair of like parity has two lifts.
This transports arbitrary coefficient functions, including Fourier characters. -/
theorem sum_difference_pushforward {R : Type*} [AddCommMonoid R] (f : C × C → R) :
    ∑ z : C × C, f (z.1-z.2,z.1+z.2) =
      ∑ w : C × C, if w.1.val%2=w.2.val%2 then f w + f w else 0 := by
  classical
  let L (z : C × C) := (z.1-z.2,z.1+z.2)
  change ∑ z, f (L z) = _
  rw [← sum_fiberwise_of_maps_to' (t := univ) (fun _ _ => mem_univ _) f]
  apply sum_congr rfl
  rintro ⟨r,s⟩ _
  by_cases h : r.val%2=s.val%2
  · simp only [h, ↓reduceIte]
    let a : C := ((r.val+s.val)/2 : ℕ)
    have hsum : a+a=r+s := calc
      _ = (((r.val+s.val)/2 + (r.val+s.val)/2:ℕ):C) := by push_cast; rfl
      _ = ((r.val+s.val:ℕ):C) := by congr 1; omega
      _ = _ := by push_cast; simp only [ZMod.natCast_zmod_val]
    have hm : (m:C)+(m:C)=0 := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, two_mul] using ZMod.natCast_self (2*m)
    have hn : (m:C) ≠ 0 := by
      intro H
      have he := (ZMod.natCast_eq_zero_iff _ _).mp H
      have hpos := NeZero.pos m
      have hmn := Nat.le_of_dvd hpos he
      omega
    have hf : (univ.filter (fun z => L z=(r,s))) =
        {(a,a-r), (a+m,a+m-r)} := by
      ext ⟨x,y⟩
      simp only [mem_filter, mem_univ, true_and, L, Prod.mk.injEq, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h₁,h₂⟩
        have hd : (x-a)+(x-a)=0 := by linear_combination h₁+h₂-hsum
        rcases double_zero (x-a) hd with h₃ | h₃
        · left; constructor <;> first | linear_combination h₃ | linear_combination h₃-h₁
        · right; constructor <;> first | linear_combination h₃ | linear_combination h₃-h₁
      · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> constructor
        · ring
        · linear_combination hsum
        · ring
        · linear_combination hsum+hm
    rw [hf, sum_pair]
    intro he
    have h₁ := congrArg Prod.fst he
    change a=a+(m:C) at h₁
    exact hn (by simpa using h₁.symm)
  · simp only [h, ↓reduceIte]
    have hf : (univ.filter (fun z => L z=(r,s))) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨x,y⟩ hz
      have he := (mem_filter.mp hz).2
      change (x-y,x+y)=(r,s) at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact h (same_parity x y)
    rw [hf, sum_empty]
end Cyclic

end ProximityGap.PaleyInversionTrace

#print axioms ProximityGap.PaleyInversionTrace.sum_difference_pushforward
#print axioms ProximityGap.PaleyInversionTrace.product_kernel
#print axioms ProximityGap.PaleyInversionTrace.weighted_trace
#print axioms ProximityGap.PaleyInversionTrace.traceCoord_eq_iff
#print axioms ProximityGap.PaleyInversionTrace.kernel
#print axioms ProximityGap.PaleyInversionTrace.kernel_at_fixed
