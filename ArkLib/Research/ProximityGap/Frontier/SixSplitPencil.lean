/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # Fifteen fully split pair differences from thirteen dyadic fibers

The affine functions vᵢ − uᵢY have slopes ωʳ at their intersections, where ω is
any primitive 16th root. Three share the ninth fiber. Every other pair occupies
a distinct fiber. These are identities in the residue field, independent of its order.
-/

namespace ProximityGap.SixSplitPencil

variable {F : Type*} [Field F]

private def tailSum (z : F) := z+z^2+z^3+z^4+z^5+z^6+z^7

/-- Abscissas of six points in the coefficient plane. -/
def u (z : F) : Fin 6 → F :=
  ![0, 2, 2*(1-z^7), 2*(1-z^5-z^6-z^7), 1-tailSum z, -2*tailSum z]

/-- Ordinates of the same six points. -/
def v (z : F) : Fin 6 → F :=
  ![0, 2, 2*(1+z), 2*(1+z+z^2+z^3), 1+tailSum z, 2*tailSum z]

/-- Exponents of pairwise secants. The diagonal entries are unused. -/
def fiber : Fin 6 → Fin 6 → Fin 16 :=
  ![![0,0,1,3,7,8], ![0,0,2,4,9,9], ![1,2,0,5,11,10],
    ![3,4,5,0,15,12], ![7,9,11,15,0,9], ![8,9,10,12,9,0]]

private theorem half_power {z : F} (hz : IsPrimitiveRoot z 16) : z^8 = -1 := by
  apply (sq_eq_one_iff.mp (by simpa only [← pow_mul] using hz.pow_eq_one)).resolve_left
  intro he
  have := hz.pow_inj (i := 8) (j := 0) (by decide) (by decide) (by simpa using he)
  omega

/-- Cross multiplication gives the prescribed secant on all fifteen pairs. -/
theorem secants {z : F} (hz : IsPrimitiveRoot z 16) (i j : Fin 6) :
    v z i - v z j = (u z i-u z j)*z^(fiber i j).val := by
  have he := half_power hz
  fin_cases i <;> fin_cases j <;> norm_num [u, v, fiber, tailSum] <;> grind (splits := 0)

private theorem two_ne {z : F} (hz : IsPrimitiveRoot z 16) : (2 : F) ≠ 0 := by
  have h := hz.pow_inj (i := 8) (j := 0) (by decide) (by decide)
  intro he
  apply (by decide : (8 : ℕ) ≠ 0)
  apply h
  rw [half_power hz, pow_zero]
  linear_combination - he

private theorem u_ne_zero {z : F} (hz : IsPrimitiveRoot z 16) {i : Fin 6} (hi : i ≠ 0) :
    u z i ≠ 0 := by
  intro hh
  have h0 := secants hz i 0
  rw [show u z 0 = 0 from rfl, show v z 0 = 0 from rfl, hh, sub_zero, sub_zero, zero_mul] at h0
  by_cases h : i = 1
  · subst i
    exact two_ne hz (by simpa [u] using hh)
  have h1 := secants hz i 1
  have hu1 : u z 1 = 2 := rfl
  have hv1 : v z 1 = 2 := rfl
  rw [hh, hu1, hv1] at h1
  rw [h0, zero_sub] at h1
  have hp : z^(fiber i 1).val = 1 := by
    apply (mul_left_cancel₀ (neg_ne_zero.mpr (two_ne hz)) : (-2 : F)*_ = (-2 : F)*_ → _)
    simpa only [mul_one] using h1.symm
  have he := hz.pow_inj (i := (fiber i 1).val) (j := 0) (fiber i 1).isLt
    (by decide) (by simpa using hp)
  exact (by decide : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → (fiber i 1).val ≠ 0) i hi h he

/-- The six abscissas are distinct in every field containing a primitive 16th root. -/
theorem u_injective {z : F} (hz : IsPrimitiveRoot z 16) : Function.Injective (u z) := by
  intro i j hh
  by_cases hi : i = 0
  · subst i
    exact (by_contra fun hj => u_ne_zero hz (Ne.symm hj) (hh.symm.trans rfl))
  by_cases hj : j = 0
  · subst j
    exact False.elim (u_ne_zero hz hi (hh.trans rfl))
  have hv := secants hz i j
  rw [hh, sub_self, zero_mul, sub_eq_zero] at hv
  have h0i := secants hz i 0
  have h0j := secants hz j 0
  have hu0 : u z 0 = 0 := rfl
  have hv0 : v z 0 = 0 := rfl
  simp only [hv0, hu0, sub_zero] at h0i h0j
  have hc := (h0i.symm.trans hv).trans h0j
  rw [hh] at hc
  have hpow := mul_left_cancel₀ (u_ne_zero hz hj) hc
  have he := hz.pow_inj (fiber i 0).isLt (fiber j 0).isLt hpow
  exact (by decide : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 →
    (fiber i 0).val = (fiber j 0).val → i = j) i j hi hj he

/-- Equality of affine heads is exactly membership in the prescribed root fiber. -/
theorem agree_iff {z : F} (hz : IsPrimitiveRoot z 16) {i j : Fin 6} (hij : i ≠ j) (Y : F) :
    v z i - u z i*Y = v z j - u z j*Y ↔ Y = z^(fiber i j).val := by
  have hc := secants hz i j
  have hx := sub_ne_zero.mpr ((u_injective hz).ne hij)
  constructor
  · intro h
    apply mul_left_cancel₀ hx
    linear_combination -h + hc
  · intro h
    rw [h]
    linear_combination hc

#print axioms secants
#print axioms agree_iff

end ProximityGap.SixSplitPencil
