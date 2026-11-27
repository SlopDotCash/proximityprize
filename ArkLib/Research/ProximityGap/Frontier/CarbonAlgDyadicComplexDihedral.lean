/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFourPairGeometry

/-! # All-orders dyadic involution rigidity in characteristic zero

`docs/research/proximity-gap/dyadic-involution-pairs.md` states that a projective involution
`x ↦ (a x + b)/(c x - a)` exchanging four disjoint pairs of roots of unity of order dividing
`2^m` is either the negation `x ↦ -x` (`c = b = 0`) or a reciprocal map `x ↦ t / x` (`a = 0`),
and describes the complex all-orders argument as written mathematics.

The ingredients are already kernel-checked: `DyadicSevenProjectivities.all_orders` (seven
matched dyadic roots force a scaling or reciprocal scaling, at every order) and
`DyadicFourPairGeometry.pattern`. This module packages them into the characteristic-zero
statement at every order `2^m`, with no field-size or height hypothesis.
-/

set_option autoImplicit false

namespace ProximityGap.CarbonAlgDyadicComplexDihedral

open DyadicFourPairGeometry DyadicPairMinorTransfer

/-- Two trace-zero relations together with an equal-product or doubly-antipodal shape force
the dihedral form. -/
theorem recover {K : Type*} [Field K] {u v x y a b c : K}
    (ux : u ≠ x) (uy : u ≠ y) (p₀ : c*u*v-a*(u+v) = b) (p₁ : c*x*y-a*(x+y) = b)
    (shape : u*v = x*y ∨ (u+v = 0 ∧ x+y = 0)) : a = 0 ∨ c = 0 ∧ b = 0 := by
  have different (hp : u*v = x*y) (hs : u+v = x+y) : False :=
    mul_ne_zero (sub_ne_zero.mpr ux) (sub_ne_zero.mpr uy) (by linear_combination u*hs-hp)
  rcases shape with hp | ⟨s₀, s₁⟩
  · left
    have z : a*(u+v-(x+y)) = 0 := by linear_combination p₁-p₀+c*hp
    exact (mul_eq_zero.mp z).resolve_right (sub_ne_zero.mpr (different hp))
  · right
    have hp : u*v ≠ x*y := fun eq => different eq (s₀.trans s₁.symm)
    have z : c*(u*v-x*y) = 0 := by linear_combination p₀-p₁+a*s₀-a*s₁
    have hc := (mul_eq_zero.mp z).resolve_right (sub_ne_zero.mpr hp)
    exact ⟨hc, by simpa [hc, s₀] using p₀.symm⟩

/-- **All-orders dyadic involution rigidity (characteristic zero).** In any field of
characteristic zero, a nonsingular trace-zero projectivity `x ↦ (a x + b)/(c x - a)` that
exchanges four disjoint pairs of roots of unity of order dividing `2^m` is a reciprocal map
(`a = 0`) or the negation (`c = 0 ∧ b = 0`). The pairs are given by exponents `q (i, j)` of a
primitive `2^m`-th root `w`; there is no restriction on `m`. -/
theorem dihedral_of_charZero {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] {m : ℕ} {w : K}
    (hw : IsPrimitiveRoot w (2^m)) (q : Fin 4 × Fin 2 ↪ Fin (2^m)) (a b c : K)
    (det : a^2+b*c ≠ 0)
    (law : ∀ i, c*w^(q (i,0)).val*w^(q (i,1)).val - a*(w^(q (i,0)).val+w^(q (i,1)).val) = b) :
    a = 0 ∨ c = 0 ∧ b = 0 := by
  have inj : Function.Injective (fun i : Fin 4 × Fin 2 => w^(q i).val) := fun i j h =>
    q.injective (Fin.ext (hw.pow_inj (q i).isLt (q j).isLt h))
  have ux : w^(q (0,0)).val ≠ w^(q (1,0)).val := inj.ne (by decide)
  have uy : w^(q (0,0)).val ≠ w^(q (1,1)).val := inj.ne (by decide)
  have rel (i : Fin 4) : minor (w^(q (0,0)).val) (w^(q (0,1)).val) (w^(q (1,0)).val)
      (w^(q (1,1)).val) (w^(q (i,0)).val) (w^(q (i,1)).val) = 0 :=
    incident det (law 0) (law 1) (law i)
  have shape := pattern hw (DyadicSevenProjectivities.all_orders hw) q rel
  exact recover ux uy (law 0) (law 1) shape

/-- The complex specialization: every projective involution exchanging four disjoint pairs of
`2^m`-th roots of unity in `ℂ` is dihedral, for every `m`. -/
theorem complex_dihedral {m : ℕ} {w : ℂ} (hw : IsPrimitiveRoot w (2^m))
    (q : Fin 4 × Fin 2 ↪ Fin (2^m)) (a b c : ℂ) (det : a^2+b*c ≠ 0)
    (law : ∀ i, c*w^(q (i,0)).val*w^(q (i,1)).val - a*(w^(q (i,0)).val+w^(q (i,1)).val) = b) :
    a = 0 ∨ c = 0 ∧ b = 0 :=
  dihedral_of_charZero hw q a b c det law

end ProximityGap.CarbonAlgDyadicComplexDihedral

#print axioms ProximityGap.CarbonAlgDyadicComplexDihedral.dihedral_of_charZero
#print axioms ProximityGap.CarbonAlgDyadicComplexDihedral.complex_dihedral
