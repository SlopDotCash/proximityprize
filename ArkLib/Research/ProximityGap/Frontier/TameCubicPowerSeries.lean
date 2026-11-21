/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic

/-! # Splitting cubic equations by tame power substitution

A unit power series has a tame root by Hensel lifting. Consequently an
arbitrary series acquires an nth root after the substitution X ↦ Xⁿ.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped PowerSeries

namespace ArkLib.ProximityGap.Frontier.TameCubicPowerSeries

variable {K : Type*} [Field K] [IsSepClosed K]

/-- Hensel lifting gives arbitrary tame roots of units of K[[X]]. -/
theorem unit_has_tame_root (u : K⟦X⟧) (hu : IsUnit u) {n : ℕ} (hn : (n : K) ≠ 0) :
    ∃ y : K⟦X⟧, y^n = u := by
  let I : Ideal K⟦X⟧ := Ideal.span {PowerSeries.X}
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  let _ : NeZero (n : K) := ⟨hn⟩
  obtain ⟨b,hb⟩ := IsSepClosed.exists_pow_nat_eq (PowerSeries.constantCoeff u) n
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hb
    exact (PowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero hb.symm
  let f : K⟦X⟧[X] := X^n-C u
  have hmem : f.eval (PowerSeries.C b) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [f, hb]
  have hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval (PowerSeries.C b))) := by
    apply IsUnit.map
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [f, Polynomial.derivative_X_pow, hn, hb0]
  obtain ⟨y,hy,_⟩ := HenselianRing.is_henselian f (monic_X_pow_sub_C u hn0) (PowerSeries.C b) hmem hder
  exact ⟨y, sub_eq_zero.mp (by simpa [f, Polynomial.IsRoot] using hy)⟩

/-- Every power series acquires a literal nth root after multiplying the
coordinate exponents by n, provided n is invertible in the coefficient field. -/
theorem expanded_has_tame_root (f : K⟦X⟧) {n : ℕ} (hn : (n : K) ≠ 0) (hn0 : n ≠ 0) :
    ∃ y : K⟦X⟧, y^n = PowerSeries.expand n hn0 f := by
  by_cases h : f = 0
  · exact ⟨0, by simp [h, hn0]⟩
  obtain ⟨b,hb⟩ := unit_has_tame_root (PowerSeries.expand n hn0 f.divXPowOrder)
    ((PowerSeries.isUnit_divided_by_X_pow_order h).map _) hn
  refine ⟨PowerSeries.X ^ f.order.toNat * b, ?_⟩
  rw [mul_pow, hb, ← pow_mul, Nat.mul_comm f.order.toNat, pow_mul, ← PowerSeries.expand_X n hn0,
    ← map_pow, ← map_mul, PowerSeries.X_pow_order_mul_divXPowOrder]

/-- Cardano's two cube roots may be aligned in the tame power series
ring, including when one of them is zero. -/
theorem cardano_data (p q : K⟦X⟧) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (ζ : K⟦X⟧) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ a b : K⟦X⟧, a*b = PowerSeries.expand 6 (by decide) p ∧
      a^3+b^3 = 2*PowerSeries.expand 6 (by decide) q := by
  let e₂ := PowerSeries.expand 2 (by decide) (R := K)
  let e₃ := PowerSeries.expand 3 (by decide) (R := K)
  let e₆ := PowerSeries.expand 6 (by decide) (R := K)
  have he (w : K⟦X⟧) : e₃ (e₂ w) = e₆ w :=
    (PowerSeries.expand_mul 3 (by decide) 2 (by decide) w).symm
  obtain ⟨s,hs⟩ := expanded_has_tame_root (q^2-p^3) (n := 2) h₂ (by decide)
  change s^2 = e₂ (q^2-p^3) at hs
  obtain ⟨a,ha⟩ := expanded_has_tame_root (e₂ q+s) (n := 3) h₃ (by decide)
  obtain ⟨b,hb⟩ := expanded_has_tame_root (e₂ q-s) (n := 3) h₃ (by decide)
  change a^3 = e₃ (e₂ q+s) at ha
  change b^3 = e₃ (e₂ q-s) at hb
  rw [map_add, he] at ha
  rw [map_sub, he] at hb
  have hs' : (e₃ s)^2 = (e₆ q)^2-(e₆ p)^3 := by
    rw [← map_pow, hs, he, map_sub, map_pow, map_pow]
  have hp : e₆ p ∈ nthRoots 3 ((a*b)^3) := by
    apply (mem_nthRoots (by decide : 0 < 3)).mpr
    rw [mul_pow, ha, hb]
    linear_combination hs'
  rw [hζ.nthRoots_eq (α := a*b) rfl] at hp
  obtain ⟨j,_,hj⟩ := Multiset.mem_map.mp hp
  have hz : (ζ^j)^3 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨a, ζ^j*b, ?_, ?_⟩
  · change a*(ζ^j*b) = e₆ p
    rw [← hj]
    ring
  · change a^3+(ζ^j*b)^3 = 2*e₆ q
    rw [mul_pow, hz, one_mul, ha, hb]
    ring

/-- Polynomial form of the three-root identity. It holds over any
commutative coefficient ring for a primitive cubic phase. -/
theorem cardano_identity {R : Type*} [CommRing R] (a b z x : R) (hz : z^2+z+1=0) :
    (x-(a+b))*(x-(z*a+z^2*b))*(x-(z^2*a+z*b)) =
      x^3-3*(a*b)*x-(a^3+b^3) := by
  have hz3 : z^3 = 1 := by linear_combination (z-1)*hz
  have hz4 : z^4 = z := by rw [show 4=3+1 by decide, pow_succ, hz3, one_mul]
  have hsum : (z*a+z^2*b)+(z^2*a+z*b) = -(a+b) := by
    linear_combination (a+b)*hz
  have hprod : (z*a+z^2*b)*(z^2*a+z*b) = a^2+b^2-a*b := by
    calc
      _ = z^3*(a^2+b^2)+(z^4+z^2)*a*b := by ring
      _ = _ := by rw [hz3,hz4]; linear_combination a*b*hz
  calc
    _ = (x-(a+b))*(x^2-((z*a+z^2*b)+(z^2*a+z*b))*x+(z*a+z^2*b)*(z^2*a+z*b)) := by ring
    _ = _ := by rw [hsum,hprod]; ring

/-- The normalized cubic splits into three polynomial linear factors over
K[[t]] after X = t⁶, with no nonsingularity assumption on its special fiber. -/
theorem depressed_cubic_split (p q : K⟦X⟧) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) :
    let e := PowerSeries.expand 6 (by decide) (R := K)
    ∃ x y z : K⟦X⟧, X^3-C (3*e p)*X-C (2*e q) =
      (X-C x)*(X-C y)*(X-C z) := by
  let e := PowerSeries.expand 6 (by decide) (R := K)
  let _ : NeZero ((3 : ℕ) : K) := ⟨h₃⟩
  obtain ⟨ξ,hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K 3
  let ζ : K⟦X⟧ := PowerSeries.C ξ
  have hζ : IsPrimitiveRoot ζ 3 := hξ.map_of_injective (f := PowerSeries.C) PowerSeries.C_injective
  have hz : ζ^2+ζ+1=0 := by
    have hs := hζ.geom_sum_eq_zero (by decide : 1 < 3)
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using hs
  obtain ⟨a,b,hab,hs⟩ := cardano_data p q h₂ h₃ ζ hζ
  refine ⟨a+b,ζ*a+ζ^2*b,ζ^2*a+ζ*b,?_⟩
  have h := cardano_identity (C a) (C b) (C ζ) (X : K⟦X⟧[X])
    (by simpa only [map_add, map_pow, map_one, map_zero] using congrArg (C (R := K⟦X⟧)) hz)
  rw [← hab, ← hs]
  simpa only [map_add, map_mul, map_pow, map_ofNat, mul_assoc] using h.symm

/-- All monic cubic equations split into three linear factors over the
sixth-root coordinate ring. This applies equally at a multiple special root. -/
theorem monic_cubic_split (A B D : K⟦X⟧) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) :
    let e := PowerSeries.expand 6 (by decide) (R := K)
    ∃ x y z : K⟦X⟧, X^3+C (e A)*X^2+C (e B)*X+C (e D) =
      (X-C x)*(X-C y)*(X-C z) := by
  let e := PowerSeries.expand 6 (by decide) (R := K)
  let j : K⟦X⟧ := PowerSeries.C ((3 : K)⁻¹)
  let l : K⟦X⟧ := PowerSeries.C ((2 : K)⁻¹)
  have hj : 3*j = 1 := by
    simpa only [j, map_mul, map_one, map_ofNat] using congrArg (PowerSeries.C (R := K)) (mul_inv_cancel₀ h₃)
  have hl : 2*l = 1 := by
    simpa only [l, map_mul, map_one, map_ofNat] using congrArg (PowerSeries.C (R := K)) (mul_inv_cancel₀ h₂)
  let h := j*A
  let p := h^2-j*B
  let q := l*(B*h-D)-h^3
  have hA : e A = 3*e h := by
    have hh : A = 3*h := by dsimp [h]; linear_combination -A*hj
    simpa only [map_mul, map_ofNat] using congrArg e hh
  have hp : 3*e p = 3*(e h)^2-e B := by
    have hh : 3*p = 3*h^2-B := by dsimp [p]; linear_combination -B*hj
    simpa only [map_pow, map_sub, map_mul, map_ofNat] using congrArg e hh
  have hq : 2*e q = e B*e h-e D-2*(e h)^3 := by
    have hh : 2*q = B*h-D-2*h^3 := by dsimp [q]; linear_combination (B*h-D)*hl
    simpa only [map_pow, map_sub, map_mul, map_ofNat] using congrArg e hh
  obtain ⟨x,y,z,hs⟩ := depressed_cubic_split p q h₂ h₃
  refine ⟨x-e h,y-e h,z-e h,?_⟩
  have hs' := congrArg (fun f : K⟦X⟧[X] => f.comp (X+C (e h))) hs
  simp only [sub_comp, mul_comp, pow_comp, X_comp, C_comp] at hs'
  change X^3+C (e A)*X^2+C (e B)*X+C (e D) = _
  calc
    _ = (X+C (e h))^3-C (3*e p)*(X+C (e h))-C (2*e q) := by
      rw [hA,hp,hq]
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    _ = _ := by
      rw [hs']
      simp only [map_sub]
      ring

#print axioms monic_cubic_split
#print axioms depressed_cubic_split
#print axioms unit_has_tame_root
#print axioms expanded_has_tame_root

end ArkLib.ProximityGap.Frontier.TameCubicPowerSeries
