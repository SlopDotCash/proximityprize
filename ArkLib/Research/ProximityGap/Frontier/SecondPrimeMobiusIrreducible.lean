/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.IntegralSectionChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeMobiusSections

/-! # Irreducibility under weighted coordinate inversion

Reflection at the polynomial's attained weight cannot introduce a coordinate
factor at the new origin. Reflecting a putative factorization back therefore
preserves any nonunit factors, giving a factorization of the original surface.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeMobiusIrreducible

open Polynomial Finset SecondPrimeCoordinateWeight
open IntegralSectionChart

variable {K : Type} [Field K]

private theorem orient_invol (f : Surface K) : orient (orient f) = f := by
  ext j : 1
  simp only [orient, coeff_map]
  exact Bivariate.swap_swap_apply _

private theorem orient_inj : Function.Injective (orient (K := K)) := fun _ _ h => by
  simpa only [orient_invol] using congrArg orient h

/-- Swapping X and Z identifies the two integral presentations of the common chart. -/
theorem orient_surfaceChart [Infinite K] (r : K) (W d : ℕ) (f : Surface K) :
    orient (SecondPrimeMobiusSections.surfaceChart r W d f) = chart r W d (orient f) := by
  have h (z : K) : fiber (orient (SecondPrimeMobiusSections.surfaceChart r W d f)) z =
      fiber (chart r W d (orient f)) z := by
    ext j : 1
    rw [fiber_orient, SecondPrimeMobiusSections.surface_fiber,
      SecondPrimeMobiusSections.plane_coeff, fiber_chart_coeff, fiber_orient, Nat.mul_comm d j]
    rfl
  ext j i : 2
  apply Polynomial.funext
  intro z
  simpa only [fiber, coeff_map, coe_mapRingHom, coe_evalRingHom] using
    congrArg (fun g : K[X][X] => (g.coeff j).coeff i) (h z)

private abbrev bound (d W : ℕ) (f : Surface K) :=
  ∀ j, f.coeff j ≠ 0 → (f.coeff j).natDegree + d*j ≤ W

private theorem bound_iff (d W : ℕ) (f : Surface K) :
    bound d W f ↔ weight d (orient f) ≤ W := by
  constructor
  · intro h
    apply weight_le_of_coeff
    intro j i a ha
    have hj : f.coeff j ≠ 0 := by
      intro hz
      apply ha
      simp [orient, coeff_map, hz]
    have hg := (le_natDegree_of_ne_zero ha).trans (Bivariate.coeff_natDegree_le_degreeX
      ((orient f).coeff j) i)
    rw [(orient_profile f j).2] at hg
    simpa only [Nat.mul_comm j d] using (Nat.add_le_add_right hg (j*d)).trans
      (show (f.coeff j).natDegree+j*d ≤ W by simpa only [Nat.mul_comm j d] using h j hj)
  · intro hw j hj
    have hj' : (orient f).coeff j ≠ 0 := by
      simp only [orient, coeff_map]
      exact (map_ne_zero_iff _ Bivariate.swap.injective).mpr hj
    obtain ⟨i, hi, hi', _⟩ := Bivariate.exists_max_index_degreeX ((orient f).coeff j) hj'
    have h := (coeff_weight_le d (orient f)
      (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))).trans hw
    change (((orient f).coeff j).coeff i).natDegree + j*d ≤ W at h
    rw [hi', (orient_profile f j).2, Nat.mul_comm j d] at h
    exact h

private theorem bound_of_unit {f : Surface K} (d : ℕ) (hu : IsUnit f) : bound d 0 f := by
  obtain ⟨b, hb, rfl⟩ := Polynomial.isUnit_iff.mp hu
  obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.mp hb
  intro j hj
  by_cases hz : j = 0
  · simp [hz]
  · simp [coeff_C, hz] at hj

private theorem maximal_slot (d : ℕ) {f : Surface K} (hf : f ≠ 0) :
    ∃ j, f.coeff j ≠ 0 ∧ (f.coeff j).natDegree + d*j = weight d (orient f) := by
  let W := weight d (orient f)
  have hb := (bound_iff d W f).mpr le_rfl
  by_contra! h
  by_cases hz : W = 0
  · have hl := leadingCoeff_ne_zero.mpr hf
    apply h f.natDegree hl
    change _ = W
    exact le_antisymm (hb _ hl) (by rw [hz]; exact Nat.zero_le _)
  · have hlt : bound d (W-1) f := fun j hj => by
      have h₁ := (hb j hj).lt_of_ne (h j hj)
      omega
    have hbad := (bound_iff _ _ _).mp hlt
    change W ≤ W-1 at hbad
    omega

private noncomputable def reflAdd {R : Type*} [CommRing R] (n : ℕ) : R[X] →+ R[X] where
  toFun := reflect n
  map_zero' := reflect_zero
  map_add' _ _ := reflect_add _ _ _

private theorem reflect_product (A B d : ℕ) (f g : Surface K)
    (hf : bound d A f) (hg : bound d B g) :
    chart 0 (A+B) d (f*g) = chart 0 A d f * chart 0 B d g := by
  classical
  ext j : 1
  rw [coeff_chart, C_0, taylor_zero, coeff_mul, coeff_mul]
  change reflAdd _ (∑ p ∈ antidiagonal j, f.coeff p.1 * g.coeff p.2) = _
  rw [map_sum]
  apply sum_congr rfl
  intro p hp
  have hsum := mem_antidiagonal.mp hp
  rw [coeff_chart, coeff_chart, C_0, taylor_zero, taylor_zero]
  by_cases h₁ : f.coeff p.1 = 0
  · simp [h₁, reflAdd]
  by_cases h₂ : g.coeff p.2 = 0
  · simp [h₂, reflAdd]
  have h₁' := hf _ h₁
  have h₂' := hg _ h₂
  change reflect (A+B-d*j) (f.coeff p.1*g.coeff p.2) = _
  rw [← hsum, Nat.mul_add]
  convert reflect_mul (f.coeff p.1) (g.coeff p.2)
    (show (f.coeff p.1).natDegree ≤ A-d*p.1 by omega)
    (show (g.coeff p.2).natDegree ≤ B-d*p.2 by omega) using 2
  omega

private theorem reflect_zero_weight (d : ℕ) (f : Surface K) : chart 0 0 d f = f := by
  ext j i : 2
  rw [coeff_chart, C_0, taylor_zero, Nat.zero_sub, coeff_reflect]
  by_cases hi : i = 0
  · simp [hi]
  · rw [revAt_eq_self_of_lt (Nat.pos_of_ne_zero hi)]

private noncomputable abbrev atOrigin : Surface K →+* K[X][X] := mapRingHom (evalRingHom (0 : K[X]))

private theorem atOrigin_chart (r : K) (d : ℕ) {f : Surface K} (hf : f ≠ 0) :
    atOrigin (chart r (weight d (orient f)) d f) ≠ 0 := by
  obtain ⟨j, hj, he⟩ := maximal_slot d hf
  intro hz
  have h := congrArg (fun g : K[X][X] => g.coeff j) hz
  simp only [atOrigin, coe_mapRingHom, coeff_map, coe_evalRingHom, coeff_zero, coeff_chart,
    ← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero] at h
  rw [← he, Nat.add_sub_cancel, coeff_taylor_natDegree] at h
  exact leadingCoeff_ne_zero.mpr hj h

private theorem unit_of_reflect_unit (A d : ℕ) (f : Surface K) (hb : bound d A f)
    (h0 : atOrigin f ≠ 0) (hu : IsUnit (chart 0 A d f)) : IsUnit f := by
  obtain ⟨j, hj⟩ : ∃ j, ((f.coeff j).coeff 0) ≠ 0 := by
    by_contra! h
    apply h0
    ext j : 1
    simpa only [atOrigin, coe_mapRingHom, coeff_map, coe_evalRingHom,
      ← coeff_zero_eq_eval_zero, coeff_zero]
      using h j
  have hfj : f.coeff j ≠ 0 := fun h => hj (by simp [h])
  have hslot : ((chart 0 A d f).coeff j).coeff (A-d*j) ≠ 0 := by
    simpa only [coeff_chart, C_0, taylor_zero, coeff_reflect, revAt_le le_rfl, Nat.sub_self]
      using hj
  have hnj : (chart 0 A d f).coeff j ≠ 0 := fun h => hslot (by simp [h])
  have hz := bound_of_unit d hu j hnj
  have hlo := le_natDegree_of_ne_zero hslot
  have hb' := hb j hfj
  have he : A = 0 := by omega
  simpa only [he, reflect_zero_weight] using hu

/-- At the attained coordinate weight the integral weighted change preserves irreducibility. -/
theorem irreducible_chart (r : K) (d : ℕ) (f : Surface K) (hi : Irreducible f)
    (hy : 0 < f.natDegree) :
    Irreducible (chart r (weight d (orient f)) d f) := by
  let W := weight d (orient f)
  let g := chart r W d f
  let e := Polynomial.mapEquiv (taylorEquiv (C r)).toRingEquiv
  have hback : chart 0 W d g = e f := by
    ext j : 1
    simp only [g, coeff_chart, C_0, taylor_zero, reflect_reflect]
    change _ = (f.map (taylorEquiv (C r)).toRingEquiv.toRingHom).coeff j
    rw [coeff_map]
    rfl
  have hir : Irreducible (e f) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hi
  have h0 : atOrigin g ≠ 0 := atOrigin_chart r d hi.ne_zero
  have hbound : bound d W g := coordinate_weight r W d f ((bound_iff d W f).mpr le_rfl)
  have hw := (bound_iff d W g).mp hbound
  have hdeg : g.natDegree = f.natDegree := chart_natDegree r W d f
  refine ⟨fun hu => hy.ne' (hdeg ▸ natDegree_eq_zero_of_isUnit hu), ?_⟩
  intro a b he
  change g = a*b at he
  have hn : g ≠ 0 := fun h => h0 (by simp [h])
  have hp : a*b ≠ 0 := fun h => hn (he.trans h)
  have ha : a ≠ 0 := left_ne_zero_of_mul hp
  have hb : b ≠ 0 := right_ne_zero_of_mul hp
  have hno (v : Surface K) (hv : v ≠ 0) : orient v ≠ 0 := fun h =>
    hv (orient_inj (h.trans (show orient (0 : Surface K) = 0 from Polynomial.map_zero _).symm))
  let A := weight d (orient a)
  let B := W-A
  have hwprod : weight d (orient g) = A + weight d (orient b) := by
    rw [he]
    simpa only [A, orient, Polynomial.map_mul] using weight_mul d _ _ (hno a ha) (hno b hb)
  have hAB : A + B = W := by dsimp [B]; omega
  have hA := (bound_iff d A a).mpr le_rfl
  have hB := (bound_iff d B b).mpr (by dsimp [B]; omega)
  have h0ab : atOrigin a * atOrigin b ≠ 0 := fun h => h0 (by rw [he, map_mul]; exact h)
  have hsplit : e f = chart 0 A d a * chart 0 B d b := by
    rw [← hback, he, ← hAB]
    exact reflect_product A B d a b hA hB
  exact (hir.isUnit_or_isUnit hsplit).imp
    (unit_of_reflect_unit A d a hA (left_ne_zero_of_mul h0ab))
    (unit_of_reflect_unit B d b hB (right_ne_zero_of_mul h0ab))

/-- The common integral chart used on all scalar labels is irreducible at its actual weight. -/
theorem irreducible_surfaceChart [Infinite K] (r : K) (d : ℕ) (f : Surface K)
    (hi : Irreducible f) (hy : 0 < f.natDegree) :
    Irreducible (SecondPrimeMobiusSections.surfaceChart r (weight d f) d f) := by
  let e := Polynomial.mapEquiv (Bivariate.swap (R := K)).toRingEquiv
  have hir : Irreducible (orient f) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hi
  have hy' : 0 < (orient f).natDegree := by
    rw [orient, natDegree_map_eq_of_injective (f := Bivariate.swap.toRingEquiv.toRingHom)
      Bivariate.swap.injective]
    exact hy
  have hc := irreducible_chart r d (orient f) hir hy'
  rw [orient_invol, ← orient_surfaceChart] at hc
  exact (MulEquiv.irreducible_iff e.toMulEquiv).mp hc

#print axioms irreducible_surfaceChart

end ArkLib.ProximityGap.Frontier.SecondPrimeMobiusIrreducible
