/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualPopulations

/-! # Descending an affine component through two actual polynomial sections -/
namespace ArkLib.ProximityGap.Frontier.SecondPrimeActualPopulations
open Finset Polynomial HalfPredecessorLineCoreGeometry

/-- An affine graph over any extension containing the polynomial ring, with at least two
selected base-field sections, coincides on those labels with a unique bounded-degree head. -/
theorem affine_head_descent {F : Type} {R : Type*} [Field F] [Field R] (φ : F[X] →+* R)
    (hφ : Function.Injective φ) (G : Finset F) (hG : 1 < G.card) (q : F → F[X]) (k : ℕ)
    (hq : ∀ z ∈ G, (q z).natDegree < k) (a b : R)
    (hline : ∀ z ∈ G, φ (q z) = a + φ (C z) * b) :
    ∃! h : F[X] × F[X], h.1.natDegree < k ∧ h.2.natDegree < k ∧
      ∀ z ∈ G, q z = h.1 + C z * h.2 := by
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp hG
  let B := C (x-y)⁻¹ * (q x - q y)
  let A := q x - C x * B
  have hB : B.natDegree < k := (natDegree_C_mul_le _ _).trans_lt
    ((natDegree_sub_le _ _).trans_lt (max_lt (hq x hx) (hq y hy)))
  have hsec : C (x-y) * B = q x - q y := by
    simp only [B, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hxy), C_1, one_mul]
  have hA : A.natDegree < k := (natDegree_sub_le ..).trans_lt
    (max_lt (hq x hx) ((natDegree_C_mul_le _ _).trans_lt hB))
  have hne : C (x-y) ≠ (0 : F[X]) := C_ne_zero.mpr (sub_ne_zero.mpr hxy)
  have hb : φ B = b := by
    apply mul_left_cancel₀ (show φ (C (x-y)) ≠ 0 from
      fun hz => hne (hφ (hz.trans (map_zero φ).symm)))
    calc
      φ (C (x-y)) * φ B = φ (q x) - φ (q y) := by
        rw [← map_mul, hsec, map_sub]
      _ = φ (C (x-y)) * b := by rw [hline x hx, hline y hy, map_sub, map_sub]; ring
  have ha : φ A = a := by
    simp only [A,map_sub,map_mul,hline x hx,hb]
    ring
  refine ⟨(A,B),⟨hA,hB,fun z hz => hφ ?_⟩,?_⟩
  · rw [map_add,map_mul,ha,hb,hline z hz]
  · rintro ⟨v,w⟩ ⟨_,_,hall⟩
    have hw : w = B := by
      apply mul_left_cancel₀ hne
      rw [hsec, hall x hx, hall y hy, map_sub]
      ring
    apply Prod.ext
    · change v = q x - C x * B
      rw [hall x hx]
      simp [hw]
    · exact hw

/-- An affine geometric component with two selected labels cannot realize the nonlinear
linear-in-value alternative of the actual interpolation surface. -/
theorem head_of_affine_component {F I K : Type} {R : Type*} [Field F] [DecidableEq F]
    [Fintype I] [Field K] [Field R] {dom : I ↪ F} {δ : NNReal}
    {u : Code.WordStack F (Fin 2) I} (fam : Family dom δ u) (σ : F →+* K)
    (f : Factor K) (hh : 1 < (population fam σ f).card)
    (φ : F[X] →+* R) (hφ : Function.Injective φ) (a b : R)
    (haff : ∀ z ∈ population fam σ f, φ (fam.q z) = a + φ (C z) * b) :
    ∃ h, valid h ∧ population fam σ f ⊆ carried fam h := by
  classical
  have sub : population fam σ f ⊆ fam.G := filter_subset _ _
  obtain ⟨p,⟨hp,hq,hes⟩,_⟩ := affine_head_descent φ hφ _ hh fam.q 67108864
    (fun z hz => fam.degree_lt z (sub hz)) a b haff
  exact ⟨p,⟨hp,hq⟩,fun z hz => mem_filter.mpr ⟨sub hz,hes z hz⟩⟩

#print axioms head_of_affine_component
#print axioms affine_head_descent
end ArkLib.ProximityGap.Frontier.SecondPrimeActualPopulations
