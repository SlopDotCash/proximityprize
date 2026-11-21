/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CommonSectionChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant

/-! # Multiple sections of a ternary cubic

If the scalar/value total degree is at most `m`, the cubic discriminant has scalar
degree at most `4m - 6`. A repeated finite section annihilates the discriminant
even if the value degree drops after specializing the scalar.
-/

namespace ArkLib.ProximityGap.Frontier.CubicSectionDiscriminant

open Polynomial Finset _root_.ProximityGap.CommonSectionChart

variable {K : Type} [Field K]
private abbrev Surface (K : Type) [Field K] := Polynomial (Polynomial K[X])

private theorem degree_bound (f : Surface K) (hi : f ≠ 0) (hy : f.natDegree = 3)
    {m : ℕ} (hm : 3 ≤ m) (ht : WeightedSylvesterDegree.TotalDegreeLe f m) :
    f.discr.natDegree ≤ 4 * m - 6 := by
  have bound (j : ℕ) (hj : j ≤ 3) : (f.coeff j).natDegree ≤ m - j := by
    by_cases h : f.coeff j = 0
    · simp [h]
    have h' := ht j h
    omega
  have mul_const (c : ℕ) (q : Polynomial K[X]) :
      ((c : Polynomial K[X]) * q).natDegree ≤ q.natDegree := by
    simpa only [map_natCast] using (natDegree_C_mul_le (c : K[X]) q)
  rw [discr_of_degree_eq_three (by rw [degree_eq_natDegree hi, hy]; rfl)]
  have h₀ := bound 0 (by decide)
  have h₁ := bound 1 (by decide)
  have h₂ := bound 2 (by decide)
  have h₃ := bound 3 (by decide)
  have A := natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 h₂) (natDegree_pow_le_of_le 2 h₁)
  have B := natDegree_mul_le_of_le ((mul_const 4 _).trans h₃) (natDegree_pow_le_of_le 3 h₁)
  have C' := natDegree_mul_le_of_le ((mul_const 4 _).trans (natDegree_pow_le_of_le 3 h₂)) h₀
  have D := natDegree_mul_le_of_le ((mul_const 27 _).trans (natDegree_pow_le_of_le 2 h₃))
    (natDegree_pow_le_of_le 2 h₀)
  have E := natDegree_mul_le_of_le (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le ((mul_const 18 _).trans h₃) h₂) h₁) h₀
  exact (natDegree_add_le_of_le (natDegree_sub_le_of_le (natDegree_sub_le_of_le
    (natDegree_sub_le_of_le A B) C') D) E).trans (by omega)

private theorem nonzero (f : Surface K) (hi : Irreducible f) (hy : f.natDegree = 3)
    (hc : (3 : K) ≠ 0) : f.discr ≠ 0 := by
  have hval : (3 : Polynomial K[X]) ≠ 0 := by
    simpa only [map_ofNat] using (C_ne_zero.mpr (C_ne_zero.mpr hc))
  have hlead : f.coeff 3 ≠ 0 := hy ▸ leadingCoeff_ne_zero.mpr hi.ne_zero
  have h₂ : f.derivative.coeff 2 ≠ 0 := by
    rw [coeff_derivative]
    convert (mul_ne_zero hlead hval) using 1
    norm_num
  have hd := natDegree_derivative_le f
  have hder : f.derivative.natDegree = 2 := by
    have := le_natDegree_of_ne_zero h₂
    omega
  have hnd : ¬ f ∣ f.derivative := by
    intro h
    have := natDegree_le_of_dvd h (fun he => h₂ (by rw [he]; simp))
    omega
  have hr := SecondPrimeSectionResultant.resultant_ne_zero f f.derivative hi (by omega) hnd
  rw [show f.derivative.natDegree = f.natDegree - 1 by omega,
    resultant_deriv (natDegree_pos_iff_degree_pos.mp (by omega))] at hr
  exact fun he => hr (by rw [he, mul_zero])

private theorem root_identity {R : Type*} [CommRing R] (a b c d w : R)
    (h : a + (b + (c + d * w) * w) * w = 0) (h' : b + (2 * c + 3 * d * w) * w = 0) :
    c ^ 2 * b ^ 2 - 4 * d * b ^ 3 - 4 * c ^ 3 * a - 27 * d ^ 2 * a ^ 2
      + 18 * d * c * b * a = 0 := by
  have hb : b = -(2 * c + 3 * d * w) * w := by linear_combination h'
  rw [hb] at h ⊢
  have ha : a = c * w ^ 2 + 2 * d * w ^ 3 := by linear_combination h
  rw [ha]
  ring

open Classical in
/-- An irreducible cubic has at most `4m - 6` distinct scalar labels with repeated
selected sections. The estimate includes degree-losing fibers. -/
theorem multiple_sections {F : Type} [Field F] (φ : F →+* K) (f : Surface K)
    (hc : (3 : K) ≠ 0) (hi : Irreducible f) (hy : f.natDegree = 3)
    {m : ℕ} (hm : 3 ≤ m) (ht : WeightedSylvesterDegree.TotalDegreeLe f m)
    (G : Finset F) (w : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0) :
    (G.filter (fun z => f.derivative.eval₂ (evalRingHom (C (φ z))) (w z) = 0)).card ≤
      4 * m - 6 := by
  classical
  by_contra! h
  apply nonzero f hi hy hc
  let S := G.filter (fun z => f.derivative.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : S => C (φ (z : F)))
    (C_injective.comp (φ.injective.comp Subtype.val_injective))
  · intro z
    let e := evalRingHom (C (φ (z : F)))
    obtain ⟨hz, hder⟩ := mem_filter.mp z.property
    have hs := section_values (f.map e) (natDegree_map_le.trans hy.le) (w z)
    rw [eval_map] at hs
    rw [derivative_map, eval_map] at hs
    rw [hroot _ hz, hder] at hs
    rw [discr_of_degree_eq_three (by rw [degree_eq_natDegree hi.ne_zero, hy]; rfl)]
    simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_ofNat]
    apply root_identity _ _ _ _ (w z)
    · simpa only [cubic, coeff_map, e, coe_evalRingHom] using hs.1.symm
    · simpa only [residual, coeff_map, map_ofNat, e, coe_evalRingHom] using hs.2.symm
  · simpa [S] using (degree_bound f hi.ne_zero hy hm ht).trans_lt h

#print axioms multiple_sections
end ArkLib.ProximityGap.Frontier.CubicSectionDiscriminant
