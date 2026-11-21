/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticFactor

/-! # Populations on the two common quarter-rate interpolation surfaces

The simple interpolant supplies the coordinate bound, while the double-root
interpolant supplies the low scalar/value degree. Both bounds pass to an
irreducible common factor, even when its coefficients lie over an extension.
At 626349397 agreements each common quadratic carries at most 263 labels.
A common linear factor with more than 228 labels carries one actual secant. -/

namespace ArkLib.ProximityGap.Frontier.QuarterRateCommonPopulation
open Polynomial Finset Code SecondPrimeCoordinateWeight SecondPrimeQuarticInterpolation
open HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open _root_.ProximityGap.SecondPrimeLinearFactor _root_.ProximityGap.SecondPrimeQuadraticFactor
open scoped NNReal

variable {I F K : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Finite F]
  [DecidableEq F] [Field K] {D : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- The site incidence count extracts 35 collinear folded witnesses from a set
of 229 selected sections of a linear or parametric quadratic factor. -/
theorem extraction (fam : BadScalarRichPointFamily D 268435456 δ u)
    (hn : Fintype.card I = 1073741824) (ht : 626349397 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    SecantExtraction fam 229 := by
  let _ := Fintype.ofFinite F
  intro M hM hm U
  apply extraction_of_geometry (m := 195) (t := 626349397) fam (by decide) (by decide)
    _ M hM hm U hn ht
  intro c a b l v hc hinc hcover ha hb hl
  omega

/-- A divisor shared by the two surfaces inherits the coordinate bound of the
first and the scalar/value total degree bound of the second. -/
theorem common_shape {Q₁ Q₂ f : Surface K} (ha : Q₁ ≠ 0) (hb : Q₂ ≠ 0)
    (h₁ : f ∣ Q₁) (h₂ : f ∣ Q₂)
    (wa : ∀ j i a, ((Q₁.coeff j).coeff i).coeff a ≠ 0 → a + j * 268435455 < 626349397)
    (sb : ∀ j i a, ((Q₂.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 16) :
    Bivariate.totalDegree f ≤ 16 ∧
      ∀ j i a, ((f.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 16 ∧ a ≤ 626349396 := by
  have hq : Bivariate.totalDegree Q₂ ≤ 16 := by
    apply Finset.sup_le
    intro j hj
    have hi := leadingCoeff_ne_zero.mpr (mem_support_iff.mp hj)
    exact sb j (Q₂.coeff j).natDegree _ (leadingCoeff_ne_zero.mpr hi)
  have hs : Bivariate.totalDegree f ≤ 16 := by
    obtain ⟨r, hr⟩ := h₂
    rw [hr] at hb hq
    rw [Bivariate.totalDegree_mul (left_ne_zero_of_mul hb) (right_ne_zero_of_mul hb)] at hq
    omega
  have hw : weight 0 Q₁ ≤ 626349396 := by
    apply weight_le_of_coeff
    intro j i a h
    have := wa j i a h
    omega
  obtain ⟨g, hprod⟩ := h₁
  rw [hprod] at hw ha
  rw [weight_mul 0 f g (left_ne_zero_of_mul ha) (right_ne_zero_of_mul ha)] at hw
  refine ⟨hs, ?_⟩
  intro j i a h
  have hi : (f.coeff j).coeff i ≠ 0 := fun hz => h (by simp [hz])
  have hj : f.coeff j ≠ 0 := fun hz => hi (by simp [hz])
  have hs' := Bivariate.coeff_totalDegree_le f (mem_support_iff.mpr hj)
  have hcoord := coeff_weight_le 0 f h
  have hscalar := le_natDegree_of_ne_zero hi
  omega

/-- Genuine bad labels whose chosen witness lies on a specified component. -/
noncomputable def population (fam : BadScalarRichPointFamily D 268435456 δ u)
    (φ : F →+* K) (f : Surface K) : Finset F := by
  classical
  exact fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0

omit [DecidableEq I] in
/-- On the actual two interpolation shapes an irreducible common quadratic
carries at most 263 labels. A populous common linear factor carries its
entire population on a single secant of the original folded witnesses. -/
theorem common_population (fam : BadScalarRichPointFamily D 268435456 δ u)
    (φ : F →+* K) (a : Monomials 268435458 2 268435455 626349397 → K)
    (b : Monomials 16 3 268435455 (2 * 626349397) → K) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Surface K) (hf : Irreducible f) (h₁ : f ∣ surface a) (h₂ : f ∣ surface b)
    (hn : Fintype.card I = 1073741824) (ht : 626349397 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1252698792 → (i : K) ≠ 0) :
    (f.natDegree = 1 → 228 < (population fam φ f).card →
        ∃ p ∈ lineParameters fam, population fam φ f ⊆ pointsOn fam p) ∧
      (f.natDegree = 2 → (population fam φ f).card ≤ 263) := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨hs, hw⟩ := common_shape (surface_ne_zero ha) (surface_ne_zero hb) h₁ h₂
    (fun _ _ _ h => (surface_support a h).2.2) (fun _ _ _ h => (surface_support b h).2.1)
  have hE := extraction fam hn ht
  refine ⟨fun hd => linear_factor_is_head_of_extraction fam φ f hf hd (hs.trans (by decide)) hE,
    fun hd => ?_⟩
  exact quadratic_population_of_extraction (w := 626349396) (m := 228) fam φ f f hf.ne_zero
    dvd_rfl hf hd (fun j i a h => ⟨(hw j i a h).1.trans (by decide), (hw j i a h).2⟩)
    (by decide) hchar hE

omit [DecidableEq I] in
/-- Every irreducible common component of positive value degree carrying more
than 263 genuine labels is covered in full by one base-field secant. -/
theorem head_of_large_population (fam : BadScalarRichPointFamily D 268435456 δ u)
    (φ : F →+* K) (a : Monomials 268435458 2 268435455 626349397 → K)
    (b : Monomials 16 3 268435455 (2 * 626349397) → K) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Surface K) (hf : Irreducible f) (hpos : 0 < f.natDegree)
    (h₁ : f ∣ surface a) (h₂ : f ∣ surface b)
    (hn : Fintype.card I = 1073741824) (ht : 626349397 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1252698792 → (i : K) ≠ 0)
    (hbig : 263 < (population fam φ f).card) :
    ∃ p ∈ lineParameters fam, population fam φ f ⊆ pointsOn fam p := by
  classical
  have hv : (surface a).natDegree ≤ 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i w
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support a h).1
  have hdeg := (natDegree_le_of_dvd h₁ (surface_ne_zero ha)).trans hv
  obtain ⟨hline, hquad⟩ := common_population fam φ a b ha hb f hf h₁ h₂ hn ht hchar
  by_cases h : f.natDegree = 2
  · exact False.elim (hbig.not_ge (hquad h))
  · exact hline (by omega) (by omega)

end ArkLib.ProximityGap.Frontier.QuarterRateCommonPopulation
