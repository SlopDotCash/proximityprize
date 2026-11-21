/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.WeightedSylvesterDegree
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # Counting sections on an irreducible component by its actual resultant

The base coefficient ring still contains the coordinate polynomial variable. Specializing
the scalar leaves a polynomial identity in that coordinate. -/

open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.SecondPrimeSectionResultant

variable {K : Type} [Field K]

private abbrev Surface (K : Type) [Field K] := Polynomial (Polynomial K[X])

/-- A positive-value-degree irreducible component has a nonzero resultant against every
polynomial it does not divide. The actual degrees are used before specializing any scalar. -/
theorem resultant_ne_zero (f g : Surface K) (hi : Irreducible f) (hpos : 0 < f.natDegree)
    (hnd : ¬ f ∣ g) : resultant f g f.natDegree g.natDegree ≠ 0 := by
  let L := FractionRing (Polynomial K[X])
  let φ := algebraMap (Polynomial K[X]) L
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hp := hi.isPrimitive hpos.ne'
  have hirr := (hp.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hi
  have hd : ¬ f.map φ ∣ g.map φ := fun h => hnd ((hp.dvd_iff_fraction_map_dvd_fraction_map L).mpr h)
  have hc := (hirr.isCoprime_or_dvd (g.map φ)).resolve_right hd
  have hr := Polynomial.resultant_ne_zero (f.map φ) (g.map φ) hc
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hr
  exact fun h => hr (by rw [h, map_zero])

/-- If many distinct actual labels have a common section, a positive-degree irreducible
component divides the auxiliary polynomial in the original trivariate polynomial ring. -/
theorem divides_of_many_sections {F : Type} [Field F] (φ : F →+* K) (f g : Surface K)
    (hi : Irreducible f) (hpos : 0 < f.natDegree) {m s : ℕ}
    (hf : WeightedSylvesterDegree.TotalDegreeLe f m)
    (hg : WeightedSylvesterDegree.TotalDegreeLe g s)
    (G : Finset F) (w : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0 ∧
      g.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hlarge : f.natDegree * s + g.natDegree * m - f.natDegree * g.natDegree < G.card) : f ∣ g := by
  by_contra hnd
  apply resultant_ne_zero f g hi hpos hnd
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : G => C (φ (z : F)))
    (C_injective.comp (φ.injective.comp Subtype.val_injective))
  · intro z
    obtain ⟨ha, hb⟩ := hroot z z.property
    apply map_resultant_eq_zero_of_common_root (evalRingHom (C (φ (z : F)))) f g le_rfl le_rfl
      (Or.inl hpos.ne') (w z)
    · rwa [eval_map]
    · rwa [eval_map]
  · simpa using (WeightedSylvesterDegree.natDegree_resultant_le f g hf hg).trans_lt hlarge

/-- For a cubic a quadratic auxiliary has at most 3s+2(m−3) common sections.
A constant or linear auxiliary satisfies the same upper bound. -/
theorem cubic_section_cap {F : Type} [Field F] (φ : F →+* K) (f g : Surface K)
    (hi : Irreducible f) (hb : f.natDegree = 3) (hgn : g ≠ 0) (hgy : g.natDegree ≤ 2)
    {m s : ℕ} (hm : 3 ≤ m) (hf : WeightedSylvesterDegree.TotalDegreeLe f m)
    (hg : WeightedSylvesterDegree.TotalDegreeLe g s)
    (G : Finset F) (w : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0 ∧
      g.eval₂ (evalRingHom (C (φ z))) (w z) = 0) :
    G.card ≤ 3 * s + 2 * (m - 3) := by
  by_contra! hbad
  have hbound : f.natDegree * s + g.natDegree * m - f.natDegree * g.natDegree < G.card := by
    rw [hb]
    interval_cases hg' : g.natDegree <;> omega
  have hdiv := divides_of_many_sections φ f g hi (by omega) hf hg G w hroot hbound
  have hle := natDegree_le_of_dvd hdiv hgn
  omega

open Classical in
/-- On a literal irreducible cubic with scalar/value total degree at most m, at most 5m−9
distinct sections are multiple in value. The specialization can lose its leading term. -/
theorem cubic_multiple_section_cap {F : Type} [Field F] (φ : F →+* K) (f : Surface K)
    (hchar : (3 : K) ≠ 0) (hi : Irreducible f) (hb : f.natDegree = 3)
    {m : ℕ} (hm : 3 ≤ m) (hf : WeightedSylvesterDegree.TotalDegreeLe f m)
    (G : Finset F) (w : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0) :
    (G.filter (fun z => f.derivative.eval₂ (evalRingHom (C (φ z))) (w z) = 0)).card ≤
      5 * m - 9 := by
  classical
  have hval : (3 : Polynomial K[X]) ≠ 0 := by
    simpa only [map_ofNat] using (C_ne_zero.mpr (C_ne_zero.mpr hchar))
  have hlead : f.coeff 3 ≠ 0 := hb ▸ leadingCoeff_ne_zero.mpr hi.ne_zero
  have hd : f.derivative ≠ 0 := by
    intro hd
    have he := congrArg (fun p : Surface K => p.coeff 2) hd
    simp only [coeff_derivative, coeff_zero] at he
    apply (mul_ne_zero hlead hval)
    convert he using 1
    norm_num
  have htri : WeightedSylvesterDegree.TotalDegreeLe f.derivative (m - 1) := by
    intro j hj
    have hlead' : f.coeff (j + 1) ≠ 0 := fun h => hj (by simp [coeff_derivative, h])
    have hbudget := hf (j + 1) hlead'
    have h' := Polynomial.coeff_derivative_natDegree_le f j
    omega
  apply le_trans (cubic_section_cap φ f f.derivative hi hb hd
    ((natDegree_derivative_le f).trans (by omega)) hm hf htri _ w (fun z hz => ?_))
    (by omega)
  obtain ⟨hzG, hz'⟩ := mem_filter.mp hz
  exact ⟨hroot z hzG, hz'⟩

/-- The scalar/value total-degree triangle descends to every nonzero surface divisor. -/
theorem factor_triangle {f Q : Surface K} {m : ℕ} (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m) :
    WeightedSylvesterDegree.TotalDegreeLe f m := by
  classical
  have hQt : Bivariate.totalDegree Q ≤ m := by
    apply Finset.sup_le
    intro j hj
    have hj' := mem_support_iff.mp hj
    have hi : (Q.coeff j).coeff (Q.coeff j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hj'
    have ha := leadingCoeff_ne_zero.mpr hi
    exact htri _ _ _ ha
  obtain ⟨H, hH⟩ := hdiv
  have hne : f * H ≠ 0 := hH ▸ hQ
  rw [hH, Bivariate.totalDegree_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)] at hQt
  intro j hj
  have h := Bivariate.coeff_totalDegree_le f (mem_support_iff.mpr hj)
  omega

/-- All but at most 161 of the sections carried by an irreducible degree-three factor of the
actual interpolant are simple. This applies even after degree drops in an individual fiber. -/
theorem secondPrime_multiple_section_cap {F : Type} [Field F] (φ : F →+* K)
    (f Q : Surface K) (hchar : (3 : K) ≠ 0) (hi : Irreducible f) (hb : f.natDegree = 3)
    (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (G : Finset F) (w : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0) :
    open scoped Classical in
    (G.filter (fun z => f.derivative.eval₂ (evalRingHom (C (φ z))) (w z) = 0)).card ≤ 161 := by
  exact cubic_multiple_section_cap φ f hchar hi hb (by decide : 3 ≤ 34)
    (factor_triangle hQ hdiv htri) G w hroot

/-- At a simple selected section the specialized cubic contains its literal linear factor.
The complementary factor evaluated on the section is exactly the nonzero derivative. -/
theorem cofactor_of_simple_section {f : Surface K} (z : K) (w : K[X])
    (hroot : f.eval₂ (evalRingHom (C z)) w = 0)
    (hsimple : f.derivative.eval₂ (evalRingHom (C z)) w ≠ 0) :
    ∃ H : Polynomial K[X], f.map (evalRingHom (C z)) = (X - C w) * H ∧
      H.eval w = f.derivative.eval₂ (evalRingHom (C z)) w ∧ H.eval w ≠ 0 := by
  have hroot' : IsRoot (f.map (evalRingHom (C z))) w := by
    simpa only [IsRoot.def, eval_map] using hroot
  obtain ⟨H, hH⟩ := dvd_iff_isRoot.mpr hroot'
  have hder : f.derivative.eval₂ (evalRingHom (C z)) w = H.eval w := by
    rw [← eval_map, ← derivative_map, hH, derivative_mul]
    simp
  exact ⟨H, hH, hder.symm, hder ▸ hsimple⟩

open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension in
/-- When a component carries sufficiently many rich sections, it actually divides every
member of the interpolation kernel for the same received rows. The population budget uses
the value-degree bound v instead of paying for the full scalar degree twice. -/
theorem divides_interpolation_kernel {F ι : Type} [Field F] (φ : F →+* K)
    (dom : ι ↪ K) (u₀ u₁ : ι → K) (f : Surface K) (hi : Irreducible f)
    (hpos : 0 < f.natDegree) {m s v d t : ℕ} (ht : 0 < t)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f m) (G : Finset F) (w : F → K[X])
    (hfit : ∀ z ∈ G, (w z).natDegree ≤ d ∧
      ∃ S : Finset ι, t ≤ S.card ∧ ∀ i ∈ S, (w z).eval (dom i) = u₀ i + φ z * u₁ i)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hlarge : f.natDegree * s + v * m < G.card) :
    ∀ c : Monomials s v d t → K, c ∈ LinearMap.ker (constraints dom u₀ u₁) → f ∣ surface c := by
  classical
  intro c hc
  by_cases hz : surface c = 0
  · rw [hz]
    exact dvd_zero f
  have hdeg : (surface c).natDegree ≤ v := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support c h).1
  have htri : WeightedSylvesterDegree.TotalDegreeLe (surface c) s :=
    factor_triangle hz dvd_rfl (fun _ _ _ h => (surface_support c h).2.1)
  apply divides_of_many_sections φ f (surface c) hi hpos hf htri G w
  · intro z hzG
    obtain ⟨hdeg, S, hS, ha⟩ := hfit z hzG
    exact ⟨hroot z hzG, kernel_specializes_zero dom u₀ u₁ ht hc (φ z) (w z) hdeg S hS ha⟩
  · exact (Nat.sub_le _ _).trans_lt
      ((Nat.add_le_add_left (Nat.mul_le_mul_right m hdeg) _).trans_lt hlarge)

#print axioms divides_interpolation_kernel
#print axioms cofactor_of_simple_section
#print axioms factor_triangle
#print axioms secondPrime_multiple_section_cap
#print axioms cubic_multiple_section_cap
#print axioms resultant_ne_zero
#print axioms divides_of_many_sections
#print axioms cubic_section_cap
end ArkLib.ProximityGap.Frontier.SecondPrimeSectionResultant
