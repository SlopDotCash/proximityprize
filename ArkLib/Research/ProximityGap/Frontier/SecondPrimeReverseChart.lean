/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeScalarChart
import ArkLib.Research.ProximityGap.Frontier.ReverseHessianAffineSection
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeReceivedJetColumns
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeHessianTransport

/-! # The coordinate-field presentation of a trivariate component

Passing to K(X) retains the scalar and the value as polynomial variables.
A positive value degree prevents the original prime factor from becoming a unit.
-/

open Polynomial
namespace ArkLib.ProximityGap.Frontier.SecondPrimeReverseChart

open SecondPrimeCoordinateWeight
variable {K : Type} [Field K]

/-- Map the coordinate to its rational function field, retaining scalar and value variables. -/
noncomputable def reverseChart (f : Surface K) : (RatFunc K)[X][X] :=
  f.map (mapRingHom (algebraMap K[X] (RatFunc K)))

theorem value_degree (f : Surface K) : (reverseChart f).natDegree = f.natDegree := by
  unfold reverseChart
  rw [natDegree_map_eq_of_injective (map_injective _ (RatFunc.algebraMap_injective K))]

private theorem twice_swapped (f : Surface K) :
    (f.map Bivariate.swap.toRingHom).map Bivariate.swap.toRingHom = f := by
  ext j : 1
  rw [coeff_map, coeff_map]
  change Bivariate.swap (Bivariate.swap (f.coeff j)) = f.coeff j
  exact Bivariate.swap_swap_apply _

/-- An irreducible positive-value-degree component remains irreducible after the coordinate
variable enters the coefficient field. In particular its coefficient content is a unit. -/
theorem irreducible (f : Surface K) (hf : Irreducible f) (hd : 0 < f.natDegree) :
    Irreducible (reverseChart f) := by
  let g := f.map Bivariate.swap.toRingHom
  have hg : Irreducible g :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv Bivariate.swap.toRingEquiv)).mpr hf
  have hdeg : 0 < g.natDegree := by
    rw [show g.natDegree = f.natDegree from
      natDegree_map_eq_of_injective (f := Bivariate.swap.toRingHom) Bivariate.swap.injective f]
    exact hd
  have h := SecondPrimeReceivedJetColumns.chart_irreducible g hg hdeg
  simpa only [g, SecondPrimeScalarChart.scalarChart, twice_swapped, reverseChart] using h

/-- Positive-degree prime divisibility descends from any injective coefficient embedding
into a field. The resultant uses the original degrees before transport. -/
theorem descends {L : Type} [Field L] (χ : K[X][X] →+* L) (hχ : Function.Injective χ)
    (f g : Surface K) (hi : Irreducible f) (hb : 0 < f.natDegree)
    (hdvd : f.map χ ∣ g.map χ) : f ∣ g := by
  by_contra hnd
  have raw := SecondPrimeSectionResultant.resultant_ne_zero f g hi hb hnd
  have nz : f.map χ ≠ 0 := by
    intro h
    apply hi.ne_zero
    apply map_injective χ hχ
    simpa only [Polynomial.map_zero] using h
  have proper : ¬ IsUnit (f.map χ) := fun hu => by
    have h := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_map_eq_of_injective hχ] at h
    omega
  have zero := resultant_eq_zero_iff.mpr
    ⟨Or.inl nz, fun hc => proper (hc.isUnit_of_dvd hdvd)⟩
  rw [natDegree_map_eq_of_injective hχ, natDegree_map_eq_of_injective hχ,
    resultant_map_map] at zero
  exact raw ((map_eq_zero_iff _ hχ).mp zero)

/-- The two rational-function presentations test the same raw component divisor. -/
theorem hessian_divides_reverse (f : Surface K) (hi : Irreducible f) (hb : 0 < f.natDegree)
    (hdvd : MovingCubicVanishingBranch.genericEquation (SecondPrimeScalarChart.scalarChart f) ∣
      MovingCubicVanishingBranch.genericEquation
        (CanonicalQuarticSiteOrder.scalarFieldHessian (SecondPrimeScalarChart.scalarChart f))) :
    MovingCubicVanishingBranch.genericEquation (reverseChart f) ∣
      MovingCubicVanishingBranch.genericEquation (ReverseHessianAffineSection.hessian
        (reverseChart f)) := by
  rw [← SecondPrimeHessianTransport.scalarChart_rawHessian] at hdvd
  let χ := ((algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))).comp
    (mapRingHom (algebraMap K[X] (RatFunc K)))).comp Bivariate.swap.toRingHom
  have hχ : Function.Injective χ := (RatFunc.algebraMap_injective (RatFunc K)).comp
    ((map_injective _ (RatFunc.algebraMap_injective K)).comp Bivariate.swap.injective)
  have h : f ∣ SecondPrimeHessianTransport.rawHessian f := by
    apply descends χ hχ _ _ hi hb
    simpa only [MovingCubicVanishingBranch.genericEquation, SecondPrimeScalarChart.scalarChart,
      Polynomial.map_map, RingHom.comp_assoc, χ] using hdvd
  obtain ⟨w, hw⟩ := h
  unfold reverseChart
  rw [← SecondPrimeHessianTransport.reverseChart_rawHessian, hw, Polynomial.map_mul]
  unfold MovingCubicVanishingBranch.genericEquation
  rw [Polynomial.map_mul]
  exact dvd_mul_right _ _

/-- Polynomial sections over the original coordinates give values in the coordinate
function field at the corresponding embedded scalar. -/
theorem root_in_reverse (f : Surface K) (z : K) (q : K[X])
    (hroot : f.eval₂ (evalRingHom (C z)) q = 0) :
    ((reverseChart f).map (evalRingHom (RatFunc.C z))).eval
      (algebraMap K[X] (RatFunc K) q) = 0 := by
  let χ := algebraMap K[X] (RatFunc K)
  have comm : (evalRingHom (RatFunc.C z)).comp (mapRingHom χ) =
      χ.comp (evalRingHom (C z)) := by
    apply RingHom.ext
    intro p
    change (p.map χ).eval (RatFunc.C z) = χ (p.eval (C z))
    have ec : χ (C z) = RatFunc.C z := by simp [χ]
    rw [eval_map, ← ec, eval₂_at_apply]
  have hz := congrArg χ hroot
  rw [hom_eval₂, map_zero] at hz
  simpa only [reverseChart, eval_map, eval₂_map, comm, χ] using hz

/-- A genuine component of value degree two, three or four on the Hessian-divisible
branch carries at most one selected scalar whenever the characteristic exceeds 276. -/
theorem divisible_label_cap {F : Type} [Field F] (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 276 < p) (f : Surface K) (hi : Irreducible f) (hlo : 2 ≤ f.natDegree)
    (hhi : f.natDegree ≤ 4) (htri : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (hdvd : MovingCubicVanishingBranch.genericEquation (SecondPrimeScalarChart.scalarChart f) ∣
      MovingCubicVanishingBranch.genericEquation
        (CanonicalQuarticSiteOrder.scalarFieldHessian (SecondPrimeScalarChart.scalarChart f)))
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0) : G.card ≤ 1 := by
  have hb : 0 < f.natDegree := by omega
  have hr := irreducible f hi hb
  have he := value_degree f
  have hpr := hr.isPrimitive (by omega)
  have hgen := (hpr.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc (RatFunc K))).mp hr
  have hx : Bivariate.degreeX (reverseChart f) ≤ 34 := by
    apply Finset.sup_le
    intro j hj
    have hj' : f.coeff j ≠ 0 := by
      intro hz
      apply mem_support_iff.mp hj
      simp only [reverseChart, coeff_map, hz, map_zero]
    change ((reverseChart f).coeff j).natDegree ≤ 34
    rw [reverseChart, coeff_map, coe_mapRingHom]
    have h := htri j hj'
    exact natDegree_map_le.trans (by omega)
  apply ReverseHessianAffineSection.card_embedded_scalar_le_one (RatFunc.C.comp φ)
    (p := p) (reverseChart f) hgen hpr (by omega) (by omega) (by omega) 34 hx (by omega)
    (hessian_divides_reverse f hi hb hdvd) G
  intro z hz
  exact ⟨_, root_in_reverse f (φ z) (q z) (hroot z hz)⟩

#print axioms divisible_label_cap
#print axioms root_in_reverse
#print axioms hessian_divides_reverse
#print axioms irreducible
end ArkLib.ProximityGap.Frontier.SecondPrimeReverseChart
