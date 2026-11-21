/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeProperCubic
import ArkLib.Research.ProximityGap.Frontier.CubicSectionDiscriminant
import ArkLib.Research.ProximityGap.Frontier.TerminalFactorCoverage

/-! # Cubic sections in an over-budget family at the named predecessor

The actual quadratic and quartic population caps leave one irreducible cubic. Its
scalar Hessian is proper, and all but at most 130 selected sections are simple.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeCubicWitness
open Polynomial Finset SecondPrimeActualPopulations SecondPrimeScalarChart
open _root_.ProximityGap.CommonSectionChart
open CanonicalQuarticSiteOrder (scalarFieldHessian)
open MovingCubicVanishingBranch (genericEquation)
open scoped NNReal

open _root_.ProximityGap.TerminalFactorCoverage (Supported)

variable {F K I : Type} [Field F] [DecidableEq F] [Field K] [Fintype I] {dom : I ↪ F}
  {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- Selected sections of the component where the value derivative specializes nonzero. -/
noncomputable def simplePopulation (fam : Family dom δ u) (φ : F →+* K) (f : Factor K) :
    Finset F := by
  classical
  exact (population fam φ f).filter fun z ↦
    f.derivative.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) ≠ 0

private theorem simple_card (fam : Family dom δ u) (φ : F →+* K) (f Q : Factor K)
    (hc : (3 : K) ≠ 0) (hi : Irreducible f) (hy : f.natDegree = 3) (hQ : Q ≠ 0)
    (hd : f ∣ Q) (tri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34) :
    (population fam φ f).card ≤ (simplePopulation fam φ f).card + 130 := by
  classical
  let S := population fam φ f
  let isMultiple (z : F) := f.derivative.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  have multiple := CubicSectionDiscriminant.multiple_sections φ f hc hi hy (by decide : 3 ≤ 34)
    (SecondPrimeSectionResultant.factor_triangle hQ hd tri) S (fun z ↦ (fam.q z).map φ)
    (fun z hz ↦ (mem_filter.mp hz).2)
  have partition := Finset.card_filter_add_card_filter_not (s := S) (p := isMultiple)
  change (S.filter isMultiple).card ≤ 130 at multiple
  change S.card ≤ (S.filter fun z ↦ ¬isMultiple z).card + 130
  omega

/-- An actual violation forces an irreducible nonflat cubic with the indicated coordinate
weight, total population, and a separate lower bound on its simple sections. -/
theorem actual_cubic [Finite F] [Nonempty I] [IsAlgClosed K] (fam : Family dom δ u)
    (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 715827884 < p) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (hbig : 2147483648 < fam.G.card) :
    ∃ Q f : Factor K, Q ≠ 0 ∧ Supported Q ∧
      Irreducible f ∧ f ∣ Q ∧ f.natDegree = 3 ∧
      SecondPrimeCoordinateWeight.weight 67108863 f ≤ 290805098 ∧
      1431655733 ≤ (population fam φ f).card ∧
      1431655603 ≤ (simplePopulation fam φ f).card ∧
      ¬genericEquation (scalarChart f) ∣
        genericEquation (scalarFieldHessian (scalarChart f)) := by
  classical
  obtain ⟨Q, f, hQ, hs, hi, hd, hy, hpop, hw, hproper⟩ :=
    SecondPrimeProperCubic.actual_cubic fam φ hp hn ht hbig
  have hc : (3 : K) ≠ 0 := by
    intro he
    have hh := (CharP.cast_eq_zero_iff K p 3).mp he
    exact (by omega : ¬p ≤ 3) (Nat.le_of_dvd (by decide) hh)
  have total := simple_card fam φ f Q hc hi hy hQ hd (fun j i a ha ↦ (hs j i a ha).2.1)
  exact ⟨Q, f, hQ, hs, hi, hd, hy, hw, hpop, by omega, hproper⟩

/-- Specializing the scalar preserves the coordinate/value weight for each nonzero
coefficient. A coefficient that vanishes in the new fiber has coordinate degree zero. -/
private theorem fiber_bound (f : Factor K) {j d W : ℕ} (z : K) (hw : j * d ≤ W)
    (hW : SecondPrimeCoordinateWeight.weight d f ≤ W) :
    ((f.map (evalRingHom (C z))).coeff j).natDegree + j * d ≤ W := by
  rw [coeff_map]
  change ((f.coeff j).eval (C z)).natDegree + j * d ≤ W
  by_cases h : f.coeff j = 0
  · simpa [h] using hw
  have he : (f.coeff j).eval (C z) = (Bivariate.swap (f.coeff j)).map (evalRingHom z) := by
    simpa only [Bivariate.evalX_eq_map, Bivariate.evalY] using
      Bivariate.evalY_eq_evalX_swap z (f.coeff j)
  rw [he]
  have hu := (natDegree_map_le (f := evalRingHom z) (p := Bivariate.swap (f.coeff j))).trans_eq
    (Bivariate.natDegreeY_swap (f.coeff j))
  obtain ⟨i, hi, heq, _⟩ := Bivariate.exists_max_index_degreeX (f.coeff j) h
  have hg := SecondPrimeCoordinateWeight.coeff_weight_le d f
    (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))
  omega

/-- One coordinate chart for all actual simple sections. Its center can avoid any finite
set of sites and any additional finite set of nonzero polynomial tests over an extension.
The transformed residual attains its full homogeneous degree for every selected section. -/
theorem common_chart [Infinite K] (fam : Family dom δ u) (φ : F →+* K) (f : Factor K)
    (hy : f.natDegree = 3) (d v : ℕ) (hd : 67108863 ≤ d)
    (hW : SecondPrimeCoordinateWeight.weight d f ≤ v + d + d + d)
    (sites : Finset K) {E : Type*} [Field E] (ψ : K →+* E) (tests : Finset E[X])
    (htests : ∀ t ∈ tests, t ≠ 0) :
    let a (z : F) (j : ℕ) := (f.map (evalRingHom (C (φ z)))).coeff j
    let q (z : F) := (fam.q z).map φ
    ∃ r : K, r ∉ sites ∧ (∀ t ∈ tests, t.eval (ψ r) ≠ 0) ∧
      Function.Injective (fun x : K ↦ (x - r)⁻¹) ∧
      ∀ z ∈ simplePopulation fam φ f,
        cubic (change r (v + d + d + d) (a z 0)) (change r (v + d + d) (a z 1))
          (change r (v + d) (a z 2)) (change r v (a z 3)) (change r d (q z)) = 0 ∧
        (residual (change r (v + d + d) (a z 1)) (change r (v + d) (a z 2))
          (change r v (a z 3)) (change r d (q z))).natDegree = v + d + d ∧
        ∀ i : I, (change r d (q z)).eval (φ (dom i) - r)⁻¹ =
          (φ (dom i) - r)⁻¹ ^ d * φ (u 0 i + z * u 1 i) ↔
          (fam.q z).eval (dom i) = u 0 i + z * u 1 i := by
  classical
  let domainSites := univ.image (fun i : I ↦ φ (dom i))
  have qDegree (z : F) (hz : z ∈ simplePopulation fam φ f) :
      ((fam.q z).map φ).natDegree ≤ d := by
    have h := fam.degree_lt z (mem_filter.mp (mem_filter.mp hz).1).1
    exact natDegree_map_le.trans (by omega)
  refine (simple_fibers (simplePopulation fam φ f) (sites ∪ domainSites) ψ tests htests
    (fun z ↦ f.map (evalRingHom (C (φ z)))) (fun z ↦ (fam.q z).map φ) v d
    ?_ ?_ ?_ ?_ qDegree ?_ ?_).elim ?_
  · intro z _
    exact natDegree_map_le.trans hy.le
  · intro z _
    have h := fiber_bound f (j := 1) (φ z) (by omega : 1 * d ≤ v + d + d + d) hW
    omega
  · intro z _
    have h := fiber_bound f (j := 2) (φ z) (by omega : 2 * d ≤ v + d + d + d) hW
    omega
  · intro z _
    have h := fiber_bound f (j := 3) (φ z) (by omega : 3 * d ≤ v + d + d + d) hW
    omega
  · intro z hz
    rw [eval_map]
    exact (mem_filter.mp (mem_filter.mp hz).1).2
  · intro z hz
    rw [derivative_map, eval_map]
    exact (mem_filter.mp hz).2
  · rintro r ⟨hr, ht, hinj, hchart⟩
    obtain ⟨hsites, hdom⟩ := notMem_union.mp hr
    refine ⟨r, hsites, ht, hinj, ?_⟩
    intro z hz
    obtain ⟨hroot, hdegree⟩ := hchart z hz
    refine ⟨hroot, hdegree, ?_⟩
    intro i
    have hx : φ (dom i) ≠ r := fun h ↦ hdom (h ▸ mem_image_of_mem _ (mem_univ i))
    rw [eval_site_eq_iff _ _ _ _ (qDegree z hz) hx, eval_map_apply]
    exact φ.injective.eq_iff

section Named
open Code HalfPredecessorBadEventRichPointBridge
open _root_.ProximityGap _root_.ProximityGap.TerminalCollinearHeadCount
open ArkLib.ProximityGap.KKH26 PrizeShapeRateHalfBracket
open scoped ENNReal

private abbrev p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev g := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact p.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The one remaining simple-section estimate on the named predecessor domain. -/
def SimpleCubicCap : Prop :=
  ∀ u : WordStack (ZMod p) (Fin 2) (Fin (2 ^ 30)),
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2 ^ 26)
      ((715827881 : ℝ≥0) / 1073741824) u (by decide)
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    ∀ Q f : Factor (AlgebraicClosure (ZMod p)), Q ≠ 0 → Supported Q →
      Irreducible f → f ∣ Q → f.natDegree = 3 →
      SecondPrimeCoordinateWeight.weight 67108863 f ≤ 290805098 →
      (¬genericEquation (scalarChart f) ∣
        genericEquation (scalarFieldHessian (scalarChart f))) →
      (simplePopulation fam φ f).card ≤ 1431655602

/-- The single cubic estimate at the predecessor implies the operational radius equality. -/
theorem secondPrime_threshold_of_simple_cubic (h : SimpleCubicCap) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (evalCode g (2 ^ 30) (2 ^ 26 - 1))
      (epsStar : ℝ≥0∞) = (715827882 : ℝ≥0) / 1073741824 := by
  apply secondPrime_threshold_of_head_cover
  intro u fam G hG hsize
  let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  have hc : 2147483648 < fam.G.card := by
    have hs := Finset.card_le_card hG
    omega
  obtain ⟨Q, f, hQ, hs, hi, hd, hy, hw, _, hpopulation, hproper⟩ :=
    actual_cubic fam φ (by decide : 715827884 < p) (Fintype.card_fin _)
      (TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)) hc
  exact False.elim ((by decide : ¬1431655603 ≤ 1431655602)
    (hpopulation.trans (h u Q f hQ hs hi hd hy hw hproper)))

end Named

#print axioms secondPrime_threshold_of_simple_cubic
#print axioms actual_cubic
#print axioms common_chart
end ArkLib.ProximityGap.Frontier.SecondPrimeCubicWitness
