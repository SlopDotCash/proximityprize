/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.PrimitiveIntegralSectionChart
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicPopulation

/-! # An integral chart for the actual received family

The coordinate change uses the weight attained by the original factor. The
geometric scalar labels embed without collisions even when the ground family
is defined over a smaller field.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.PopulatedCubicChart
open SecondPrimeActualPopulations SecondPrimeCoordinateWeight IntegralSectionChart
open TerminalQuarticLocalization TerminalQuarticHessianTransport

variable {F k I : Type} [Field F] [DecidableEq F] [Field k] [Infinite k] [Fintype I]
    {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- A populated production cubic yields one center avoiding any prescribed
sites and a large gcd for every pair of nonzero chart polar resultants. -/
theorem select_inequality (fam : Family dom δ u) (φ : F →+* k) (p₃ : (3:k) ≠ 0)
    (f : k[X][X][X]) (hi : Irreducible f) (hf : f.natDegree=3)
    (hw : weight 67108863 f ≤ 290805098) (ht : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (sites : Finset k) :
    201326589 ≤ weight 67108863 f ∧ ∃ r ∉ sites,
      let Fraw := chart r (weight 67108863 f) 67108863 (orient f)
      ∀ c₁ c₂ : k, IntegralOrdinaryPolars.polarResultant Fraw (C c₁) ≠ 0 →
        IntegralOrdinaryPolars.polarResultant Fraw (C c₂) ≠ 0 →
        let g := OrdinaryPolarGcdBudget.genericDegree (IntegralOrdinaryPolars.polarResultant Fraw (C c₁))
          (IntegralOrdinaryPolars.polarResultant Fraw (C c₂))
        ((population fam φ f).card-161)*(2*(weight 67108863 f-67108863)-g) ≤
          390*(6*weight 67108863 f-9*67108863-3-g) := by
  classical
  let M := population fam φ f
  let e : F ↪ k := ⟨φ,φ.injective⟩
  let G := M.map e
  let q := Function.extend e (fun z => (fam.q z).map φ) (fun _ => 0)
  have hq (z : F) : q (e z) = (fam.q z).map φ := e.injective.extend_apply _ _ _
  obtain ⟨hprof,_⟩ := PrimitiveIntegralSectionChart.weight_profile f hi.ne_zero 67108863
  have hraw (j : ℕ) (hj : f.coeff j ≠ 0) : (orient f).coeff j ≠ 0 := by
    change (permute f).coeff j ≠ 0
    rw [permute_coeff]
    simpa only [map_zero] using Bivariate.swap.injective.ne hj
  have top : f.coeff 3 ≠ 0 := hf ▸ leadingCoeff_ne_zero.mpr hi.ne_zero
  have lower : 201326589 ≤ weight 67108863 f := by have := hprof 3 (hraw 3 top); omega
  refine ⟨lower,?_⟩
  obtain ⟨S,r,_,_,hr,_,_,_,hg⟩ := production_chart_inequality p₃ f hi hf _ lower (by
    intro j hj
    rw [← (orient_profile f j).1]
    exact hprof j (hraw j hj)) ht G sites q (by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hz
    rw [hq]
    exact natDegree_map_le.trans (by have := fam.degree_lt a (mem_filter.mp ha).1; omega)) (by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hz
    rw [hq]
    exact (mem_filter.mp ha).2) (RingHom.id k) ∅ (by simp)
  refine ⟨r,hr,?_⟩
  simpa only [G,Finset.card_map] using hg

/-- At the terminal cutoff the polar degree defect is at most 201. -/
theorem select (fam : Family dom δ u) (φ : F →+* k) (p₃ : (3:k) ≠ 0)
    (f : k[X][X][X]) (hi : Irreducible f) (hf : f.natDegree=3)
    (hw : weight 67108863 f ≤ 290805098) (ht : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (hp : 1431655733 ≤ (population fam φ f).card) (sites : Finset k) :
    201326589 ≤ weight 67108863 f ∧ ∃ r ∉ sites,
      let Fraw := chart r (weight 67108863 f) 67108863 (orient f)
      ∀ c₁ c₂ : k, IntegralOrdinaryPolars.polarResultant Fraw (C c₁) ≠ 0 →
        IntegralOrdinaryPolars.polarResultant Fraw (C c₂) ≠ 0 →
        2*(weight 67108863 f-67108863) ≤ OrdinaryPolarGcdBudget.genericDegree
          (IntegralOrdinaryPolars.polarResultant Fraw (C c₁))
          (IntegralOrdinaryPolars.polarResultant Fraw (C c₂)) + 201 := by
  obtain ⟨hl,r,hr,hg⟩ := select_inequality fam φ p₃ f hi hf hw ht sites
  refine ⟨hl,r,hr,?_⟩
  dsimp only at hg ⊢
  intro c₁ c₂ h₁ h₂
  have H := hg c₁ c₂ h₁ h₂
  have hmin : 1342177085 ≤ (population fam φ f).card-161 := by omega
  have h := (Nat.mul_le_mul_right _ hmin).trans H
  omega

#print axioms select
end ArkLib.ProximityGap.Frontier.PopulatedCubicChart
