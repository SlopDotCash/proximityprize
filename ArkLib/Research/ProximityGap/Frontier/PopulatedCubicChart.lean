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
  obtain ⟨S,r,_,_,hr,_,_,_,hg⟩ := production_chart p₃ f hi hf _ lower hw (by
    intro j hj
    rw [← (orient_profile f j).1]
    exact hprof j (hraw j hj)) ht G sites (by
      change 1342177249 ≤ (M.map e).card
      rw [card_map]
      exact le_trans (by decide : 1342177249 ≤ 1431655733) hp) q (by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hz
    rw [hq]
    exact natDegree_map_le.trans (by have := fam.degree_lt a (mem_filter.mp ha).1; omega)) (by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hz
    rw [hq]
    exact (mem_filter.mp ha).2) (RingHom.id k) ∅ (by simp)
  exact ⟨r,hr,hg⟩

#print axioms select
end ArkLib.ProximityGap.Frontier.PopulatedCubicChart
