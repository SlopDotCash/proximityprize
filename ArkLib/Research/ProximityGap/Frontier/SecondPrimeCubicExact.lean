/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ChartFiberHessian
import ArkLib.Research.ProximityGap.Frontier.PopulatedCubicChart
import ArkLib.Research.ProximityGap.Frontier.OriginalCubicResultants
import ArkLib.Research.ProximityGap.Frontier.IntegralPolarDescent
import ArkLib.Research.ProximityGap.Frontier.ReceivedOrderChartFamily

/-! # The second production prime at rate one sixteenth

The same original factor accounts for the section population, the two polar
resultants in the primitive reciprocal chart and the scalar Hessian at
every received site. Its intrinsic interpolation space excludes the last
possible over-budget population.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal ENNReal Differential
namespace ArkLib.ProximityGap.Frontier.SecondPrimeCubicExact
open IntegralSectionChart TerminalQuarticLocalization TerminalQuarticHessianTransport
open SecondPrimeCoordinateWeight SecondPrimeActualPopulations IntrinsicCubicPopulation

variable {k : Type} [Field k] [Infinite k]
local instance : Differential k[X] := MovingCubicVanishingBranch.coordinateDifferential
local instance : Differential (RatFunc k) := CanonicalQuarticSiteOrder.scalarFieldDifferential k
local instance : Differential (RatFunc k)[X] := ImplicitDerivativeBidegree.coefficientDifferential

/-- Both resultants are nonzero on the actual chart used for the polar gcd. -/
theorem chart_resultants (f : k[X][X][X]) (hi : Irreducible f) (hy : f.natDegree=3)
    (h₃ : (3:k) ≠ 0) (hp : Proper f) (a : k) (d : ℕ) :
    let G := localPlane (chart a (weight d f) d (orient f))
    G.resultant G.derivative 3 3 ≠ 0 ∧ G.resultant (ScalarHessianLocalOrder.hessian G) 3 7 ≠ 0 := by
  let m := algebraMap k[X] (RatFunc k)
  let F := localPlane (orient f)
  let G := localPlane (chart a (weight d f) d (orient f))
  obtain ⟨hv,hh⟩ := OriginalCubicResultants.nonzero f hi hy h₃ hp
  apply ChartFiberHessian.transfer RatFunc.C OriginalCubicResultants.constant F G a (weight d f) d
    ((local_degree _).trans ((permute_degree f).trans hy)) _ _ hv hh
  · intro j hj
    have hn : (orient f).coeff j ≠ 0 := fun hz => hj (by simp [F,JetMultiplierGraph.mapPlane,hz])
    have h := (PrimitiveIntegralSectionChart.weight_profile f hi.ne_zero d).1 j hn
    simp only [F,JetMultiplierGraph.mapPlane,coeff_map,coe_mapRingHom]
    exact (Nat.add_le_add_right natDegree_map_le _).trans h
  · intro j
    simp only [F,G,JetMultiplierGraph.mapPlane,coeff_map,coe_mapRingHom]
    exact PrimitiveIntegralSectionChart.map_slot m (orient f) a (weight d f) d j

/-- At the lower neighbor of the named endpoint the original sum of received
multiplicities obeys the geometric bound, with additive defect 402. -/
theorem received_budget {F I : Type} [Field F] [DecidableEq F] [Fintype I]
    {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}
    (fam : Family dom δ u) (φ : F →+* k) (p : ℕ) [CharP k p]
    (hp : 1744830589 < p) (f : k[X][X][X]) (hi : Irreducible f)
    (hy : f.natDegree = 3) (hw : weight 67108863 f ≤ 290805098)
    (ht : WeightedSylvesterDegree.TotalDegreeLe f 34) (hproper : Proper f)
    (hpop : 1431655733 ≤ (population fam φ f).card) :
    3*totalOrder φ dom u f+35*67108863 ≤ 2*Fintype.card I+16*weight 67108863 f+402 := by
  classical
  let pmap : k →+* RatFunc k := RatFunc.C
  let : CharP (RatFunc k) p := charP_of_injective_ringHom pmap.injective p
  have sm (j : ℕ) (hj : 0 < j) (hj' : j < p) : (j:k) ≠ 0 := by
    intro h
    exact hj'.not_ge (Nat.le_of_dvd hj ((CharP.cast_eq_zero_iff k p j).mp h))
  have h₃ : (3:k) ≠ 0 := sm 3 (by decide) (by omega)
  have h₂ : (2:k) ≠ 0 := sm 2 (by decide) (by omega)
  have h₂' : (2:RatFunc k) ≠ 0 := by simpa only [map_ofNat,map_zero] using pmap.injective.ne h₂
  have h₃' : (3:RatFunc k) ≠ 0 := by simpa only [map_ofNat,map_zero] using pmap.injective.ne h₃
  let dom' := dom.trans (⟨φ,φ.injective⟩ : F ↪ k)
  let sites := Finset.univ.map dom'
  obtain ⟨hl,a,ha,hg⟩ := PopulatedCubicChart.select fam φ h₃ f hi hy hw ht hpop sites
  let w := weight 67108863 f
  let C₀ := chart a w 67108863 (orient f)
  have hprim := PrimitiveIntegralSectionChart.primitive_of_original f hi (by omega) a 67108863
  obtain ⟨hval,hhes⟩ := chart_resultants f hi hy h₃ hproper a 67108863
  have hp₀ := (PrimitiveIntegralSectionChart.weight_profile f hi.ne_zero 67108863).1
  have hraw (j : ℕ) (hj : f.coeff j ≠ 0) : Bivariate.degreeX (f.coeff j)+67108863*j ≤ w := by
    rw [← (orient_profile f j).1]
    apply hp₀
    change (permute f).coeff j ≠ 0
    rw [permute_coeff]
    simpa only [map_zero] using Bivariate.swap.injective.ne hj
  obtain ⟨D,l,r,hD,hs,hsite⟩ := ReceivedOrderChartFamily.received_sites f hy.le w 67108863
    (by omega) (by decide) hraw a dom' (fun i => φ (u 0 i)) (fun i => φ (u 1 i)) (by
      intro i h
      exact ha (h ▸ Finset.mem_map_of_mem dom' (Finset.mem_univ i))) hprim
  have hbound := IntegralPolarDescent.order_budget C₀ w p hl (by dsimp [w]; omega)
    (coordinate_weight a w 67108863 (orient f) hp₀)
    (OriginalCubicResultants.chart_bounds f hy 67108863 a).1 hprim h₂' h₃' hval hhes hg D l r hsite
  change totalOrder φ dom u f ≤ ∑ α ∈ D, r α at hs
  rw [hD] at hbound
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hs) _).trans hbound

open _root_.ProximityGap
open _root_.ProximityGap.SecondPrimeCubicOnly _root_.ProximityGap.TerminalCollinearHeadCount
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
private abbrev p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev g := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact p.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The operational line-MCA supremum at the second named prime at length
2³⁰, dimension 2²⁶ and tolerance 2⁻¹²⁸. -/
theorem secondPrime_rateSixteenth :
    _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (evalCode g (2^30) (2^26-1))
      (epsStar : ℝ≥0∞) = (715827882 : ℝ≥0)/1073741824 := by
  apply secondPrime_threshold_of_received_order
  intro u fam φ Q f hQ hs hi hd hy hw hp hpop
  have ht := SecondPrimeSectionResultant.factor_triangle hQ hd (fun j i a he => (hs j i a he).2.1)
  have h := received_budget fam φ p (by decide) f hi hy hw ht hp hpop
  exact h.trans (by simp only [Fintype.card_fin]; omega)

#print axioms chart_resultants
#print axioms received_budget
#print axioms secondPrime_rateSixteenth
end ArkLib.ProximityGap.Frontier.SecondPrimeCubicExact
