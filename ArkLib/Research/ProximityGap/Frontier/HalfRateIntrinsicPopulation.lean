/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.UnrestrictedSectionPopulation
import ArkLib.Research.ProximityGap.Frontier.HalfRateJetCapacity

/-! # Unrestricted nonlinear section populations at the half-rate predecessor -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset Module
namespace ArkLib.ProximityGap.Frontier.HalfRateIntrinsicPopulation
open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension SecondPrimeCoordinateWeight
open TerminalQuarticHessianTransport TerminalQuarticLocalization IntrinsicReceivedSections
open JetMultiplierGraph QuarticIntrinsicAuxiliary IntrinsicCubicQuotientWindow
open IntrinsicCubicPopulation (originalOrder)
private abbrev s : ℕ := 536797744
private abbrev J : ℕ := 2523
private abbrev d : ℕ := 536870911
variable {K F I : Type} [Field K] [Field F] [Fintype I]

/-- For every actual nonlinear component through degree four satisfying the reverse-Hessian
intersection inequality, the original selected labels use at most half the block length
per unit of value degree. The nonmultiple auxiliary and its section roots are constructed. -/
theorem population_of_charge (φ : F →+* K) (dom : I ↪ K) (u v : I → K)
    (hn : Fintype.card I = 1073741824) (f : K[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 58) (hw : weight d f ≤ 3*791228368-1)
    (hR : (∑ i, let r := originalOrder f (dom i) (u i) (v i); r*(3*r-2)) +
      3*f.natDegree^2*d ≤ (6*f.natDegree-2)*weight d f)
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0)
    (hfit : ∀ z ∈ G, (q z).natDegree ≤ d ∧ ∃ H : Finset I, 791228368 ≤ H.card ∧
      ∀ i ∈ H, (q z).eval (dom i) = u i+φ z*v i) : G.card+5048 ≤ f.natDegree*536870912 := by
  have hcap := UnrestrictedSectionPopulation.population_of_capacity
    (s:=s) (J:=J) (t:=791228368) (μ:=1712) (by decide) (by decide) (by decide)
    (by decide) φ dom u v f hi (by omega) (by omega) htot (by
      rw [hn]
      refine _root_.ProximityGap.HalfRateJetCapacity.strict_count
        (fun i => originalOrder f (dom i) (u i) (v i)) f.natDegree _ hb₂ hb₄ hn ?_
        (UnrestrictedSectionPopulation.degree_floor d f hi.ne_zero) hw hR
      intro i
      exact (CanonicalQuarticSiteOrder.siteOrder_le _ _ _).trans (by
        rw [local_degree,permute_degree])) G q hroot hfit
  interval_cases hy : f.natDegree <;> dsimp [s,J] at hcap ⊢ <;> omega

/-- Every nonlinear component of the actual half-rate interpolant saves at least 5,048
labels from its per-degree allocation. The proper reverse Hessian and geometric-line
branches are both included. -/
theorem population {p : ℕ} [CharP K p] (hp : 468 < p) (φ : F →+* K) (dom : I ↪ K)
    (u v : I → K) (hn : Fintype.card I = 1073741824) (f : K[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 58) (hw : weight d f ≤ 3*791228368-1)
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0)
    (hfit : ∀ z ∈ G, (q z).natDegree ≤ d ∧ ∃ H : Finset I, 791228368 ≤ H.card ∧
      ∀ i ∈ H, (q z).eval (dom i) = u i+φ z*v i) : G.card+5048 ≤ f.natDegree*536870912 := by
  rcases UnrestrictedSectionPopulation.charge_or_singleton (d:=d) hp φ dom u v f hi
    hb₂ hb₄ htot G q hroot with hcharge | hs
  · exact population_of_charge φ dom u v hn f hi hb₂ hb₄ htot hw hcharge G q hroot hfit
  · omega

open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open scoped NNReal

/-- The cap on an original MCA family, after lifting its received pair and sections to
the extension field. All hypotheses on its agreement sets come from the family. -/
theorem actual_population [DecidableEq F] {p : ℕ} [CharP K p] (hp : 468 < p)
    (φ : F →+* K) (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I)
    (hn : Fintype.card I = 1073741824) (ht : 791228368 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 536870912 δ u) (f : K[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 58) (hw : weight d f ≤ 3*791228368-1)
    (G : Finset F) (hsub : G ⊆ fam.G)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    G.card+5048 ≤ f.natDegree*536870912 := by
  let dk := dom.trans ⟨φ,φ.injective⟩
  apply population hp φ dk (fun i => φ (u 0 i)) (fun i => φ (u 1 i)) hn f hi hb₂ hb₄
    htot hw G (fun z => (fam.q z).map φ) hroot
  intro z hz
  refine ⟨natDegree_map_le.trans (by have := fam.degree_lt z (hsub hz); unfold d; omega),
    fullAgreement dom (u 0) (u 1) z (fam.q z), ht.trans (fam.threshold_le z (hsub hz)), ?_⟩
  intro i hi
  change ((fam.q z).map φ).eval (φ (dom i)) = _
  rw [eval_map_apply]
  exact (congrArg φ (Finset.mem_filter.mp hi).2).trans (by simp only [map_add,map_mul])

#print axioms population_of_charge
#print axioms population
#print axioms actual_population
end ArkLib.ProximityGap.Frontier.HalfRateIntrinsicPopulation
