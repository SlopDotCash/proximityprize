/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.UnrestrictedSectionPopulation
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorSectionBudget

/-! # Nonlinear sections of the first half-rate successor quartic -/

open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.HalfSuccessorNonlinearPopulation
open UnrestrictedSectionPopulation
open SecondPrimeCoordinateWeight HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
variable {F I : Type} [Field F] [Fintype I] [DecidableEq F]

/-- Over any field of characteristic greater than 116, at agreement 805306367,
a nonlinear component of value degree two, three or four carries at most 3940,
5756 or 7572 actual scalar witnesses, respectively. -/
theorem actual_population {p : ℕ} [CharP F p] (hp : 116 < p)
    (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I)
    (hn : Fintype.card I = 1073741824) (ht : 805306367 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 536870912 δ u) (f : F[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 14)
    (hw : weight 536870911 f ≤ 2415919100)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C z)) (fam.q z) = 0) :
    G.card ≤ f.natDegree*1838 + 22*(14-f.natDegree) := by
  classical
  rcases charge_or_singleton (d:=536870911) hp (RingHom.id F) dom (u 0) (u 1) f hi hb₂ hb₄
    htot G fam.q hroot with hcharge | hs
  · refine population_of_capacity (t:=805306367) (μ:=15) (d:=536870911) (by decide)
      (by decide) (by decide) (by decide) (RingHom.id F) dom (u 0) (u 1) f hi (by omega)
      (by omega) htot ?_ G fam.q hroot ?_
    · rw [hn]
      apply _root_.ProximityGap.HalfSuccessorSectionCapacity.strict_count _ f.natDegree _
        hb₂ hb₄ hn _ (degree_floor _ f hi.ne_zero) hw hcharge
      intro i
      exact (CanonicalQuarticSiteOrder.siteOrder_le _ _ _).trans (by
        rw [TerminalQuarticLocalization.local_degree,TerminalQuarticHessianTransport.permute_degree])
    · intro z hz
      refine ⟨by have := fam.degree_lt z (hG hz); omega, fullAgreement dom (u 0) (u 1) z (fam.q z),
        ht.trans (fam.threshold_le z (hG hz)), fun i hi => (mem_filter.mp hi).2⟩
  · omega

#print axioms actual_population
end ArkLib.ProximityGap.Frontier.HalfSuccessorNonlinearPopulation
