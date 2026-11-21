/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeNonlinearObstruction
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualQuarticCap
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticPopulation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeReverseChart

/-! # The sole remaining component at the second-prime predecessor

An over-budget family would give an irreducible cubic of large population and restricted
weight that intersects its scalar Hessian properly. Both Hessian branches of a quartic,
all quadratic components, and the linear/head configurations are already excluded.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeProperCubic

open Finset Polynomial SecondPrimeActualPopulations SecondPrimeScalarChart
open MovingCubicVanishingBranch CanonicalQuarticSiteOrder
open scoped NNReal
variable {I F K : Type} [Fintype I] [Nonempty I] [Field F] [Finite F] [DecidableEq F]
  [Field K] [IsAlgClosed K] {p : ℕ} [CharP K p]
  {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- At the named predecessor, exceeding 2n genuine bad scalars forces a populous proper cubic. -/
theorem actual_cubic (fam : Family dom δ u) (φ : F →+* K) (hp : 715827884 < p)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (hbig : 2147483648 < fam.G.card) :
    ∃ (Q f : Factor K), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      Irreducible f ∧ f ∣ Q ∧ f.natDegree = 3 ∧ 1431655733 ≤ (population fam φ f).card ∧
      SecondPrimeCoordinateWeight.weight 67108863 f ≤ 290805098 ∧
      ¬ genericEquation (scalarChart f) ∣ genericEquation (scalarFieldHessian (scalarChart f)) := by
  classical
  obtain ⟨Q, hQ, hs, f, hi, hdiv, alt⟩ :=
    SecondPrimeNonlinearObstruction.actual_factor fam φ hn ht hbig
  have tri (j i a : ℕ) (h : ((Q.coeff j).coeff i).coeff a ≠ 0) : i + j ≤ 34 :=
    (hs j i a h).2.1
  have cap (hl : 2 ≤ f.natDegree) (hu : f.natDegree ≤ 4)
      (h : genericEquation (scalarChart f) ∣ genericEquation (scalarFieldHessian (scalarChart f))) :
      (population fam φ f).card ≤ 1 := by
    exact SecondPrimeReverseChart.divisible_label_cap φ (p := p) (by omega) f hi hl hu
      (SecondPrimeSectionResultant.factor_triangle hQ hdiv tri) h (population fam φ f)
      (fun z => (fam.q z).map φ) (fun _ hz => (mem_filter.mp hz).2)
  rcases alt with ⟨hd, hpop, _⟩ | ⟨hd, hpop, hw⟩ | ⟨hd, hpop⟩
  · by_cases h : genericEquation (scalarChart f) ∣
        genericEquation (scalarFieldHessian (scalarChart f))
    · have hsmall := cap (by omega) (by omega) h
      omega
    · have hsmall := SecondPrimeActualQuarticCap.population_cap fam φ hn ht.ge Q f hQ hdiv
        hi hd tri h
      omega
  · refine ⟨Q, f, hQ, hs, hi, hdiv, hd, hpop, hw, fun h => ?_⟩
    have hsmall := cap (by omega) (by omega) h
    omega
  · have hchar : ringChar K = p := ringChar.eq K p
    have h2 : (2 : K) ≠ 0 := by
      intro hz
      have h := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast hz)
      have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
    have hsmall := SecondPrimeQuadraticPopulation.population_le fam φ f Q hi hd hQ hdiv hs hn
      ht.ge h2 (Or.inl (by omega))
    omega

#print axioms actual_cubic
end ArkLib.ProximityGap.Frontier.SecondPrimeProperCubic
