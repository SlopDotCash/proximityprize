/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeLinearSaturation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicWeightBound
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticWeightBound
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount

/-! # Geometric obstructions that remain at the second-prime predecessor

Every large affine head in the population split contains two distinct selected scalars.
This identifies it with a genuine secant of the family, allowing the terminal counting
theorem to rule out the entire few-head alternative.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeNonlinearObstruction

open Finset Polynomial SecondPrimeActualPopulations HalfPredecessorSecantLines
open _root_.ProximityGap.TerminalCollinearHeadCount
open scoped NNReal

variable {I F K : Type} [Fintype I] [Nonempty I] [Field F] [Finite F]
  [DecidableEq F] [Field K] {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

set_option maxHeartbeats 1000000 in
-- Checking the dependent secant-family identities expands large finite-cardinality expressions.
/-- At 715827881 errors, exceeding the budget produces a populous irreducible component.
Its value degree is two, three or four. The cubic and quartic also satisfy their terminal weight bounds. -/
theorem actual_factor (fam : Family dom δ u) (φ : F →+* K) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (hbig : 2147483648 < fam.G.card) :
    ∃ Q : Factor K, Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      ∃ f : Factor K, Irreducible f ∧ f ∣ Q ∧
        ((f.natDegree = 4 ∧ 2147483615 ≤ (population fam φ f).card ∧
           SecondPrimeCoordinateWeight.weight 67108863 f ≤ 302954072) ∨
         (f.natDegree = 3 ∧ 1431655733 ≤ (population fam φ f).card ∧
           SecondPrimeCoordinateWeight.weight 67108863 f ≤ 290805098) ∨
         (f.natDegree = 2 ∧ 4128 < (population fam φ f).card)) := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨Q,hQ,shape,fac | ⟨H,_,h4,heavy,cover⟩⟩ :=
    SecondPrimeLinearSaturation.actual_reduction fam φ hn ht.ge hbig
  · obtain ⟨f, hf, hdiv, ⟨h4, hpop⟩ | ⟨h3, hpop⟩ | h2⟩ := fac
    · refine ⟨Q,hQ,shape,f,hf,hdiv,Or.inl ⟨h4,hpop,?_⟩⟩
      apply SecondPrimeQuarticWeightBound.actual_quartic_weight φ dom δ u hn ht.ge fam Q f hQ hdiv
        hf h4 (fun j i a h => (shape j i a h).2.1) (population fam φ f)
        (filter_subset _ _) (lt_of_lt_of_le (by decide) hpop)
      exact fun z hz => (mem_filter.mp hz).2
    · refine ⟨Q,hQ,shape,f,hf,hdiv,Or.inr (Or.inl ⟨h3,hpop,?_⟩)⟩
      apply SecondPrimeCubicWeightBound.actual_cubic_weight φ dom δ u hn ht.ge fam Q f hQ hdiv
        hf h3 (fun j i a h => (shape j i a h).2.1) (population fam φ f)
        (filter_subset _ _) (lt_of_lt_of_le (by decide) hpop)
      exact fun z hz => (mem_filter.mp hz).2
    · exact ⟨Q,hQ,shape,f,hf,hdiv,Or.inr (Or.inr h2)⟩
  have on (p : LineParameter F) : carried fam p = pointsOn fam p := rfl
  simp_rw [on] at heavy cover
  have belongs : H ⊆ lineParameters fam := by
    intro p hp
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (lt_trans (by decide : 1 < 512)
      (heavy p hp).2.1)
    rw [← secantParameter_eq_of_mem_pointsOn fam p ha hb hab]
    exact secantParameter_mem_lineParameters fam (pointsOn_subset_G fam p ha)
      (pointsOn_subset_G fam p hb) hab
  have sub : H.biUnion (pointsOn fam) ⊆ fam.G := by
    intro z hz
    obtain ⟨p, _, hz⟩ := mem_biUnion.mp hz
    exact pointsOn_subset_G fam p hz
  have total : fam.G.card ≤ (H.biUnion (pointsOn fam)).card + 4*4128 + 34 := cover
  have few : (fam.G \ H.biUnion (pointsOn fam)).card ≤ 16546 := by
    rw [card_sdiff_of_subset sub]
    omega
  have bound := selected_card_of_few_heads fam fam.G (subset_refl _) hn rfl
    (e := 715827881) (by decide) (by decide) ht H belongs h4 (fun p hp => (heavy p hp).2.1) few
  omega

#print axioms actual_factor
end ArkLib.ProximityGap.Frontier.SecondPrimeNonlinearObstruction
