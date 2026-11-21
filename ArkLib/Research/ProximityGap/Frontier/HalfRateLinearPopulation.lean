/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalLinearComponent
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount
import ArkLib.Research.ProximityGap.Frontier.WeightedSylvesterDegree

/-! # Value-linear components in the half-rate interpolation bound -/

open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.HalfRateLinearPopulation
open _root_.ProximityGap.TerminalLinearComponent
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry HalfPredecessorSecantLines

variable {F K I : Type} [Field F] [Field K] [Fintype F] [DecidableEq F]
  [Fintype I] [Nonempty I] [DecidableEq I] {dom : I ↪ F} {δ : ℝ≥0}
  {u : WordStack F (Fin 2) I}

/-- Any 636 sections on an irreducible value-linear factor force every section
of the selected population onto one secant over the original field. -/
theorem secant (φ : F →+* K) (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824) (ht : 791228368 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (f : Polynomial (Polynomial K[X])) (hi : Irreducible f) (hy : f.natDegree = 1)
    (hm : WeightedSylvesterDegree.TotalDegreeLe f 58)
    (G : Finset F) (hG : G ⊆ fam.G) (hlarge : 636 ≤ G.card)
    (hr : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    ∃ l ∈ lineParameters fam, G ⊆ pointsOn fam l := by
  classical
  have degree (i : ℕ) (hh : i ≤ 58) : (f.coeff i).natDegree + i ≤ 58 := by
    by_cases he : f.coeff i = 0
    · simpa [he] using hh
    · exact hm i he
  apply secant_of_agreement_selection (d := 536870911) (m := 57) (N := 636)
    φ fam f hi hy (by simpa using degree 0 (by decide)) (by have := degree 1 (by decide); omega)
    _ G hG hlarge hr
  intro M S U hM hS off onI
  obtain ⟨hU, W, hWM, hW, htr⟩ := triple_incidence_bounds M S U 578 57 791228368
    (by decide) hM (fun z hz => ht.trans (hS z hz)) off onI
  refine ⟨W, hWM, hW, ?_⟩
  intro a ha b hb c hc
  have h := htr a ha b hb c hc
  omega

/-- A value-linear factor of scalar/value degree at most 58 carries at most
282,513,457 labels of any actual half-rate family at the specified agreement.
The domain and fields are arbitrary. -/
theorem actual_population (φ : F →+* K) (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824) (ht : 791228368 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (f : Polynomial (Polynomial K[X])) (hi : Irreducible f) (hy : f.natDegree = 1)
    (hm : WeightedSylvesterDegree.TotalDegreeLe f 58)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hr : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    G.card ≤ 282513457 := by
  classical
  by_cases hsmall : G.card < 636
  · omega
  obtain ⟨l, hl, hsub⟩ := secant φ fam hn ht f hi hy hm G hG (by omega) hr
  obtain ⟨z,hz⟩ := card_pos.mp (show 0 < G.card by omega)
  let t := ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊
  have ht' : t ≤ Fintype.card I := (fam.threshold_le z (hG hz)).trans (card_le_univ _)
  have occ := TwoLargeCoreCount.line_occupancy_le fam (t := t) (e := Fintype.card I - t)
    (by omega) rfl hl
  have hcard := card_le_card hsub
  change 791228368 ≤ t at ht
  omega

#print axioms secant
#print axioms actual_population
end ArkLib.ProximityGap.Frontier.HalfRateLinearPopulation
