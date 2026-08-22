/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.E2CharFreeLowerBound

/-!
# The char-free `r=2` floor, transferred to the moment object `rEnergy G 2` (#444, #389, #407)

The cross-step ladder (`CrossStepRungTwo`, `GaussianEnergyBoundMuNDepthTwo`, …) takes the EXACT
value `rEnergy G 2 = 3|G|²−3|G|` as a **hypothesis** `hE2`.  That value is the char-DEPENDENT
near-Sidon one, which the probes (`scripts/probes/probe_e2_excess_*.py`) show FAILS in the deep
prize regime (the additive energy strictly EXCEEDS it there).  This file transfers the char-FREE
**floor** `E2CharFree.E2_ge_three_card_sq_sub_three_card` to the in-tree moment object `rEnergy`,
so the ladder has an always-true `≥` to lean on instead of a sometimes-false `=`.

The bridge `rEnergy_two_eq_E2 : rEnergy G 2 = E2CharFree.E2 G` is a card bijection: `rEnergy G 2`
counts pairs `(v,w) ∈ (Fin 2 → G)²` with `∑v = ∑w`, and `E2CharFree.E2 G` counts quadruples
`(a,b,c,d) ∈ G⁴` with `a+b = c+d`; the map `(v,w) ↦ (v 0, v 1, w 0, w 1)` is the bijection
(`∑_{i:Fin 2} v i = v 0 + v 1`).

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389, #407.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `rEnergy G 2` as the card of a filtered product of `(Fin 2 → G)` pairs. -/
theorem rEnergy_two_eq_filter_card (G : Finset F) :
    rEnergy G 2 =
      ((Fintype.piFinset (fun _ : Fin 2 => G) ×ˢ Fintype.piFinset (fun _ : Fin 2 => G)).filter
        (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card := by
  classical
  unfold rEnergy
  rw [Finset.card_filter, Finset.sum_product]

/-- **The bridge.**  The in-tree moment object `rEnergy G 2` equals the additive-energy count
`E2CharFree.E2 G`, via the card bijection `(v,w) ↦ (v 0, v 1, w 0, w 1)`. -/
theorem rEnergy_two_eq_E2 (G : Finset F) :
    rEnergy G 2 = ArkLib.ProximityGap.E2CharFree.E2 G := by
  classical
  rw [rEnergy_two_eq_filter_card]
  unfold ArkLib.ProximityGap.E2CharFree.E2 ArkLib.ProximityGap.E2CharFree.energyQuads
  rw [Finset.card_image_of_injective _ (by
      intro x y h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4))]
  -- bijection from the (Fin 2 → G)-pair filter to the G⁴ filter
  apply Finset.card_bij
    (fun p _ => ((p.1 0, p.1 1), (p.2 0, p.2 1)))
  · -- maps into the target filter
    rintro ⟨v, w⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Fin.sum_univ_two]
      at hp ⊢
    obtain ⟨⟨hv, hw⟩, hsum⟩ := hp
    exact ⟨⟨⟨hv 0, hv 1⟩, ⟨hw 0, hw 1⟩⟩, hsum⟩
  · -- injective on the filter
    rintro ⟨v, w⟩ hp ⟨v', w'⟩ hp' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨hv0, hv1⟩, ⟨hw0, hw1⟩⟩ := heq
    refine Prod.ext ?_ ?_
    · funext i; fin_cases i
      · exact hv0
      · exact hv1
    · funext i; fin_cases i
      · exact hw0
      · exact hw1
  · -- surjective onto the target filter
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, hsum⟩ := hq
    refine ⟨(![a, b], ![c, d]), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Fin.sum_univ_two]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i; fin_cases i <;> simpa
      · intro i; fin_cases i <;> simpa
      · simpa using hsum
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The char-free `r=2` floor on the moment object.**  For a negation-closed `G` in a finite
field, `3|G|² − 3|G| ≤ rEnergy G 2` — the always-true `≥` underlying the ladder's hypothesis
`rEnergy G 2 = 3|G|²−3|G|` (which is the char-dependent UPPER half, false in the deep prize regime). -/
theorem rEnergy_two_ge_three_card_sq_sub_three_card (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) :
    3 * (G.card * G.card) - 3 * G.card ≤ rEnergy G 2 := by
  rw [rEnergy_two_eq_E2]
  exact ArkLib.ProximityGap.E2CharFree.E2_ge_three_card_sq_sub_three_card G hG

/-- **The hypothesis-free `2n²−n` floor on the moment object.**  For ANY finite `G` (no negation
closure needed), `2|G|² − |G| ≤ rEnergy G 2`, via the char-free diagonal+swap families (`T1+T2`).
Weaker than the negation-closed `3n²−3n` floor but UNCONDITIONAL — a usable `≥` on the moment
object even where negation-closure is unavailable. -/
theorem rEnergy_two_ge_two_card_sq_sub_card (G : Finset F) :
    2 * (G.card * G.card) - G.card ≤ rEnergy G 2 := by
  rw [rEnergy_two_eq_E2]
  exact ArkLib.ProximityGap.E2CharFree.E2_ge_two_card_sq_sub_card G

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_two_eq_filter_card
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_two_eq_E2
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_two_ge_three_card_sq_sub_three_card
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_two_ge_two_card_sq_sub_card
