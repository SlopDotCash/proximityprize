/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyNegClosedLower
import ArkLib.Data.CodingTheory.ProximityGap.EnergyExcessCore
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The (2)⟺(3) unification: minimal energy ⟺ Sidon-mod-negation (#389)

This completes the equivalence between two of the seven forms of the δ* wall (issue #389 unifying
map): the **additive energy at its floor** and the **Sidon-mod-negation** property.

The forward direction `SidonModNeg G → E(G) = 3n²−3n` is `additiveEnergy_eq_of_sidonModNeg`. This
file adds the **converse** and packages both as an iff:

> **`sidonModNeg_of_additiveEnergy_eq_energyIff`** — for negation-closed `G ∌ 0` over a field with `2 ≠ 0`,
> `E(G) = 3n²−3n  ⟹  SidonModNeg G`.
> **`energyExcess_eq_zero_iff_sidonModNeg`** — `energyExcess G = 0 ↔ SidonModNeg G`.

The converse is the **equality case** of the minimal-energy lower bound: `E(G) = ∑∑ repCount(a+b) ≥
∑∑ structured = 3n²−3n` with `structured(a,b) ≤ repCount(a+b)` pointwise (`structured_le_repCount`);
equality of the sums forces pointwise equality (`Finset.sum_eq_sum_iff_of_le`), i.e. for every
`a,b ∈ G` with `a+b ≠ 0` the representations of `a+b` are *exactly* `{a,b}` — which is precisely
`SidonModNeg`. So the additive defect `D(G) = energyExcess G` vanishes **iff** `G` is Sidon-mod-neg,
making "energy at the floor" and "no nontrivial parallelogram" one machine-checked statement.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Converse of `additiveEnergy_eq_of_sidonModNeg`.** If the additive energy attains its
negation-closed floor `3n²−3n`, then `G` is Sidon-mod-negation. -/
theorem sidonModNeg_of_additiveEnergy_eq_energyIff {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hE : additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card) :
    SidonModNeg G := by
  classical
  have hne0 : ∀ x ∈ G, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  -- the structured double-sum equals the floor (verbatim from `additiveEnergy_ge_of_negClosed`)
  have hinner : ∀ a ∈ G,
      (∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card)) = 3 * G.card - 3 := by
    intro a ha
    have ha0 : a ≠ 0 := hne0 a ha
    have hna : -a ∈ G := hneg a ha
    have haa : a + a ≠ 0 := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have ha_ne : a ≠ -a := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have hna' : -a ∈ G := hneg a ha
    have hge2 : 2 ≤ G.card := by
      have hsub : ({a, -a} : Finset F) ⊆ G := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha
        · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hna'
      calc 2 = ({a, -a} : Finset F).card := (Finset.card_pair ha_ne).symm
        _ ≤ G.card := Finset.card_le_card hsub
    rw [Finset.sum_ite]
    have hf0 : G.filter (fun b => a + b = 0) = {-a} := by
      ext b; rw [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => by linear_combination h.2, fun h => ⟨h ▸ hna, by rw [h]; ring⟩⟩
    rw [hf0, Finset.sum_const, Finset.card_singleton, one_smul]
    set S := G.filter (fun b => ¬ a + b = 0) with hSdef
    have haS : a ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨ha, haa⟩
    have hScard : S.card = G.card - 1 := by
      have htot := Finset.card_filter_add_card_filter_not (s := G) (fun b => a + b = 0)
      rw [hf0, Finset.card_singleton] at htot
      rw [hSdef]; omega
    rw [← Finset.add_sum_erase S _ haS]
    have hfa : ({a, a} : Finset F).card = 1 := by simp
    have hrest : (∑ b ∈ S.erase a, ({a, b} : Finset F).card) = (S.card - 1) * 2 := by
      have hc : ∀ b ∈ S.erase a, ({a, b} : Finset F).card = 2 := fun b hb =>
        Finset.card_pair (Ne.symm (Finset.mem_erase.mp hb).1)
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_erase_of_mem haS, smul_eq_mul]
    rw [hfa, hrest, hScard]
    omega
  have hss : (∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card))
      = 3 * G.card ^ 2 - 3 * G.card := by
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    rcases Nat.eq_zero_or_pos G.card with h | h
    · rw [h]; simp
    · have h1 : 3 ≤ 3 * G.card := by omega
      have hsq : G.card ≤ G.card ^ 2 := Nat.le_self_pow (by norm_num) _
      have h2' : 3 * G.card ≤ 3 * G.card ^ 2 := by omega
      zify [h1, h2']; ring
  -- sum equality ⟹ pointwise equality structured = repCount
  have hsum_eq : (∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card))
      = ∑ a ∈ G, ∑ b ∈ G, repCount G (a + b) := by
    rw [hss]; exact hE.symm
  have houter := (Finset.sum_eq_sum_iff_of_le (fun a ha =>
    Finset.sum_le_sum (fun b hb => structured_le_repCount hneg ha hb))).mp hsum_eq
  have hpt : ∀ a ∈ G, ∀ b ∈ G,
      (if a + b = 0 then G.card else ({a, b} : Finset F).card) = repCount G (a + b) :=
    fun a ha => (Finset.sum_eq_sum_iff_of_le
      (fun b hb => structured_le_repCount hneg ha hb)).mp (houter a ha)
  -- the Sidon-mod-neg conclusion
  intro a ha b hb c hc d hd habcd
  by_cases hab0 : a + b = 0
  · exact Or.inr (Or.inr hab0)
  · have hpt' := hpt a ha b hb
    rw [if_neg hab0] at hpt'
    set RB := G.filter (fun y => (a + b) - y ∈ G) with hRB
    have hsubset : ({a, b} : Finset F) ⊆ RB := by
      intro x hx
      rw [hRB, Finset.mem_filter]
      rcases Finset.mem_insert.mp hx with hxa | hxb
      · rw [hxa]; exact ⟨ha, by rw [show a + b - a = b by ring]; exact hb⟩
      · rw [Finset.mem_singleton] at hxb; rw [hxb]
        exact ⟨hb, by rw [show a + b - b = a by ring]; exact ha⟩
    have heq : ({a, b} : Finset F) = RB :=
      Finset.eq_of_subset_of_card_le hsubset (le_of_eq hpt'.symm)
    have hcRB : c ∈ RB := by
      rw [hRB, Finset.mem_filter]
      exact ⟨hc, by rw [show a + b - c = d by linear_combination habcd]; exact hd⟩
    rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hcRB
    rcases hcRB with hca | hcb
    · exact Or.inl ⟨hca.symm, by linear_combination habcd + hca⟩
    · exact Or.inr (Or.inl ⟨by linear_combination habcd + hcb, hcb.symm⟩)

/-- **The (2)⟺(3) iff: the additive defect vanishes iff `G` is Sidon-mod-negation.** -/
theorem energyExcess_eq_zero_iff_sidonModNeg {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    energyExcess G = 0 ↔ SidonModNeg G := by
  constructor
  · intro hz
    have hge := additiveEnergy_ge_of_negClosed h2 h0 hneg
    have hE : additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card := by
      have := additiveEnergy_eq_min_add_excess h2 h0 hneg
      rw [hz, add_zero] at this; exact this
    exact sidonModNeg_of_additiveEnergy_eq_energyIff h2 h0 hneg hE
  · intro hS
    have hE := additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS
    unfold energyExcess; omega

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg
