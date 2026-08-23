/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# THE ADDITIVE-ENERGY LOWER BOUND — Sidon-mod-negation is the MINIMUM (#389)

`AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg` shows a Sidon-modulo-negation set has
additive energy *exactly* `3|G|² − 3|G|`.  This file proves the matching **lower bound**: *every*
negation-closed `G ∌ 0` in characteristic `≠ 2` has `E(G) ≥ 3|G|² − 3|G|` (`additiveEnergy_ge`).
So the char-0 value `3|G|² − 3|G|` is the **minimum** additive energy over negation-closed sets,
attained exactly at the Sidon-modulo-negation sets.  The bound is unconditional (no Sidon hypothesis):
the trivial coincidences (pair-matches and zero-sums) alone force `≥ 3|G|² − 3|G|`, since each pair
`{a,b}` always represents `a+b` (`repCount_ge_structured`) and the structural inner sum is
`3|G| − 3` (`structuredInner_eq`).  Axiom-clean.  Issue #389.
-/

open Finset ArkLib.ProximityGap.AdditiveEnergyRepBound
namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- The **structural inner sum** (unconditional, no Sidon hypothesis): for a negation-closed
`G ∌ 0` in char `≠ 2` and `a ∈ G`, `∑_{b∈G} (if a+b=0 then |G| else |{a,b}|) = 3|G| − 3`. -/
theorem structuredInner_eq {G : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) {a : F} (ha : a ∈ G) :
    (∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card)) = 3 * G.card - 3 := by
  classical
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hna : -a ∈ G := hneg a ha
  have haa : a + a ≠ 0 := fun h =>
    ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
  have ha_ne : a ≠ -a := fun h =>
    ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
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
  have hge2 : 2 ≤ G.card := by
    have hsub : ({a, -a} : Finset F) ⊆ G := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact ha
      · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hna
    calc 2 = ({a, -a} : Finset F).card := (Finset.card_pair ha_ne).symm
      _ ≤ G.card := Finset.card_le_card hsub
  omega

/-- Pointwise: the representation count is at least the structural value (negation-closure). -/
theorem repCount_ge_structured {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) {a b : F}
    (ha : a ∈ G) (hb : b ∈ G) :
    (if a + b = 0 then G.card else ({a, b} : Finset F).card) ≤ repCount G (a + b) := by
  classical
  by_cases hab : a + b = 0
  · rw [if_pos hab, hab, repCount_zero_eq_card hneg]
  · rw [if_neg hab]
    unfold repCount
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with hxa | hxb
    · rw [hxa]; exact ⟨ha, by rw [show a + b - a = b by ring]; exact hb⟩
    · rw [hxb]; exact ⟨hb, by rw [show a + b - b = a by ring]; exact ha⟩

/-- **THE ADDITIVE-ENERGY LOWER BOUND — Sidon-mod-negation is the *minimum* energy.**  Every
negation-closed `G ∌ 0` in characteristic `≠ 2` has `E(G) ≥ 3|G|² − 3|G|`, the char-0 value, with
equality iff `G` is Sidon-modulo-negation (`additiveEnergy_eq_of_sidonModNeg`).  The matching lower
bound to that equality. -/
theorem additiveEnergy_ge {G : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    3 * G.card ^ 2 - 3 * G.card ≤ additiveEnergy G := by
  classical
  have key : (∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card))
      ≤ additiveEnergy G := by
    unfold additiveEnergy
    exact Finset.sum_le_sum fun a ha =>
      Finset.sum_le_sum fun b hb => repCount_ge_structured hneg ha hb
  have hval : (∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card))
      = 3 * G.card ^ 2 - 3 * G.card := by
    rw [Finset.sum_congr rfl fun a ha => structuredInner_eq h2 h0 hneg ha,
      Finset.sum_const, smul_eq_mul]
    rcases Nat.eq_zero_or_pos G.card with h | h
    · rw [h]; simp
    · have h1 : 3 ≤ 3 * G.card := by omega
      have hsq : G.card ≤ G.card ^ 2 := Nat.le_self_pow (by norm_num) _
      zify [h1, show 3 * G.card ≤ 3 * G.card ^ 2 by omega]; ring
  rw [← hval]; exact key

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.structuredInner_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_ge
