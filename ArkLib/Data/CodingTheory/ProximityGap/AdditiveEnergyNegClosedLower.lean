/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# The unconditional minimal-energy LOWER bound (#389)

The sibling's `additiveEnergy_eq_of_sidonModNeg` shows `E(G) = 3n²−3n` *when `G` is
Sidon-modulo-negation*.  This file proves the matching **unconditional lower bound** for
*every* negation-closed set (in particular every NTT domain `μ_n`, `−1 ∈ μ_n`):

> **`additiveEnergy_ge_of_negClosed`** — for `0 ∉ G`, `2 ≠ 0`, `G` negation-closed,
> `3n² − 3n ≤ E(G)`.

The mechanism: each `repCount G (a+b)` is at least the *structured* value
(`|G|` if `a+b=0`, else `|{a,b}|`), because `a` and `b` themselves witness
representations of `a+b`; and the structured double-sum equals `3n²−3n` unconditionally
(the same count the sibling evaluates).

**Consequence.**  `E(μ_n)` is *bracketed*: `3n²−3n ≤ E(μ_n)`, with equality iff `μ_n`
is Sidon-modulo-negation.  So the entire `#389` wall is *exactly* the gap on the **upper**
side — the non-Sidon **excess** `E(μ_n) − (3n²−3n) ≥ 0`, the multiplicative–additive
interaction that the Stepanov/sum-product bound must control.  The lower side is now
closed unconditionally; only the excess remains open.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Per-term structured lower bound.**  For `a, b ∈ G` (negation-closed), the
representation count of `a+b` is at least its structured value: `|G|` if `a+b=0` (the
negation pairing), else `|{a,b}|` (since `a` and `b` each witness a representation). -/
theorem structured_le_repCount {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G)
    {a b : F} (ha : a ∈ G) (hb : b ∈ G) :
    (if a + b = 0 then G.card else ({a, b} : Finset F).card) ≤ repCount G (a + b) := by
  split_ifs with hab
  · rw [hab, repCount_zero_eq_card hneg]
  · rw [repCount]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with hxa | hxb
    · rw [hxa]
      refine ⟨ha, ?_⟩
      have h : a + b - a = b := by ring
      rw [h]; exact hb
    · rw [hxb]
      refine ⟨hb, ?_⟩
      have h : a + b - b = a := by ring
      rw [h]; exact ha

/-- **The unconditional minimal-energy lower bound: `3n² − 3n ≤ E(G)`** for every
negation-closed `G` with `0 ∉ G`, `2 ≠ 0`. -/
theorem additiveEnergy_ge_of_negClosed {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    3 * G.card ^ 2 - 3 * G.card ≤ additiveEnergy G := by
  classical
  have hne0 : ∀ x ∈ G, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  -- the structured double-sum equals 3n²−3n (unconditional count; same as the sibling's)
  have hinner : ∀ a ∈ G,
      (∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card)) = 3 * G.card - 3 := by
    intro a ha
    have ha0 : a ≠ 0 := hne0 a ha
    have hna : -a ∈ G := hneg a ha
    have haa : a + a ≠ 0 := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have ha_ne : a ≠ -a := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have hge2 : 2 ≤ G.card := by
      have hsub : ({a, -a} : Finset F) ⊆ G := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha
        · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hna
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
  -- E = Σ Σ repCount(a+b) ≥ Σ Σ structured = 3n²−3n
  calc 3 * G.card ^ 2 - 3 * G.card
      = ∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card) := hss.symm
    _ ≤ ∑ a ∈ G, ∑ b ∈ G, repCount G (a + b) :=
        Finset.sum_le_sum fun a ha =>
          Finset.sum_le_sum fun b hb => structured_le_repCount hneg ha hb
    _ = additiveEnergy G := rfl

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_ge_of_negClosed
