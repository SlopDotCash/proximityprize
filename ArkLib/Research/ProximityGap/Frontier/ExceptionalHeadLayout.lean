/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ExceptionalHeadMass
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Packing the exceptional heads on any evaluation domain -/

open Finset ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ExceptionalHeadLayout

variable {F : Type} [Field F] [Fintype F] {n k r m : ℕ} [NeZero n]

/-- Pack `m` omitted roots in a block of size `k` and `r` private sites per head.
A virtual head labels every leftover site without changing the defining cores. -/
theorem mass (dom : Fin n ↪ F) (δ : ℝ≥0) (hm : m ≤ k) (hn : k + m * r ≤ n)
    (hk : k ≤ k - 1 + r) (hq : n < Fintype.card F)
    (hsize : (1 - δ) * (n : ℝ≥0) ≤ ((k - 1 + r + 1 : ℕ) : ℝ≥0))
    (hfield : (m * (n - (k - 1 + r))).choose 2 ≤ Nat.card F) :
    ((m * (n - (k - 1 + r)) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : F, ∀ x, dom x ≠ v := by
    by_contra! hs
    have hc := Fintype.card_le_of_surjective dom hs
    simp only [Fintype.card_fin] at hc
    omega
  have hkn : k ≤ n := by omega
  let a := Fin.castLEEmb (hm.trans hkn)
  let base := univ.map (Fin.castLEEmb hkn)
  let slot : Fin m × Fin r ↪ Fin n :=
    (finProdFinEquiv.toEmbedding.trans (Fin.natAddEmb k)).trans (Fin.castLEEmb hn)
  let block (i : Fin m) : Fin r ↪ Fin n :=
    ⟨fun j => slot (i, j), fun _ _ he => congrArg Prod.snd (slot.injective he)⟩
  have hnot (j : Fin m × Fin r) : slot j ∉ base := by
    intro he
    obtain ⟨b, _, hb⟩ := mem_map.mp he
    have hv := congrArg Fin.val hb
    change b.val = k + (finProdFinEquiv j).val at hv
    omega
  have ha (i : Fin m) : a i ∈ base :=
    mem_map.mpr ⟨⟨i.val, lt_of_lt_of_le i.isLt hm⟩, mem_univ _, rfl⟩
  let owner (x : Fin n) : F := if g : ∃ j, slot j = x then dom (a g.choose.1) else v
  have hslot (j : Fin m × Fin r) : owner (slot j) = dom (a j.1) := by
    have hex : ∃ z, slot z = slot j := ⟨j, rfl⟩
    simp only [owner, dite_eq_left hex]
    rw [slot.injective hex.choose_spec]
  have ho (x : Fin n) : dom x ≠ owner x := by
    by_cases hex : ∃ z, slot z = x
    · obtain ⟨z, rfl⟩ := hex
      rw [hslot]
      exact fun he => hnot z (dom.injective he ▸ ha z.1)
    · simpa only [owner, dite_eq_right hex] using hv x
  have hc (i : Fin m) : (ExceptionalHeadMass.core dom base a owner i).card = k - 1 + r := by
    have hf : (univ.filter fun x => x ∉ base ∧ owner x = dom (a i)) = univ.map (block i) := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, he⟩
        by_cases hex : ∃ z, slot z = x
        · obtain ⟨⟨j, y⟩, rfl⟩ := hex
          have hji : j = i := a.injective (dom.injective ((hslot (j, y)).symm.trans he))
          subst j
          exact mem_map.mpr ⟨y, mem_univ _, rfl⟩
        · have hv' : v = dom (a i) := by simpa only [owner, dite_eq_right hex] using he
          exact (hv (a i) hv'.symm).elim
      · intro hx
        obtain ⟨y, _, rfl⟩ := mem_map.mp hx
        exact ⟨hnot (i, y), hslot (i, y)⟩
    have hd : Disjoint (base.erase (a i)) (univ.map (block i)) := by
      apply disjoint_left.mpr
      intro x hx hy
      obtain ⟨y, _, rfl⟩ := mem_map.mp hy
      exact hnot (i, y) (mem_erase.mp hx).2
    rw [ExceptionalHeadMass.core, hf, card_union_of_disjoint hd, card_erase_of_mem (ha i)]
    simp [base]
  have hmain := ExceptionalHeadMass.mass dom base a owner δ (k - 1 + r) k ha
    (by simp [base]) ho hc hk (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hfield)
  simpa only [Fintype.card_fin] using hmain

end ArkLib.ProximityGap.Frontier.ExceptionalHeadLayout

#print axioms ArkLib.ProximityGap.Frontier.ExceptionalHeadLayout.mass
