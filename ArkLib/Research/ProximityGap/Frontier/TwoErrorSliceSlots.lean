/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceTransfer
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Finite slots for a cross-ratio penalty histogram -/

namespace ProximityGap.TwoErrorSlice

open Finset

variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F]

/-- For each tested product in the field, the charged triples occupy distinct
slots. The implication compares two explicit table entries. -/
def SlotInjective {H : ℕ} (D : I ↪ F) (u v : I) (key : Fin H → F) (cost : Fin H → ℕ)
    (slot : Fin H → I → Fin 3 → Fin 12) : Prop :=
  ∀ i x l j y m, x ∈ (univ.erase u).erase v → y ∈ (univ.erase u).erase v →
    l.val < cost i → m.val < cost j →
    key i * ratio D u v x = key j * ratio D u v y →
    slot i x l = slot j y m → i=j ∧ x=y ∧ l=m

/-- An explicit heavy-key table and twelve tagged slots certify the entire row,
including field scalars absent from the table. -/
theorem rowPenaltyBound_of_slots {H : ℕ} (D : I ↪ F) (u v : I) (key : Fin H → F)
    (cost : Fin H → ℕ) (hcost : ∀ i, cost i=1 ∨ cost i=3)
    (light : ∀ T : F, (∀ i, key i ≠ T) → (alternatives D u v T).card ≤ 1)
    (heavy : ∀ i, cost i=1 → (alternatives D u v (key i)).card ≤ 2)
    (slot : Fin H → I → Fin 3 → Fin 12) (hslot : SlotInjective D u v key cost slot) :
    RowPenaltyBound D u v := by
  classical
  intro μ _
  let sites := (univ.erase u).erase v
  let f := ratio D u v
  let keys (x : I) := univ.filter fun i => key i*f x=μ
  let tags (i : Fin H) := (univ : Finset (Fin 3)).filter fun l => l.val<cost i
  have tag_size (i : Fin H) : (tags i).card=cost i := by
    rcases hcost i with h | h <;> simp only [tags,h] <;> decide
  have nf {x} (hx : x ∈ sites) : f x ≠ 0 := by
    obtain ⟨hv,hu⟩ := mem_erase.mp hx
    exact ratio_ne_zero D (mem_erase.mp hu).1.symm hv.symm
  let bag (x : I) := (keys x).sigma tags
  have row (x) (hx : x ∈ sites) :
      penalty (alternatives D u v (μ / f x)).card ≤ (bag x).card := by
    have hc : (bag x).card = ∑ i ∈ keys x, cost i := by simp only [bag,card_sigma,tag_size]
    rw [hc]
    by_cases ex : ∃ i, key i=μ/f x
    · obtain ⟨i,hi⟩ := ex
      have hmem : i ∈ keys x := mem_filter.mpr ⟨mem_univ _, (eq_div_iff (nf hx)).mp hi⟩
      apply le_trans _ (single_le_sum (f := cost) (fun _ _ => Nat.zero_le _) hmem)
      rw [← hi]
      rcases hcost i with h | h
      · have r := heavy i h
        rw [h]
        unfold penalty
        split_ifs <;> omega
      · rw [h]
        unfold penalty
        split_ifs <;> omega
    · have r := light _ (not_exists.mp ex)
      simp [penalty,r]
  have lo := sum_le_sum row
  rw [← card_sigma] at lo
  apply lo.trans
  have bound : (sites.sigma bag).card ≤ (univ : Finset (Fin 12)).card := by
    apply card_le_card_of_injOn (fun a => slot a.2.1 a.1 a.2.2) (fun _ _ => mem_univ _)
    rintro ⟨x,i,l⟩ hx ⟨y,j,m⟩ hy he
    obtain ⟨hx,hb⟩ := mem_sigma.mp hx
    obtain ⟨hy,hc⟩ := mem_sigma.mp hy
    obtain ⟨hi,hl⟩ := mem_sigma.mp hb
    obtain ⟨hj,hm⟩ := mem_sigma.mp hc
    have hprod : key i*f x=key j*f y := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
    obtain ⟨rfl,rfl,rfl⟩ := hslot i x l j y m hx hy (mem_filter.mp hl).2 (mem_filter.mp hm).2 hprod he
    rfl
  simpa using bound

/-- An equivalent finite-pair input for the multiplicity hypotheses. Pairwise
collisions must hit a recorded key, and a cost-one key needs two slots. -/
theorem rowPenaltyBound_of_pair_slots {H : ℕ} (D : I ↪ F) (u v : I) (key : Fin H → F)
    (cost : Fin H → ℕ) (hcost : ∀ i, cost i=1 ∨ cost i=3)
    (pairSlot : Finset I → Fin 2)
    (lightCollision : ∀ A B : Finset I, A ∈ ((univ.erase u).erase v).powersetCard 2 →
      B ∈ ((univ.erase u).erase v).powersetCard 2 → A ≠ B →
      (∏ x ∈ A, ratio D u v x) = ∏ x ∈ B, ratio D u v x →
      ∃ i, key i = ∏ x ∈ A, ratio D u v x)
    (heavyCollision : ∀ i, cost i=1 → ∀ A B : Finset I,
      A ∈ alternatives D u v (key i) → B ∈ alternatives D u v (key i) →
      pairSlot A=pairSlot B → A=B)
    (slot : Fin H → I → Fin 3 → Fin 12) (hslot : SlotInjective D u v key cost slot) :
    RowPenaltyBound D u v := by
  classical
  apply rowPenaltyBound_of_slots D u v key cost hcost _ _ slot hslot
  · intro t hn
    apply card_le_one.mpr
    intro A hA B hB
    by_contra hab
    have ha := mem_filter.mp hA
    have hb := mem_filter.mp hB
    obtain ⟨i,hi⟩ := lightCollision A B ha.1 hb.1 hab (ha.2.trans hb.2.symm)
    exact hn i (hi.trans ha.2)
  · intro i hi
    have h : (alternatives D u v (key i)).card ≤ (univ : Finset (Fin 2)).card :=
      card_le_card_of_injOn pairSlot (fun _ _ => mem_univ _)
        (fun A hA B hB he => heavyCollision i hi A B hA hB he)
    simpa using h

/-- Unique natural tags within each pair-product fiber give the light and heavy
multiplicity bounds without enumerating arbitrary field elements. -/
theorem rowPenaltyBound_of_pair_tags {H : ℕ} (D : I ↪ F) (u v : I) (key : Fin H → F)
    (cost : Fin H → ℕ) (hcost : ∀ i, cost i=1 ∨ cost i=3) (keyInj : Function.Injective key)
    (tag : Finset I → ℕ)
    (tagInj : ∀ A B : Finset I, A ∈ ((univ.erase u).erase v).powersetCard 2 →
      B ∈ ((univ.erase u).erase v).powersetCard 2 →
      (∏ x ∈ A, ratio D u v x) = ∏ x ∈ B, ratio D u v x → tag A = tag B → A=B)
    (tagPos : ∀ A ∈ ((univ.erase u).erase v).powersetCard 2, 1 ≤ tag A →
      ∃ i, key i = ∏ x ∈ A, ratio D u v x)
    (tagTwo : ∀ A ∈ ((univ.erase u).erase v).powersetCard 2, 2 ≤ tag A →
      ∃ i, key i = (∏ x ∈ A, ratio D u v x) ∧ cost i=3)
    (slot : Fin H → I → Fin 3 → Fin 12) (hslot : SlotInjective D u v key cost slot) :
    RowPenaltyBound D u v := by
  classical
  apply rowPenaltyBound_of_slots D u v key cost hcost _ _ slot hslot
  · intro t hn
    have small (A) (ha : A ∈ alternatives D u v t) : tag A=0 := by
      by_contra h
      obtain ⟨i,hi⟩ := tagPos A (mem_filter.mp ha).1 (by omega)
      exact hn i (hi.trans (mem_filter.mp ha).2)
    apply card_le_one.mpr
    intro A hA B hB
    exact tagInj A B (mem_filter.mp hA).1 (mem_filter.mp hB).1
      ((mem_filter.mp hA).2.trans (mem_filter.mp hB).2.symm) ((small A hA).trans (small B hB).symm)
  · intro i hi
    have small (A) (ha : A ∈ alternatives D u v (key i)) : tag A<2 := by
      by_contra! h
      obtain ⟨j,hj,hcost'⟩ := tagTwo A (mem_filter.mp ha).1 h
      have hji := keyInj (hj.trans (mem_filter.mp ha).2)
      rw [hji,hi] at hcost'
      contradiction
    have hb : (alternatives D u v (key i)).card ≤ (range 2).card := by
      apply card_le_card_of_injOn tag (fun A hA => mem_range.mpr (small A hA))
      intro A hA B hB he
      exact tagInj A B (mem_filter.mp hA).1 (mem_filter.mp hB).1
        ((mem_filter.mp hA).2.trans (mem_filter.mp hB).2.symm) he
    simpa using hb

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.rowPenaltyBound_of_slots
#print axioms ProximityGap.TwoErrorSlice.rowPenaltyBound_of_pair_slots
#print axioms ProximityGap.TwoErrorSlice.rowPenaltyBound_of_pair_tags
