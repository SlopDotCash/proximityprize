/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftMultiplicityBudget
import Mathlib.Data.Finset.Powerset

/-! # Exact distribution of a Paley row on a fixed-size sample

For a prescribed shift, each sign occurs at half the nonzero coordinates.
The counts of samples at each signed imbalance are products of binomial
coefficients, with an extra coordinate when the sample contains the zero.
-/

namespace ProximityGap.PaleyRowSampling

open Finset PaleyShiftMultiplicityBudget

variable {p : ℕ} [Fact p.Prime]

private def signClass (b : ZMod p) (s : ℤ) : Finset (ZMod p) :=
  univ.filter fun x => quadraticChar (ZMod p) (x + b) = s

private theorem signClass_card (hp : p ≠ 2) (b : ZMod p) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (signClass b s).card = (p - 1) / 2 := by
  have hsum : ∑ x : ZMod p, quadraticChar (ZMod p) (x + b) = 0 := by
    calc
      _ = ∑ x : ZMod p, quadraticChar (ZMod p) x :=
        Fintype.sum_equiv (Equiv.addRight b) _ _ (fun _ => rfl)
      _ = 0 := quadraticChar_sum_zero (by rwa [ZMod.ringChar_zmod_n])
  have h := PaleyShiftListRecovery.agreement_excess (univ : Finset (ZMod p)) b hs
  simp only [hsum, mul_zero, mem_univ, ite_true, card_univ, ZMod.card] at h
  change (PaleyShiftListRecovery.agreements univ b s) = _
  omega

/-- On a fixed row, exactly this many samples omit the zero, have size
`r+s`, and have signed discrepancy `r-s`. -/
theorem card_row_omit (hp : p ≠ 2) (b : ZMod p) (r s : ℕ) :
    (((univ : Finset (ZMod p)).powersetCard (r + s)).filter
      (fun S => -b ∉ S ∧ shiftSum S b = (r : ℤ) - s)).card =
      ((p - 1) / 2).choose r * ((p - 1) / 2).choose s := by
  classical
  let P := signClass b 1
  let N := signClass b (-1)
  have hd : Disjoint P N := by
    apply disjoint_left.mpr
    intro x hx hy
    have h := (mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2
    norm_num at h
  have hpole : -b ∉ P ∪ N := by simp [P, N, signClass]
  have decompose (S : Finset (ZMod p)) (hs : -b ∉ S) :
      (S ∩ P) ∪ (S ∩ N) = S := by
    rw [← inter_union_distrib_left, inter_eq_left]
    intro x hx
    have hn : x + b ≠ 0 := fun h => hs (eq_neg_of_add_eq_zero_left h ▸ hx)
    simpa only [P, N, signClass, mem_union, mem_filter, mem_univ, true_and] using
      quadraticChar_dichotomy hn
  have project {X Y : Finset (ZMod p)} (hX : X ⊆ P) (hY : Y ⊆ N) :
      (X ∪ Y) ∩ P = X ∧ (X ∪ Y) ∩ N = Y := by
    have hXP := inter_eq_left.mpr hX
    have hYN := inter_eq_left.mpr hY
    have hXN := Finset.disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hX hd)
    have hYP := Finset.disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hY hd.symm)
    simp [union_inter_distrib_right, hXP, hYN, hXN, hYP]
  have row (S : Finset (ZMod p)) (h : -b ∉ S) :
      shiftSum S b = 2 * ((S ∩ P).card : ℤ) - S.card := by
    have he : S.filter (fun x => quadraticChar (ZMod p) (x + b) = 1) = S ∩ P := by
      ext x
      simp [P, signClass]
    simpa only [shiftSum, PaleyShiftListRecovery.agreements, he, one_mul, h, ite_false, add_zero]
      using PaleyShiftListRecovery.agreement_excess S b (s := 1) (Or.inl rfl)
  have hPsize : P.card = (p - 1) / 2 := signClass_card hp b (Or.inl rfl)
  have hNsize : N.card = (p - 1) / 2 := signClass_card hp b (Or.inr rfl)
  rw [show ((p - 1) / 2).choose r * ((p - 1) / 2).choose s =
      P.card.choose r * N.card.choose s by rw [hPsize, hNsize]]
  rw [← card_powersetCard, ← card_powersetCard, ← card_product]
  refine card_bij' (fun S _ => (S ∩ P, S ∩ N)) (fun X _ => X.1 ∪ X.2) ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨hsize, hpoleS, hrow⟩ := mem_filter.mp hS
    have hc := (mem_powersetCard.mp hsize).2
    have hP := row S hpoleS
    have dis := disjoint_of_subset_right (inter_subset_right (s₁ := S)) <|
      disjoint_of_subset_left (inter_subset_right (s₁ := S)) hd
    have hsum := card_union_of_disjoint dis
    rw [decompose S hpoleS] at hsum
    have hpCount : (S ∩ P).card = r := by omega
    have hnCount : (S ∩ N).card = s := by omega
    exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_right, hpCount⟩,
      mem_powersetCard.mpr ⟨inter_subset_right, hnCount⟩⟩
  · rintro ⟨X, Y⟩ h
    obtain ⟨hx, hy⟩ := mem_product.mp h
    obtain ⟨hX, hXc⟩ := mem_powersetCard.mp hx
    obtain ⟨hY, hYc⟩ := mem_powersetCard.mp hy
    have hzero : -b ∉ X ∪ Y := fun hm => hpole (union_subset_union hX hY hm)
    have hc : (X ∪ Y).card = r + s := by
      rw [card_union_of_disjoint (disjoint_of_subset_right hY (disjoint_of_subset_left hX hd)),
        hXc, hYc]
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hc⟩, hzero, ?_⟩
    rw [row _ hzero, (project hX hY).1, hXc, hc]
    omega
  · intro S h
    exact decompose S (mem_filter.mp h).2.1
  · rintro ⟨X, Y⟩ h
    obtain ⟨hx, hy⟩ := mem_product.mp h
    exact Prod.ext_iff.mpr (project (mem_powersetCard.mp hx).1 (mem_powersetCard.mp hy).1)

/-- Including the zero adds one coordinate without changing the signed
discrepancy or its number of witnesses. -/
theorem card_row_hit (hp : p ≠ 2) (b : ZMod p) (r s : ℕ) :
    (((univ : Finset (ZMod p)).powersetCard (r + s + 1)).filter
      (fun S => -b ∈ S ∧ shiftSum S b = (r : ℤ) - s)).card =
      ((p - 1) / 2).choose r * ((p - 1) / 2).choose s := by
  classical
  rw [← card_row_omit hp b r s]
  have herase (S : Finset (ZMod p)) : shiftSum (S.erase (-b)) b = shiftSum S b := by
    by_cases h : -b ∈ S
    · rw [shiftSum, shiftSum, ← sum_erase_add _ _ h]
      simp
    · rw [erase_eq_of_notMem h]
  refine card_bij' (fun S _ => S.erase (-b)) (fun S _ => insert (-b) S) ?_ ?_ ?_ ?_
  · intro S h
    obtain ⟨hs, hb, hr⟩ := mem_filter.mp h
    have hc := (mem_powersetCard.mp hs).2
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, notMem_erase _ _, ?_⟩
    · rw [card_erase_of_mem hb, hc]
      omega
    · rwa [herase]
  · intro S h
    obtain ⟨hs, hb, hr⟩ := mem_filter.mp h
    have hc := (mem_powersetCard.mp hs).2
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, mem_insert_self _ _, ?_⟩
    · rw [card_insert_of_notMem hb, hc]
    · rw [shiftSum, sum_insert hb]
      simpa only [shiftSum, neg_add_cancel, MulChar.map_zero, zero_add] using hr
  · intro S h
    exact insert_erase (mem_filter.mp h).2.1
  · intro S h
    exact erase_insert (mem_filter.mp h).2.1

/-- The complete fixed-size, fixed-discrepancy fiber. Its parity determines
whether the sample contains the zero of the row. -/
theorem card_row (hp : p ≠ 2) (b : ZMod p) (r s : ℕ) (z : Bool) :
    (((univ : Finset (ZMod p)).powersetCard (r + s + z.toNat)).filter
      (fun S => shiftSum S b = (r : ℤ) - s)).card =
      ((p - 1) / 2).choose r * ((p - 1) / 2).choose s := by
  classical
  have parity (S : Finset (ZMod p)) (h : shiftSum S b = (r : ℤ) - s) :
      (r : ℤ) - s = 2 * (PaleyShiftListRecovery.agreements S b 1 : ℤ) -
        S.card + (if -b ∈ S then 1 else 0) := by
    simpa only [← h, shiftSum, one_mul] using
      PaleyShiftListRecovery.agreement_excess S b (s := 1) (Or.inl rfl)
  cases z
  · rw [← card_row_omit hp b r s]
    congr 1
    apply filter_congr
    intro S hS
    have hc := (mem_powersetCard.mp hS).2
    constructor
    · intro h
      refine ⟨fun hz => ?_, h⟩
      have hh := parity S h
      simp [hz, hc] at hh
      omega
    · exact And.right
  · rw [← card_row_hit hp b r s]
    congr 1
    apply filter_congr
    intro S hS
    have hc := (mem_powersetCard.mp hS).2
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hz
      have hh := parity S h
      simp [hz, hc] at hh
      omega
    · exact And.right

/-- Total number of incidences with a prescribed row sum, over all samples
and all shifts. Dividing by the number of samples gives the expected number
of such shifts for a uniform fixed-size subset. -/
theorem sum_card_shifts (hp : p ≠ 2) (r s : ℕ) (z : Bool) :
    ∑ S ∈ (univ : Finset (ZMod p)).powersetCard (r + s + z.toNat),
      (univ.filter (fun b => shiftSum S b = (r : ℤ) - s)).card =
        p * (((p - 1) / 2).choose r * ((p - 1) / 2).choose s) := by
  classical
  have indicator (S : Finset (ZMod p)) :
      (univ.filter (fun b => shiftSum S b = (r : ℤ) - s)).card =
        ∑ b : ZMod p, if shiftSum S b = (r : ℤ) - s then 1 else 0 :=
    (sum_boole (R := ℕ) _ univ).symm
  simp_rw [indicator]
  rw [sum_comm]
  simp [sum_boole, card_row hp _ r s z]

end ProximityGap.PaleyRowSampling

#print axioms ProximityGap.PaleyRowSampling.card_row_omit
#print axioms ProximityGap.PaleyRowSampling.card_row_hit

#print axioms ProximityGap.PaleyRowSampling.sum_card_shifts
