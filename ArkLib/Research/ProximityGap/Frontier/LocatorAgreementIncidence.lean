/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith

/-!
# Counting a list with baseline and fresh agreements

Remove the common zero coordinates. Among the remaining coordinates each
candidate can use only a bounded number of baseline sites. Each fresh site
can serve only a bounded number of candidates. The resulting bound uses the
two capacities even when the number of baseline coordinates is unknown.
-/
namespace ProximityGap.LocatorAgreementIncidence

open Finset

/-- A received word with few baseline sites offers more fresh sites but forces
every candidate to take more fresh agreements. Eliminating the baseline count
gives the bound below. The relation describes matches at each group of sites. -/
theorem list_capacity {α β : Type*} (W : Finset α) (B F : Finset β)
    (R : α → β → Prop) [∀ w x, Decidable (R w x)] (m t c : ℤ)
    (hm : m ≤ t) (ht : t ≤ (B.card : ℤ) + F.card) (hc : 0 ≤ c)
    (hscore : ∀ w ∈ W, t ≤ ((B.bipartiteAbove R w).card : ℤ) + (F.bipartiteAbove R w).card)
    (hbase : ∀ w ∈ W, ((B.bipartiteAbove R w).card : ℤ) ≤ m)
    (hfresh : ∀ x ∈ F, ((W.bipartiteBelow R x).card : ℤ) ≤ c) :
    (W.card : ℤ) * (t - m) ≤ ((B.card : ℤ) + F.card - m) * c := by
  let b : ℤ := B.card
  let n : ℤ := F.card
  let L : ℤ := W.card
  have hd (w) (hw : w ∈ W) :
      t - min b m ≤ ((F.bipartiteAbove R w).card : ℤ) := by
    have hle : ((B.bipartiteAbove R w).card : ℤ) ≤ b := by
      change ((B.filter (R w)).card : ℤ) ≤ (B.card : ℤ)
      exact_mod_cast card_filter_le B (R w)
    have h := hscore w hw
    have hm' := hbase w hw
    omega
  have hcap : L * (t - min b m) ≤ n * c := by
    simpa only [L, n, nsmul_eq_mul] using
      (card_nsmul_le_card_nsmul R hd hfresh)
  change L * (t - m) ≤ (b + n - m) * c
  by_cases hbm : m ≤ b
  · rw [min_eq_right hbm] at hcap
    exact hcap.trans (mul_le_mul_of_nonneg_right (by omega) hc)
  rw [min_eq_left (le_of_not_ge hbm)] at hcap
  by_cases hLc : L ≤ c
  · calc
      _ ≤ c * (t - m) := mul_le_mul_of_nonneg_right hLc (sub_nonneg.mpr hm)
      _ ≤ c * (b + n - m) := mul_le_mul_of_nonneg_left (sub_le_sub_right ht m) hc
      _ = _ := mul_comm _ _
  have hx := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hLc)) (sub_nonneg.mpr (le_of_not_ge hbm))
  nlinarith only [hcap, hx]

#print axioms list_capacity

end ProximityGap.LocatorAgreementIncidence
