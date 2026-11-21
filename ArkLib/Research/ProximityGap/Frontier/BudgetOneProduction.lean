/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ListBudgetOne
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarLiteralEps
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality

/-! # Four exact list boundaries and an MCA boundary at length 2³⁰

The explicit 129-bit field has 128-bit integer budget one. Its multiplicative group
contains the exhibited smooth domain. All four list cutoffs apply at every positive
interleaving width. The existing one-error MCA theorem applies to this same code.
-/

namespace ProximityGap.BudgetOneProduction

open Code GrandChallenges
open scoped NNReal ENNReal
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

/-- A prime of the form 11·2¹²⁵+1. -/
abbrev p : ℕ := 467888254516290387262140085218681290753

set_option maxRecDepth 100000 in
/-- The Lucas certificate uses generator 3 and the two prime divisors 2 and 11 of p−1. -/
theorem prime_p : p.Prime := by
  apply lucas_primality p 3 (by rw [← binaryPow_eq_pow]; decide)
  intro v hv hd
  rw [show p - 1 = 2 ^ 125 * 11 by decide] at hd
  rcases hv.dvd_mul.mp hd with h | h
  · have heq := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow h)
    subst v
    rw [← binaryPow_eq_pow]
    decide
  · have heq := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 11)).mp h
    subst v
    rw [← binaryPow_eq_pow]
    decide

instance : Fact p.Prime := ⟨prime_p⟩

/-- Fixed nonzero generator of the evaluation subgroup. -/
def generator : (ZMod p)ˣ := Units.mk0 20759207997786210761536297572531909971 (by decide)

set_option maxRecDepth 100000 in
theorem generator_order : orderOf generator = 2 ^ 30 := by
  rw [← orderOf_units]
  apply orderOf_eq_prime_pow (p := 2) (n := 29) <;> rw [← binaryPow_eq_pow] <;> decide

/-- The domain sends i to the i-th power of the specified generator. -/
def domain : Fin (2 ^ 30) ↪ ZMod p := MCADeltaStarLiteralEps.smoothDom p generator generator_order

/-- Smoothness in the sponsor's canonical predicate, including the full coset equality. -/
@[instance_reducible] noncomputable def smooth : ReedSolomon.Smooth domain where
  H := Subgroup.zpowers generator
  a := 1
  h_card_pow2 := ⟨30, Fintype.card_fin _⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨generator ^ i.val, Subgroup.npow_mem_zpowers _ _, one_mul _⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hu)
      have his : i < 2 ^ 30 := generator_order ▸ Finset.mem_range.mp hi
      exact Finset.mem_image.mpr ⟨⟨i, his⟩, Finset.mem_univ _, (one_mul _).symm⟩

/-- First failing integer error counts, ordered by decreasing prize rate. -/
def firstBad : Fin 4 → ℕ := ![268435457, 402653185, 469762049, 503316481]

private theorem sizes (j : Fin 4) :
    let k := prizeDimension (ι := Fin (2 ^ 30)) j
    0 < k ∧ k + 2 ≤ 2 ^ 30 ∧ (2 ^ 30 - k + 2) / 2 = firstBad j := by
  simp only [prizeDimension, Fintype.card_fin]
  fin_cases j <;> norm_num [prizeDenominator, firstBad]

/-- The rate-j Reed–Solomon code on the fixed common domain. -/
noncomputable abbrev rs (j : Fin 4) : Submodule (ZMod p) (Fin (2 ^ 30) → ZMod p) :=
  ReedSolomon.code domain (prizeDimension (ι := Fin (2 ^ 30)) j)

/-- Exact canonical 128-bit list test for all widths and all real radii at the four rates. -/
theorem four_list (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m) (rs j : Set (Fin (2 ^ 30) → ZMod p))) δ : ℝ≥0∞) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * (Fintype.card (ZMod p) : ℝ≥0∞) ↔
        δ < (firstBad j : ℝ) / 2 ^ 30 := by
  let k := prizeDimension (ι := Fin (2 ^ 30)) j
  have hkn : k ≤ Fintype.card (Fin (2 ^ 30)) := by
    rw [Fintype.card_fin]
    exact (Nat.le_add_right k 2).trans (sizes j).2.1
  have hbudget : Fintype.card (ZMod p) / 2 ^ 128 = 1 := by rw [ZMod.card]; decide
  have h := ListBudgetOne.prize_safe_iff domain k m (sizes j).1 hkn hm δ hbudget
  rw [Fintype.card_fin, (sizes j).2.2] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- The MCA supremum on precisely the above domain is one error at each of the four rates. -/
theorem four_mca (j : Fin 4) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (rs j : Set (Fin (2 ^ 30) → ZMod p))
      (1 / 2 ^ 128) = 1 / (2 ^ 30 : ℝ≥0) := by
  have h := MCADeltaStarLiteralEps.mcaDeltaStar_zmod_eq_inv_n p
    (by decide) (by decide) domain (sizes j).2.1
  rw [BoundarySecurityBudget.rsCode_eq_code] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

end ProximityGap.BudgetOneProduction

#print axioms ProximityGap.BudgetOneProduction.prime_p
#print axioms ProximityGap.BudgetOneProduction.generator_order
#print axioms ProximityGap.BudgetOneProduction.smooth
#print axioms ProximityGap.BudgetOneProduction.four_list
#print axioms ProximityGap.BudgetOneProduction.four_mca
