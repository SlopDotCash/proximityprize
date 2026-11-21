/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourRateBudget32
import Mathlib.Tactic.ReduceModChar

/-! # A smooth prime-field realization of the eight length-32 thresholds -/

namespace ProximityGap.FourRatePrime152

open Code GrandChallenges
open scoped NNReal ENNReal

abbrev p : ℕ := 17 * 2^147 + 1

/-- Lucas certificate for the 152-bit modulus. -/
theorem prime_p : Nat.Prime p := by
  have hm : (3 : ZMod p) ^ (p-1) = 1 := by reduce_mod_char
  refine lucas_primality p 3 hm ?_
  intro v hv hd
  rw [show p-1 = 2^147 * 17 by decide] at hd
  rcases hv.dvd_mul.mp hd with he | ho
  · have h := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow he)
    subst v
    reduce_mod_char
    decide
  · have h := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 17)).mp ho
    subst v
    reduce_mod_char
    decide

instance : Fact p.Prime := ⟨prime_p⟩

abbrev K := ZMod p
abbrev generator : K := 528780187462544907525990687541422824431408579

theorem generator_primitive : IsPrimitiveRoot generator 32 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow (p := 2) (n := 4)
  · change (528780187462544907525990687541422824431408579 : ZMod p)^16 ≠ 1
    reduce_mod_char
    decide
  · change (528780187462544907525990687541422824431408579 : ZMod p)^32 = 1
    reduce_mod_char

noncomputable def H : Subgroup Kˣ := rootsOfUnity 32 K
noncomputable instance : Fintype H := Fintype.ofFinite H

theorem card_H : Fintype.card H = 32 :=
  Nat.card_eq_fintype_card.symm.trans generator_primitive.card_rootsOfUnity

/-- The inclusion of all 32nd roots of unity. -/
noncomputable abbrev domain : H ↪ K := FourRateList128.domain H

noncomputable instance : ReedSolomon.Smooth domain where
  H := H
  a := 1
  h_card_pow2 := ⟨5, card_H⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i.val, i.property, one_mul _⟩
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, (one_mul _).symm⟩

private theorem card_K : Fintype.card K = p := ZMod.card p

private theorem modulus_budget : p / 2^128 = 8912896 := by decide

/-- The prize's 128-bit security tolerance allows 8,912,896 bad scalars. -/
theorem budget : Fintype.card K / 2^128 = 8912896 :=
  (congrArg (fun x : ℕ => x/2^128) card_K).trans modulus_budget

/-- On this one prime-field domain, the MCA failures at dimensions 16 and 8 are 14
and 23 errors and the two lower rates are safe through radius one. The four list
failures are 15, 24, 29 and 31 errors. Both conclusions include every positive width. -/
theorem thresholds (j : Fin 4) (m : ℕ) [NeZero m] (δ : ℝ≥0) :
    (epsMCA (F := K) (A := Fin m → K)
        ((ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K)) ^⋈ (Fin m)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔
      (j = 0 → δ < 14/32) ∧ (j = 1 → δ < 23/32)) ∧
    ((Lambda (ListInterpolationBoundary.words domain (prizeDimension (ι := H) j) m)
      (δ : ℝ) : ℝ≥0∞) ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card K ↔
      (δ : ℝ) < (FourRateBudget32.listFirstBad j : ℝ)/32) := by
  classical
  have hw : FourRateBudget32.BudgetWindow (Fintype.card K) :=
    ⟨(show 3928630 ≤ 8912896 by decide).trans budget.ge,
      budget.le.trans (by decide : 8912896 ≤ 10518299)⟩
  exact ⟨FourRateBudget32.mca_threshold domain card_H hw j m δ,
    FourRateBudget32.list_threshold domain card_H hw j m (NeZero.pos m) δ⟩

end ProximityGap.FourRatePrime152
