/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothCubicBudgetWindow
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-! # A quadratic extension with a sharp production-length MCA threshold

Over the field of order `(1433 · 2^69 + 1)^2`, the order-`2^30` multiplicative
subgroup gives first failure at 700924245 errors for rate one sixteenth.
The two codeword rows and their scalar combinations are taken over the extension. -/

namespace ArkLib.ProximityGap.Frontier.QuadraticCubicWindowExample

open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity
open ProximityPrize
open scoped NNReal ENNReal

abbrev p : ℕ := 1433 * 2 ^ 69 + 1

/-- A Lucas certificate using the complete factorization of `p-1`. -/
theorem prime_p : Nat.Prime p := by
  have hm : (3 : ZMod p) ^ (p - 1) = 1 := by reduce_mod_char
  refine lucas_primality p 3 hm ?_
  intro v hv hd
  rw [show p - 1 = 2 ^ 69 * 1433 by decide] at hd
  rcases hv.dvd_mul.mp hd with he | ho
  · have h := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow he)
    subst v
    reduce_mod_char
    decide
  · have h := (Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 1433)).mp ho
    subst v
    reduce_mod_char
    decide

instance : Fact p.Prime := ⟨prime_p⟩

abbrev K := GaloisField p 2

noncomputable instance : Fintype K := Fintype.ofFinite K
noncomputable instance : DecidableEq K := Classical.decEq K

/-- The dimension over the prime field is exactly two. -/
theorem degree : Module.finrank (ZMod p) K = 2 := GaloisField.finrank p (by decide)

/-- Order of the extension field. -/
theorem card_K : Fintype.card K = p ^ 2 := Nat.card_eq_fintype_card.symm.trans
  (GaloisField.card p 2 (by decide))

abbrev baseGenerator : ZMod p := 24238576185632127096285

/-- The explicit generator has order `2^30` in the prime field. -/
theorem base_generator_primitive : IsPrimitiveRoot baseGenerator (2 ^ 30) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow (p := 2) (n := 29)
  · change (24238576185632127096285 : ZMod p) ^ (2 ^ 29 : ℕ) ≠ 1
    reduce_mod_char
    decide
  · change (24238576185632127096285 : ZMod p) ^ (2 ^ 30 : ℕ) = 1
    reduce_mod_char

/-- Embedding in the quadratic extension preserves the order. -/
theorem generator_primitive :
    IsPrimitiveRoot (algebraMap (ZMod p) K baseGenerator) (2 ^ 30) :=
  base_generator_primitive.map_of_injective (algebraMap (ZMod p) K).injective

noncomputable def H : Subgroup Kˣ := rootsOfUnity (2 ^ 30) K
noncomputable instance : Fintype H := Fintype.ofFinite H

theorem card_H : Fintype.card H = n :=
  Nat.card_eq_fintype_card.symm.trans generator_primitive.card_rootsOfUnity

/-- Explicit evaluation domain in the extension field. -/
noncomputable abbrev domain : H ↪ K := FourRateList128.domain H

noncomputable instance : ReedSolomon.Smooth domain where
  H := H
  a := 1
  h_card_pow2 := ⟨30, card_H⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i.val, i.property, one_mul _⟩
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, (one_mul _).symm⟩

theorem budget : Fintype.card K / 2 ^ 128 = 2102772736 := by rw [card_K]; decide

/-- All real radii below the boundary pass, and the boundary itself fails at every width. -/
theorem classification (m : ℕ) [NeZero m] :
    let b : ℝ≥0 := 700924245 / n
    mcaDeltaStar (F := K) ((ReedSolomon.code domain k : Set (H → K)) ^⋈ (Fin m)) tolerance = b ∧
      ∀ δ : ℝ≥0, epsMCA (F := K) ((ReedSolomon.code domain k : Set (H → K)) ^⋈ (Fin m)) δ ≤
        tolerance ↔ δ < b :=
  SmoothCubicBudgetWindow.classification domain card_H budget (by decide) (by decide) m

/-- On this quadratic extension the finite rank formula returns 700924245. -/
theorem rank_answer : (RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) k).map Fin.val =
    some 700924245 :=
  SmoothCubicBudgetWindow.rank_answer domain card_H budget (by decide) (by decide)

end ArkLib.ProximityGap.Frontier.QuadraticCubicWindowExample
