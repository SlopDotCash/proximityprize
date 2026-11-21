/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Four exact list thresholds over a 246-bit prime field

On the 128th roots of unity in the prime field of order `65 * 2^239 + 1`, the
first bad error counts are `63, 97, 113, 121` at the four sponsor rates in order.
A Lucas witness and binary powering certify primality and the order of the
explicit domain generator.
-/

namespace ProximityGap.FourRateListPrime246

open Code GrandChallenges
open scoped NNReal ENNReal
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

set_option maxRecDepth 10000

/-- The 246-bit prime modulus. -/
abbrev P : ℕ := 65 * 2^239 + 1

theorem prime_P : Nat.Prime P := by
  have hmain : (3 : ZMod P) ^ (P-1) = 1 := by rw [← binaryPow_eq_pow]; decide
  refine lucas_primality P 3 hmain ?_
  intro v hv hd
  rw [show P-1 = 2^239 * (5*13) by decide] at hd
  rcases hv.dvd_mul.mp hd with htwo | hodd
  · have heq := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow htwo)
    subst v
    rw [← binaryPow_eq_pow]
    decide
  · rcases hv.dvd_mul.mp hodd with h5 | h13
    · have heq := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 5)).mp h5
      subst v
      rw [← binaryPow_eq_pow]
      decide
    · have heq := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 13)).mp h13
      subst v
      rw [← binaryPow_eq_pow]
      decide

instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The prime field with this modulus. -/
abbrev K := ZMod P

/-- An explicit primitive 128th root of unity. -/
abbrev generator : K :=
  17853208868485432014317288845792547206997403552813598151082541291610392869

theorem generator_primitive : IsPrimitiveRoot generator 128 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow (p := 2) (n := 6)
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide

/-- The smooth subgroup domain. -/
noncomputable def H : Subgroup Kˣ := rootsOfUnity 128 K

noncomputable instance : Fintype H := Fintype.ofFinite H

theorem card_K : Fintype.card K = P := ZMod.card P

theorem card_H : Fintype.card H = 128 :=
  Nat.card_eq_fintype_card.symm.trans generator_primitive.card_rootsOfUnity

/-- The subgroup inclusion defining the evaluation domain. -/
noncomputable abbrev domain : H ↪ K := FourRateList128.domain H

noncomputable instance : ReedSolomon.Smooth domain := FourRateList128.smooth H card_H

/-- First over-budget error count, ordered by decreasing prize rate. -/
def firstBad : Fin 4 → ℕ := FourRateList128.firstBad

theorem budget_window : FourRateList128.BudgetWindow (Fintype.card K) := by
  rw [card_K]
  constructor <;> simp only [Nat.choose_eq_descFactorial_div_factorial] <;> decide

/-- Exact list thresholds at every real radius and every positive width. -/
theorem list_threshold (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card K : ENNReal) ↔
        δ < (firstBad j : ℝ)/128 :=
  FourRateList128.list_threshold H card_H budget_window j m hm δ

/-- Adjacent grid witnesses for the four prize rates. -/
noncomputable def resolution (j : Fin 4) (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K))
      m (prizeThreshold : ℝ≥0) :=
  FourRateList128.resolution H card_H budget_window j m hm

/-- The complete four-rate prize proposition at every positive width. -/
theorem listDecodingPrize_all_rates (m : ℕ) (hm : 0 < m) : listDecodingPrize domain m :=
  FourRateList128.listDecodingPrize_all_rates H card_H budget_window m hm

#print axioms list_threshold
#print axioms listDecodingPrize_all_rates

#print axioms prime_P
#print axioms generator_primitive

end ProximityGap.FourRateListPrime246
