/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeThreeLineCutoff
import ArkLib.Research.ProximityGap.Support.BinaryPower
import ArkLib.Research.ProximityGap.Support.DyadicPowerDomain
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-! # A 255-bit prime with an exact three-line MCA threshold

The prime 2^126(2^129-7)+1 admits a smooth evaluation domain of length
2^126. At dimension sixteen and 128-bit security every injective domain
has the same explicitly rounded cutoff. Lucas certificates use binary
exponentiation for kernel-checked modular arithmetic.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
namespace ProximityGap.PrimeThreeLine255
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open MCAThresholdLedger
open scoped NNReal ENNReal

/-- The certified 255-bit prime. -/
abbrev P : ℕ := 57896044618658097711785492504343953926039498190708639708667886440950970449921

private theorem prime_19917551 : Nat.Prime 19917551 := by
  apply lucas_primality 19917551 17 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show 19917551-1=2*(5^2*(467*(853))) by decide] at hd
  simp only [hq.dvd_mul] at hd
  have options : q=2 ∨ q=5 ∨ q=467 ∨ q=853 := by
    rcases hd with h | h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).mp (hq.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 467)).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 853)).mp h)))
  rcases options with rfl | rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

private theorem prime_7054121 : Nat.Prime 7054121 := by
  apply lucas_primality 7054121 3 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show 7054121-1=2^3*(5*(176353)) by decide] at hd
  simp only [hq.dvd_mul] at hd
  have options : q=2 ∨ q=5 ∨ q=176353 := by
    rcases hd with h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 176353)).mp h))
  rcases options with rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

private theorem prime_6806077 : Nat.Prime 6806077 := by
  apply lucas_primality 6806077 2 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show 6806077-1=2^2*(3*(37*(15329))) by decide] at hd
  simp only [hq.dvd_mul] at hd
  have options : q=2 ∨ q=3 ∨ q=37 ∨ q=15329 := by
    rcases hd with h | h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp h))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37)).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 15329)).mp h)))
  rcases options with rfl | rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

private theorem prime_5750782129 : Nat.Prime 5750782129 := by
  apply lucas_primality 5750782129 19 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show 5750782129-1=2^4*(3^2*(7*(13*(29*(37*(409)))))) by decide] at hd
  simp only [hq.dvd_mul] at hd
  have options : q=2 ∨ q=3 ∨ q=7 ∨ q=13 ∨ q=29 ∨ q=37 ∨ q=409 := by
    rcases hd with h | h | h | h | h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp (hq.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).mp h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13)).mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 29)).mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37)).mp h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 409)).mp h))))))
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

private theorem prime_861085851564354527 : Nat.Prime 861085851564354527 := by
  apply lucas_primality 861085851564354527 10 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show 861085851564354527-1=2*(11*(6806077*(5750782129))) by decide] at hd
  simp only [hq.dvd_mul] at hd
  have options : q=2 ∨ q=11 ∨ q=6806077 ∨ q=5750782129 := by
    rcases hd with h | h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11)).mp h))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq prime_6806077).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq prime_5750782129).mp h)))
  rcases options with rfl | rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

private theorem prime_388749042452671751702769089 : Nat.Prime 388749042452671751702769089 := by
  apply lucas_primality 388749042452671751702769089 3 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show 388749042452671751702769089-1=2^6*(7054121*(861085851564354527)) by decide] at hd
  simp only [hq.dvd_mul] at hd
  have options : q=2 ∨ q=7054121 ∨ q=861085851564354527 := by
    rcases hd with h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq prime_7054121).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq prime_861085851564354527).mp h))
  rcases options with rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

/-- The full factorization of P-1 supplies the Lucas certificate for P. -/
theorem prime_P : Nat.Prime P := by
  apply lucas_primality P 3 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show P-1=2^126*(5*(17579*(19917551*(388749042452671751702769089)))) by decide] at hd
  simp only [hq.dvd_mul] at hd
  have options : q=2 ∨ q=5 ∨ q=17579 ∨ q=19917551 ∨ q=388749042452671751702769089 := by
    rcases hd with h | h | h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).mp h))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17579)).mp h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq prime_19917551).mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq prime_388749042452671751702769089).mp h))))
  rcases options with rfl | rfl | rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

local instance : Fact P.Prime := ⟨prime_P⟩

private abbrev g : ZMod P := 47339145559290942420807142490342298984018508943554033622364312841067936762688

/-- An explicit unit generating the smooth subgroup. -/
def generator : (ZMod P)ˣ := Units.mk0 g (by decide)

/-- The evaluation generator has order exactly 2^126. -/
theorem generator_order : orderOf generator = 2^126 := by
  have half : g^(2:ℕ)^125≠1 := by rw [← binaryPow_eq_pow]; decide
  have full : g^(2:ℕ)^126=1 := by rw [← binaryPow_eq_pow]; decide
  rw [← orderOf_units]
  exact orderOf_eq_prime_pow (x:=g) half full

/-- The consecutive powers of the generator enumerate the domain. -/
def domain : Fin (2^126) ↪ ZMod P := MCADeltaStarLiteralEps.smoothDom P generator generator_order

/-- The consecutive powers form a smooth domain. -/
noncomputable instance smooth_domain : ReedSolomon.Smooth domain :=
  DyadicPowerDomain.smooth generator generator_order

/-- The literal good-radius predicate and supremum on every embedding,
including the certified smooth subgroup. -/
theorem classification (x : Fin (2^126) ↪ ZMod P) :
    let C := (ReedSolomon.code x 16 : Set (Fin (2^126) → ZMod P))
    let ε := 1/(2:ℝ≥0∞)^128
    let b := ((56713727820156410577229101238628035242:ℕ):ℝ≥0)/(2:ℝ≥0)^126
    mcaDeltaStar (F:=ZMod P) C ε=b ∧ ∀ δ, epsMCA (F:=ZMod P) C δ≤ε ↔ δ<b := by
  have length : PrimeThreeLineFamily.length P=2^126 := by decide
  have size : PrimeThreeLineFamily.length P/2^122=16 := by decide
  have budget : P/2^128/3=56713727820156410577229101238628035242 := by decide
  have result := PrimeThreeLineCutoff.classification_254_bits (p:=P) (by decide)
  rw [size,length,budget] at result
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using result x

end ProximityGap.PrimeThreeLine255
#print axioms ProximityGap.PrimeThreeLine255.prime_P
#print axioms ProximityGap.PrimeThreeLine255.generator_order
#print axioms ProximityGap.PrimeThreeLine255.smooth_domain
#print axioms ProximityGap.PrimeThreeLine255.classification
