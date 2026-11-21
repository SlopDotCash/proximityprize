/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CubicHalfDistancePlateau
import ArkLib.Research.ProximityGap.Frontier.OddSmoothPrimeThreshold
import ArkLib.Research.ProximityGap.Support.BinaryPower
import ArkLib.Research.ProximityGap.Support.DyadicPowerDomain
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-! # A smooth prime field at the odd-redundancy transition near rate one eighth

The integer 128-bit budget equals half the rounded-up redundancy at dimension
134217727 on a length-2³⁰ domain. Its odd parity changes the first failure
between two adjacent dimensions.
-/
set_option autoImplicit false
namespace ProximityGap.SmoothParityPrime157
open MCAThresholdLedger
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open scoped NNReal ENNReal

/-- The order multiplier for a smooth prime field with integer budget 469762049. -/
abbrev multiplier : ℕ := 240518169179

private theorem multiplier_prime : Nat.Prime multiplier := by
  apply lucas_primality multiplier 2 (by rw [← binaryPow_eq_pow]; decide)
  intro v hv hd
  rw [show multiplier-1 = 2*(7*(229*(2417*31039))) by decide] at hd
  rcases hv.dvd_mul.mp hd with factor | hd
  · have eqv := (Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 2)).mp factor
    subst v
    rw [← binaryPow_eq_pow]
    decide
  rcases hv.dvd_mul.mp hd with factor | hd
  · have eqv := (Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 7)).mp factor
    subst v
    rw [← binaryPow_eq_pow]
    decide
  rcases hv.dvd_mul.mp hd with factor | hd
  · have eqv := (Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 229)).mp factor
    subst v
    rw [← binaryPow_eq_pow]
    decide
  rcases hv.dvd_mul.mp hd with factor | hd
  · have eqv := (Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 2417)).mp factor
    subst v
    rw [← binaryPow_eq_pow]
    decide
  have eqv := (Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 31039)).mp hd
  subst v
  rw [← binaryPow_eq_pow]
  decide

/-- The 157-bit prime 240518169179·2¹¹⁹+1. -/
abbrev p : ℕ := 159851741983829747407680164258841283949391511553

set_option maxRecDepth 100000 in
theorem prime_p : Nat.Prime p := by
  apply lucas_primality p 3 (by rw [← binaryPow_eq_pow]; decide)
  intro v hv hd
  rw [show p-1 = 2^119*multiplier by decide] at hd
  rcases hv.dvd_mul.mp hd with two | large
  · have eqv := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow two)
    subst v
    rw [← binaryPow_eq_pow]
    decide
  · have eqv := (Nat.prime_dvd_prime_iff_eq hv multiplier_prime).mp large
    subst v
    rw [← binaryPow_eq_pow]
    decide

instance : Fact p.Prime := ⟨prime_p⟩

/-- A generator of the length-2³⁰ subgroup. -/
def generator : (ZMod p)ˣ := Units.mk0 79683576485643376276792320464234886136900769133 (by decide)

set_option maxRecDepth 100000 in
theorem generator_order : orderOf generator = 2^30 := by
  rw [← orderOf_units]
  apply orderOf_eq_prime_pow (p := 2) (n := 29) <;> rw [← binaryPow_eq_pow] <;> decide

/-- The power domain at the prize length. -/
def domain : Fin (2^30) ↪ ZMod p := MCADeltaStarLiteralEps.smoothDom p generator generator_order

noncomputable instance smooth : ReedSolomon.Smooth domain :=
  DyadicPowerDomain.smooth generator generator_order

theorem budget : p/2^128 = 469762049 := by decide


/-- A literal real first-failure radius and its full safe interval. -/
def Cutoff (x : Fin 1073741824 ↪ ZMod p) (k j width : ℕ) [NeZero width] : Prop :=
  let C := (ReedSolomon.code x k : Set (Fin 1073741824 → ZMod p)) ^⋈ (Fin width)
  mcaDeltaStar (F:=ZMod p) C (1 / ((2^128:ℕ):ℝ≥0∞)) = (j:ℝ≥0)/1073741824 ∧
    ∀ δ, epsMCA (F:=ZMod p) C δ ≤ 1 / ((2^128:ℕ):ℝ≥0∞) ↔ δ < (j:ℝ≥0)/1073741824

private theorem even_cut (x : Fin 1073741824 ↪ ZMod p) {k h : ℕ} (hk : 2 ≤ k)
    (len : k+2*h=1073741824) (rate : 1073741824<3*h) (range : 469762049≤2*h+1)
    (width : ℕ) [NeZero width] : Cutoff x k (min 469762049 h) width := by
  have result := ArkLib.ProximityGap.Frontier.ApolarAllFieldPlateau.classification
    (a:=h) (B:=469762049) (Q:=2^128) x hk (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin])
    (by decide) (by simpa only [ZMod.card] using budget) range width
  dsimp only at result
  rw [Fintype.card_fin] at result
  exact result

/-- On arbitrary embeddings the four official dimensions have the displayed
cutoffs, including all positive interleaving widths. -/
theorem four_rates (x : Fin 1073741824 ↪ ZMod p) (width : ℕ) [NeZero width] :
    Cutoff x 536870912 268435456 width ∧ Cutoff x 268435456 402653184 width ∧
      Cutoff x 134217728 469762048 width ∧ Cutoff x 67108864 469762049 width := by
  have hb : Fintype.card (ZMod p)/2^128=469762049 := by simpa only [ZMod.card] using budget
  have hh := CubicHalfDistancePlateau.classification (k:=536870912) (h:=268435456) x (by decide)
    (by decide) (by decide) (by decide) (by decide : 0<2^128) hb (by decide) width
  have step := CubicHalfDistancePlateau.index_eq_min (k:=536870912) (h:=268435456) x (by decide)
    (by decide) (by decide) (by decide) (by decide : 0<2^128) hb (Or.inr (by decide))
  dsimp only at hh
  rw [step] at hh
  exact ⟨hh,even_cut (h:=402653184) x (by decide) (by decide) (by decide) (by decide) width,
    even_cut (h:=469762048) x (by decide) (by decide) (by decide) (by decide) width,
    even_cut (h:=503316480) x (by decide) (by decide) (by decide) (by decide) width⟩

/-- At dimension two below the one-eighth prize dimension the last safe
count is one larger than at the intervening odd dimension. -/
theorem adjacent (x : Fin 1073741824 ↪ ZMod p) [ReedSolomon.Smooth x] (width : ℕ) [NeZero width] :
    Cutoff x 134217726 469762049 width ∧ Cutoff x 134217727 469762048 width := by
  refine ⟨even_cut (h:=469762049) x (by decide) (by decide) (by decide) (by decide) width,?_⟩
  exact OddSmoothPrimeThreshold.exceptional (k:=134217727) (h:=469762049) (Q:=2^128) x
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa only [ZMod.card] using budget) width

end ProximityGap.SmoothParityPrime157
#print axioms ProximityGap.SmoothParityPrime157.prime_p
#print axioms ProximityGap.SmoothParityPrime157.smooth
#print axioms ProximityGap.SmoothParityPrime157.four_rates
#print axioms ProximityGap.SmoothParityPrime157.adjacent
