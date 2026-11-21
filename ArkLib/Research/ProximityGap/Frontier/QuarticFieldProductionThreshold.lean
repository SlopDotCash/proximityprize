/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionThreeHeadWindow
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.ReduceModChar

/-! # An exact production-length crossing over a quartic extension

The field has order `912680550401^4`. Its prime subfield supplies a primitive
root of order `2^30`. The three-head interval gives the same first failure
for more than twelve million dimensions on this smooth domain.
-/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.QuarticFieldProductionThreshold
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity

/-- Characteristic of the quartic extension. -/
abbrev p : ℕ := 912680550401

/-- Lucas primality certificate with generator three. -/
theorem prime_p : p.Prime := by
  have hm : (3 : ZMod p)^(p-1) = 1 := by reduce_mod_char
  refine lucas_primality p 3 hm ?_
  intro v hv hd
  rw [show p-1 = 2^31*(5^2*17) by decide] at hd
  rcases hv.dvd_mul.mp hd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow h)
    subst v
    reduce_mod_char
    decide
  · rcases hv.dvd_mul.mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 5)).mp (hv.dvd_of_dvd_pow h)
      subst v
      reduce_mod_char
      decide
    · have := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 17)).mp h
      subst v
      reduce_mod_char
      decide

instance : Fact p.Prime := ⟨prime_p⟩

/-- The finite extension field of degree four. -/
abbrev K := GaloisField p 4

instance : Fintype K := Fintype.ofFinite K
instance : DecidableEq K := Classical.decEq K

/-- The subgroup of all production-length roots of unity. -/
def H : Subgroup Kˣ := rootsOfUnity n K

instance : Fintype H := Fintype.ofFinite H

theorem card_H : Fintype.card H = n := by
  have h : IsPrimitiveRoot (488776197412 : ZMod p) n := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    apply orderOf_eq_prime_pow (p := 2) (n := 29)
    · change (488776197412 : ZMod p)^536870912 ≠ 1
      reduce_mod_char
      decide
    · change (488776197412 : ZMod p)^1073741824 = 1
      reduce_mod_char
  rw [← Nat.card_eq_fintype_card]
  exact (h.map_of_injective (algebraMap (ZMod p) K).injective).card_rootsOfUnity

/-- Inclusion of the entire subgroup into the extension field. -/
def domain : H ↪ K :=
  ⟨fun i => ((i : Kˣ) : K), fun _ _ h => Subtype.ext (Units.ext h)⟩

instance : ReedSolomon.Smooth domain where
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

theorem budget : Fintype.card K / 2^128 = 2039086914 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p 4 (by decide)]
  decide

/-- On this smooth quartic-extension code the first failure occurs at
679,695,638 errors for every listed message dimension and every positive width. -/
theorem classification {d : ℕ} (hd : 54198367 ≤ d) (hd' : d ≤ 67108864)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code domain d : Set (H → K)) ^⋈ (Fin width)
    let t : ℝ≥0 := 679695638/1073741824
    mcaDeltaStar (F := K) C tolerance = t ∧
      ∀ δ : ℝ≥0, epsMCA (F := K) C δ ≤ tolerance ↔ δ < t := by
  have h := DimensionThreeHeadWindow.classification domain card_H (p := p) (by decide) budget
    (by decide) (by decide) (by omega : 2 ≤ d) hd'
    (by change 1182138558 ≤ 1073741824+2*d; omega) width
  simpa only [Nat.reduceDiv, Nat.cast_ofNat, n] using h

/-- At dimension one the same smooth code remains safe through 791,036,486 errors. -/
theorem dimension_one (width : ℕ) [NeZero width] :
    epsMCA (F := K) ((ReedSolomon.code domain 1 : Set (H → K)) ^⋈ (Fin width))
      (791036486/1073741824) ≤ tolerance := by
  have h := DimensionThreeHeadWindow.dimension_one_safe domain card_H (e := 791036486) budget
    (by decide) (by rw [Nat.choose_two_right]; decide) width
  simpa only [Nat.cast_ofNat, n] using h

#print axioms dimension_one
#print axioms classification
end ArkLib.ProximityGap.Frontier.QuarticFieldProductionThreshold
