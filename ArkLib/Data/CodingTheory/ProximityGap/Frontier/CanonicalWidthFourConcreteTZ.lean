/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ThornerZamanInstance

/-!
# Concrete TZ-window refuters for the canonical width-four `n = 32` lane

`E2W4CyclotomicNonCollision` proves that a primitive-root canonical collision at `n = 32`
can only occur in the four characteristics `97, 641, 673, 1153`.  This file composes that exact
finite-exception theorem with the concrete Thorner-Zaman prime-supply rows: a window containing
more than those four exceptions has a prime that refutes the literal width-four `≤ 32` budget.
-/

set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ

local instance fact_prime_1217_concrete_tz : Fact (Nat.Prime 1217) := ⟨by norm_num⟩
local instance fact_prime_1048609_concrete_tz : Fact (Nat.Prime 1048609) := ⟨by norm_num⟩

/-- The exact primitive-root-compatible exceptional characteristics for the canonical `n = 32`
denominator-cleared collision. -/
def canonicalN32PrimitiveBadPrimes : Finset ℕ := {97, 641, 673, 1153}

/-- The exact primitive-compatible `n = 32` exception set has four elements. -/
theorem canonicalN32PrimitiveBadPrimes_card :
    canonicalN32PrimitiveBadPrimes.card = 4 := by
  decide

/-- A TZ supply for `n = 32` larger than the four exact primitive-compatible exceptions produces
a window prime/refuter for the literal canonical width-four `≤ 32` budget. -/
theorem exists_tzWindow_mu32_width4_refuter_of_TZ
    {β : ℝ} {supply : ℕ}
    (hTZ : TZPrimeSupply 32 β supply)
    (hcard : canonicalN32PrimitiveBadPrimes.card < supply) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 32 β ∧
        IsPrimitiveRoot ζ 32 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod p)) 4).card ≤ 32 := by
  classical
  have hcardW : canonicalN32PrimitiveBadPrimes.card < (tzWindow 32 β).card :=
    hcard.trans_le hTZ.le_card
  obtain ⟨p, hpW, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardW
  obtain ⟨hpprime, hpmod, _hlb, _hub⟩ := mem_tzWindow.mp hpW
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨ζ, hζ32⟩ := exists_isPrimitiveRoot_zmod_of_modEq
    (p := p) (n := 32) (by norm_num) hpmod
  have hp97 : p ≠ 97 := by
    intro h
    exact hpnot (by simp [canonicalN32PrimitiveBadPrimes, h])
  have hp641 : p ≠ 641 := by
    intro h
    exact hpnot (by simp [canonicalN32PrimitiveBadPrimes, h])
  have hp673 : p ≠ 673 := by
    intro h
    exact hpnot (by simp [canonicalN32PrimitiveBadPrimes, h])
  have hp1153 : p ≠ 1153 := by
    intro h
    exact hpnot (by simp [canonicalN32PrimitiveBadPrimes, h])
  exact ⟨p, inferInstance, ζ, hpW, hζ32,
    not_e2BadScalarSet_mu32_card_le_32_zmod_of_prime_not_97_641_673_1153
      hp97 hp641 hp673 hp1153 hζ32⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 32` width-four lane. -/
theorem exists_tzWindow_mu32_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 32 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 32 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod p)) 4).card ≤ 32 :=
  exists_tzWindow_mu32_width4_refuter_of_TZ tzPrimeSupply_32_two (by
    rw [canonicalN32PrimitiveBadPrimes_card]
    norm_num)

/-- Fully explicit β=2 witness: `1217 ∈ [32², 2 * 32²]` refutes the canonical `n = 32`
width-four budget. -/
theorem exists_tzWindow_mu32_width4_refuter_zmod1217_beta2 :
    ∃ ζ : ZMod 1217,
      1217 ∈ tzWindow 32 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 32 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod 1217)) 4).card ≤ 32 := by
  have hpow : ((32 : ℕ) : ℝ) ^ (2 : ℝ) = 1024 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 1217 ∈ tzWindow 32 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ32, hnot⟩ := exists_mu32_width4_refuter_zmod1217
  exact ⟨ζ, hpW, hζ32, hnot⟩

/-- Concrete β=3 TZ-window refuter for the canonical `n = 32` width-four lane. -/
theorem exists_tzWindow_mu32_width4_refuter_beta3 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 32 (3 : ℝ) ∧
        IsPrimitiveRoot ζ 32 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod p)) 4).card ≤ 32 :=
  exists_tzWindow_mu32_width4_refuter_of_TZ tzPrimeSupply_32_three (by
    rw [canonicalN32PrimitiveBadPrimes_card]
    norm_num)

/-- Concrete β=4 TZ-window refuter for the canonical `n = 32` width-four lane. -/
theorem exists_tzWindow_mu32_width4_refuter_beta4 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 32 (4 : ℝ) ∧
        IsPrimitiveRoot ζ 32 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod p)) 4).card ≤ 32 :=
  exists_tzWindow_mu32_width4_refuter_of_TZ tzPrimeSupply_32_four (by
    rw [canonicalN32PrimitiveBadPrimes_card]
    norm_num)

/-- Fully explicit β=4 witness: `1048609 ∈ [32⁴, 2 * 32⁴]` refutes the canonical `n = 32`
width-four budget. -/
theorem exists_tzWindow_mu32_width4_refuter_zmod1048609_beta4 :
    ∃ ζ : ZMod 1048609,
      1048609 ∈ tzWindow 32 (4 : ℝ) ∧
        IsPrimitiveRoot ζ 32 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod 1048609)) 4).card ≤ 32 := by
  have hpow : ((32 : ℕ) : ℝ) ^ (4 : ℝ) = 1048576 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 1048609 ∈ tzWindow 32 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ32, hnot⟩ := exists_mu32_width4_refuter_zmod1048609
  exact ⟨ζ, hpW, hζ32, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ

#print axioms canonicalN32PrimitiveBadPrimes_card
#print axioms exists_tzWindow_mu32_width4_refuter_of_TZ
#print axioms exists_tzWindow_mu32_width4_refuter_beta2
#print axioms exists_tzWindow_mu32_width4_refuter_zmod1217_beta2
#print axioms exists_tzWindow_mu32_width4_refuter_beta3
#print axioms exists_tzWindow_mu32_width4_refuter_beta4
#print axioms exists_tzWindow_mu32_width4_refuter_zmod1048609_beta4

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ
