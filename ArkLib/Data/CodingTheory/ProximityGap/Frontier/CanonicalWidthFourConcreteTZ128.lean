/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ThornerZamanInstance

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 128` lane

This module packages the concrete `F_17921` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window.  It extends the direct
canonical width-four refuter ladder one smooth-domain rung past the `n = 64` wrapper.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ128

local instance fact_prime_17921_concrete_tz128 : Fact (Nat.Prime 17921) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `17921 ∈ [128², 2 * 128²]` refutes the canonical `n = 128`
width-four budget. -/
theorem exists_tzWindow_mu128_width4_refuter_zmod17921_beta2 :
    ∃ ζ : ZMod 17921,
      17921 ∈ tzWindow 128 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 128 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 128 (1 : ZMod 17921)) 4).card ≤ 128 := by
  have hpow : ((128 : ℕ) : ℝ) ^ (2 : ℝ) = 16384 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 17921 ∈ tzWindow 128 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ128, hnot⟩ := exists_mu128_width4_refuter_zmod17921
  exact ⟨ζ, hpW, hζ128, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 128` width-four lane. -/
theorem exists_tzWindow_mu128_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 128 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 128 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 128 (1 : ZMod p)) 4).card ≤ 128 := by
  obtain ⟨ζ, hpW, hζ128, hnot⟩ := exists_tzWindow_mu128_width4_refuter_zmod17921_beta2
  exact ⟨17921, inferInstance, ζ, hpW, hζ128, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ128

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ128

#print axioms exists_tzWindow_mu128_width4_refuter_zmod17921_beta2
#print axioms exists_tzWindow_mu128_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ128
