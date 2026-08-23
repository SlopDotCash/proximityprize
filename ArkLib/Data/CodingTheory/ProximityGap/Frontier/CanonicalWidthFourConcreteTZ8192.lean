/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 8192` lane

This module packages the concrete `F_67731457` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window. It gives a named
power-of-two rung beyond the `n = 4096` wrapper without claiming an exact finite-exception
classification at `n = 8192`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ8192

local instance fact_prime_67731457_concrete_tz8192 : Fact (Nat.Prime 67731457) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `67731457 ∈ [8192^2, 2 * 8192^2]` refutes the canonical
`n = 8192` width-four budget. -/
theorem exists_tzWindow_mu8192_width4_refuter_zmod67731457_beta2 :
    ∃ ζ : ZMod 67731457,
      67731457 ∈ tzWindow 8192 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 8192 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 8192 (1 : ZMod 67731457)) 4).card ≤
            8192 := by
  have hpow : ((8192 : ℕ) : ℝ) ^ (2 : ℝ) = 67108864 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 67731457 ∈ tzWindow 8192 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ8192, hnot⟩ := exists_mu8192_width4_refuter_zmod67731457
  exact ⟨ζ, hpW, hζ8192, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 8192` width-four lane. -/
theorem exists_tzWindow_mu8192_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 8192 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 8192 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 8192 (1 : ZMod p)) 4).card ≤ 8192 := by
  obtain ⟨ζ, hpW, hζ8192, hnot⟩ := exists_tzWindow_mu8192_width4_refuter_zmod67731457_beta2
  exact ⟨67731457, inferInstance, ζ, hpW, hζ8192, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ8192

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ8192

#print axioms exists_tzWindow_mu8192_width4_refuter_zmod67731457_beta2
#print axioms exists_tzWindow_mu8192_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ8192
