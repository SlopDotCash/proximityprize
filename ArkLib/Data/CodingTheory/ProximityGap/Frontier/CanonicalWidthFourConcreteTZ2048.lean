/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 2048` lane

This module packages the concrete `F_4206593` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window. It gives a named
power-of-two rung beyond the `n = 1024` wrapper without claiming an exact finite-exception
classification at `n = 2048`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ2048

local instance fact_prime_4206593_concrete_tz2048 : Fact (Nat.Prime 4206593) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `4206593 ∈ [2048^2, 2 * 2048^2]` refutes the canonical
`n = 2048` width-four budget. -/
theorem exists_tzWindow_mu2048_width4_refuter_zmod4206593_beta2 :
    ∃ ζ : ZMod 4206593,
      4206593 ∈ tzWindow 2048 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 2048 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 2048 (1 : ZMod 4206593)) 4).card ≤
            2048 := by
  have hpow : ((2048 : ℕ) : ℝ) ^ (2 : ℝ) = 4194304 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 4206593 ∈ tzWindow 2048 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ2048, hnot⟩ := exists_mu2048_width4_refuter_zmod4206593
  exact ⟨ζ, hpW, hζ2048, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 2048` width-four lane. -/
theorem exists_tzWindow_mu2048_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 2048 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 2048 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 2048 (1 : ZMod p)) 4).card ≤ 2048 := by
  obtain ⟨ζ, hpW, hζ2048, hnot⟩ := exists_tzWindow_mu2048_width4_refuter_zmod4206593_beta2
  exact ⟨4206593, inferInstance, ζ, hpW, hζ2048, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ2048

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ2048

#print axioms exists_tzWindow_mu2048_width4_refuter_zmod4206593_beta2
#print axioms exists_tzWindow_mu2048_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ2048
