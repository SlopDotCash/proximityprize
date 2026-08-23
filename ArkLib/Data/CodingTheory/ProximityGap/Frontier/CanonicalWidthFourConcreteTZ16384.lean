/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 16384` lane

This module packages the concrete `F_268730369` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window. It gives a named
power-of-two rung beyond the `n = 8192` wrapper without claiming an exact finite-exception
classification at `n = 16384`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ16384

local instance fact_prime_268730369_concrete_tz16384 : Fact (Nat.Prime 268730369) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `268730369 ∈ [16384^2, 2 * 16384^2]` refutes the canonical
`n = 16384` width-four budget. -/
theorem exists_tzWindow_mu16384_width4_refuter_zmod268730369_beta2 :
    ∃ ζ : ZMod 268730369,
      268730369 ∈ tzWindow 16384 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 16384 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 16384 (1 : ZMod 268730369)) 4).card ≤
            16384 := by
  have hpow : ((16384 : ℕ) : ℝ) ^ (2 : ℝ) = 268435456 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 268730369 ∈ tzWindow 16384 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ16384, hnot⟩ := exists_mu16384_width4_refuter_zmod268730369
  exact ⟨ζ, hpW, hζ16384, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 16384` width-four lane. -/
theorem exists_tzWindow_mu16384_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 16384 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 16384 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 16384 (1 : ZMod p)) 4).card ≤
            16384 := by
  obtain ⟨ζ, hpW, hζ16384, hnot⟩ := exists_tzWindow_mu16384_width4_refuter_zmod268730369_beta2
  exact ⟨268730369, inferInstance, ζ, hpW, hζ16384, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ16384

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ16384

#print axioms exists_tzWindow_mu16384_width4_refuter_zmod268730369_beta2
#print axioms exists_tzWindow_mu16384_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ16384
