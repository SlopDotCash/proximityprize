/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 4096` lane

This module packages the concrete `F_16957441` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window. It gives a named
power-of-two rung beyond the `n = 2048` wrapper without claiming an exact finite-exception
classification at `n = 4096`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ4096

local instance fact_prime_16957441_concrete_tz4096 : Fact (Nat.Prime 16957441) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `16957441 ∈ [4096^2, 2 * 4096^2]` refutes the canonical
`n = 4096` width-four budget. -/
theorem exists_tzWindow_mu4096_width4_refuter_zmod16957441_beta2 :
    ∃ ζ : ZMod 16957441,
      16957441 ∈ tzWindow 4096 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 4096 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 4096 (1 : ZMod 16957441)) 4).card ≤
            4096 := by
  have hpow : ((4096 : ℕ) : ℝ) ^ (2 : ℝ) = 16777216 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 16957441 ∈ tzWindow 4096 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ4096, hnot⟩ := exists_mu4096_width4_refuter_zmod16957441
  exact ⟨ζ, hpW, hζ4096, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 4096` width-four lane. -/
theorem exists_tzWindow_mu4096_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 4096 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 4096 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 4096 (1 : ZMod p)) 4).card ≤ 4096 := by
  obtain ⟨ζ, hpW, hζ4096, hnot⟩ := exists_tzWindow_mu4096_width4_refuter_zmod16957441_beta2
  exact ⟨16957441, inferInstance, ζ, hpW, hζ4096, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ4096

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ4096

#print axioms exists_tzWindow_mu4096_width4_refuter_zmod16957441_beta2
#print axioms exists_tzWindow_mu4096_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ4096
