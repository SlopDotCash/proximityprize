/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ThornerZamanInstance

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 1024` lane

This module packages the concrete `F_1053697` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window. It gives a named
power-of-two rung beyond the `n = 512` wrapper without claiming an exact finite-exception
classification at `n = 1024`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ1024

local instance fact_prime_1053697_concrete_tz1024 : Fact (Nat.Prime 1053697) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `1053697 ∈ [1024^2, 2 * 1024^2]` refutes the canonical
`n = 1024` width-four budget. -/
theorem exists_tzWindow_mu1024_width4_refuter_zmod1053697_beta2 :
    ∃ ζ : ZMod 1053697,
      1053697 ∈ tzWindow 1024 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 1024 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 1024 (1 : ZMod 1053697)) 4).card ≤ 1024 := by
  have hpow : ((1024 : ℕ) : ℝ) ^ (2 : ℝ) = 1048576 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 1053697 ∈ tzWindow 1024 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ1024, hnot⟩ := exists_mu1024_width4_refuter_zmod1053697
  exact ⟨ζ, hpW, hζ1024, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 1024` width-four lane. -/
theorem exists_tzWindow_mu1024_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 1024 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 1024 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 1024 (1 : ZMod p)) 4).card ≤ 1024 := by
  obtain ⟨ζ, hpW, hζ1024, hnot⟩ := exists_tzWindow_mu1024_width4_refuter_zmod1053697_beta2
  exact ⟨1053697, inferInstance, ζ, hpW, hζ1024, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ1024

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ1024

#print axioms exists_tzWindow_mu1024_width4_refuter_zmod1053697_beta2
#print axioms exists_tzWindow_mu1024_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ1024
