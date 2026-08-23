/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ThornerZamanInstance

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 256` lane

This module packages the concrete `F_65537` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window.  It gives a named, fully
explicit canonical width-four refuter at the next power-of-two rung after `n = 128`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ256

local instance fact_prime_65537_concrete_tz256 : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `65537 ∈ [256², 2 * 256²]` refutes the canonical `n = 256`
width-four budget. -/
theorem exists_tzWindow_mu256_width4_refuter_zmod65537_beta2 :
    ∃ ζ : ZMod 65537,
      65537 ∈ tzWindow 256 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 256 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 256 (1 : ZMod 65537)) 4).card ≤ 256 := by
  have hpow : ((256 : ℕ) : ℝ) ^ (2 : ℝ) = 65536 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 65537 ∈ tzWindow 256 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ256, hnot⟩ := exists_mu256_width4_refuter_zmod65537
  exact ⟨ζ, hpW, hζ256, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 256` width-four lane. -/
theorem exists_tzWindow_mu256_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 256 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 256 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 256 (1 : ZMod p)) 4).card ≤ 256 := by
  obtain ⟨ζ, hpW, hζ256, hnot⟩ := exists_tzWindow_mu256_width4_refuter_zmod65537_beta2
  exact ⟨65537, inferInstance, ζ, hpW, hζ256, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ256

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ256

#print axioms exists_tzWindow_mu256_width4_refuter_zmod65537_beta2
#print axioms exists_tzWindow_mu256_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ256
