/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ThornerZamanInstance

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 512` lane

This module packages the concrete `F_262657` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the beta=2 Thorner-Zaman window.  It gives a named
power-of-two rung beyond the `n = 256` wrapper without claiming an exact finite-exception
classification at `n = 512`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ512

local instance fact_prime_262657_concrete_tz512 : Fact (Nat.Prime 262657) := ⟨by norm_num⟩

/-- Fully explicit beta=2 witness: `262657 ∈ [512^2, 2 * 512^2]` refutes the canonical
`n = 512` width-four budget. -/
theorem exists_tzWindow_mu512_width4_refuter_zmod262657_beta2 :
    ∃ ζ : ZMod 262657,
      262657 ∈ tzWindow 512 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 512 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 512 (1 : ZMod 262657)) 4).card ≤ 512 := by
  have hpow : ((512 : ℕ) : ℝ) ^ (2 : ℝ) = 262144 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 262657 ∈ tzWindow 512 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ512, hnot⟩ := exists_mu512_width4_refuter_zmod262657
  exact ⟨ζ, hpW, hζ512, hnot⟩

/-- Concrete beta=2 TZ-window refuter for the canonical `n = 512` width-four lane. -/
theorem exists_tzWindow_mu512_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 512 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 512 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 512 (1 : ZMod p)) 4).card ≤ 512 := by
  obtain ⟨ζ, hpW, hζ512, hnot⟩ := exists_tzWindow_mu512_width4_refuter_zmod262657_beta2
  exact ⟨262657, inferInstance, ζ, hpW, hζ512, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ512

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ512

#print axioms exists_tzWindow_mu512_width4_refuter_zmod262657_beta2
#print axioms exists_tzWindow_mu512_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ512
