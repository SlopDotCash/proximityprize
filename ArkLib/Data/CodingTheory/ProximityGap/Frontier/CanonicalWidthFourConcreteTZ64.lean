/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ThornerZamanInstance

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 64` lane

This module packages the concrete `F_4289` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window.  It gives a named, fully
explicit `n = 64` literal-budget refuter without claiming an exact finite-exception classification
at `n = 64`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ64

local instance fact_prime_4289_concrete_tz64 : Fact (Nat.Prime 4289) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `4289 ∈ [64², 2 * 64²]` refutes the canonical `n = 64`
width-four budget. -/
theorem exists_tzWindow_mu64_width4_refuter_zmod4289_beta2 :
    ∃ ζ : ZMod 4289,
      4289 ∈ tzWindow 64 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 64 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 64 (1 : ZMod 4289)) 4).card ≤ 64 := by
  have hpow : ((64 : ℕ) : ℝ) ^ (2 : ℝ) = 4096 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 4289 ∈ tzWindow 64 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ64, hnot⟩ := exists_mu64_width4_refuter_zmod4289
  exact ⟨ζ, hpW, hζ64, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 64` width-four lane. -/
theorem exists_tzWindow_mu64_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 64 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 64 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 64 (1 : ZMod p)) 4).card ≤ 64 := by
  obtain ⟨ζ, hpW, hζ64, hnot⟩ := exists_tzWindow_mu64_width4_refuter_zmod4289_beta2
  exact ⟨4289, inferInstance, ζ, hpW, hζ64, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ64

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ64

#print axioms exists_tzWindow_mu64_width4_refuter_zmod4289_beta2
#print axioms exists_tzWindow_mu64_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ64
