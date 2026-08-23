/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2W4CyclotomicConcreteWitnesses
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman

/-!
# Concrete TZ-window refuter for the canonical width-four `n = 32768` lane

This module packages the concrete `F_1073872897` primitive-root witness from
`E2W4CyclotomicConcreteWitnesses` with the β=2 Thorner-Zaman window. It gives a named
power-of-two rung beyond the `n = 16384` wrapper without claiming an exact finite-exception
classification at `n = 32768`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.E2W4CyclotomicNonCollision
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ32768

local instance fact_prime_1073872897_concrete_tz32768 :
    Fact (Nat.Prime 1073872897) := ⟨by norm_num⟩

/-- Fully explicit β=2 witness: `1073872897 ∈ [32768^2, 2 * 32768^2]` refutes the
canonical `n = 32768` width-four budget. -/
theorem exists_tzWindow_mu32768_width4_refuter_zmod1073872897_beta2 :
    ∃ ζ : ZMod 1073872897,
      1073872897 ∈ tzWindow 32768 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 32768 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32768 (1 : ZMod 1073872897)) 4).card ≤
            32768 := by
  have hpow : ((32768 : ℕ) : ℝ) ^ (2 : ℝ) = 1073741824 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpW : 1073872897 ∈ tzWindow 32768 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  obtain ⟨ζ, hζ32768, hnot⟩ := exists_mu32768_width4_refuter_zmod1073872897
  exact ⟨ζ, hpW, hζ32768, hnot⟩

/-- Concrete β=2 TZ-window refuter for the canonical `n = 32768` width-four lane. -/
theorem exists_tzWindow_mu32768_width4_refuter_beta2 :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      p ∈ tzWindow 32768 (2 : ℝ) ∧
        IsPrimitiveRoot ζ 32768 ∧
          ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32768 (1 : ZMod p)) 4).card ≤
            32768 := by
  obtain ⟨ζ, hpW, hζ32768, hnot⟩ :=
    exists_tzWindow_mu32768_width4_refuter_zmod1073872897_beta2
  exact ⟨1073872897, inferInstance, ζ, hpW, hζ32768, hnot⟩

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ32768

namespace ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ32768

#print axioms exists_tzWindow_mu32768_width4_refuter_zmod1073872897_beta2
#print axioms exists_tzWindow_mu32768_width4_refuter_beta2

end ArkLib.ProximityGap.Frontier.CanonicalWidthFourConcreteTZ32768
