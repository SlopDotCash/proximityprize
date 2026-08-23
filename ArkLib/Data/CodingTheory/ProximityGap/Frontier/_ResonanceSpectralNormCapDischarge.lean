/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralCapDischarge

/-!
# Norm-form one-step spectral cap discharges the resonance conjecture (#407 / #444)

`_ResonanceSpectralCapDischarge` gives the squared-spectrum consumer:
`∀ k, ‖K̂(k)‖² ≤ B ⟹ T r ≤ B^r`.

This file packages the same door-(iv) target in the more natural sup-norm form: if every one-step
frequency satisfies `‖K̂(k)‖ ≤ R`, then `T r ≤ (R²)^r`; if moreover `R² ≤ 2m log m`, then
`ResonanceConjecture u r` follows.

## Honest scope

This proves no new upper bound on `R`. It is a clean API for the exact missing theorem: a direct
worst-frequency estimate for the one-step Gauss-period kernel, avoiding moment/completion losses.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Norm cap ⇒ depth-`r` resonance-moment cap.** A uniform one-step bound `‖K̂(k)‖ ≤ R` gives
`T r ≤ (R²)^r` by squaring the cap and invoking the squared-spectrum consumer. -/
theorem resonanceMoment_le_of_kernelSpectrum_norm_le (u : ZMod m → ℂ) (r : ℕ) {R : ℝ}
    (hR : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ≤ R) :
    resonanceMoment u r ≤ (R ^ 2) ^ r := by
  refine resonanceMoment_le_of_kernelSpectrum_normSq_le u r ?_
  intro k
  exact pow_le_pow_left₀ (norm_nonneg _) (hR k) 2

/-- **Door-(iv) norm-cap consumer.** A one-step worst-frequency norm cap whose square is at most
`2m log m` proves `ResonanceConjecture u r`. This is the natural sup-norm API for the remaining
anti-concentration/evaluation target. -/
theorem resonanceConjecture_of_kernelSpectrum_norm_le (u : ZMod m → ℂ) (r : ℕ) {R : ℝ}
    (hRcap : R ^ 2 ≤ 2 * (m : ℝ) * Real.log m)
    (hR : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ≤ R) :
    ResonanceConjecture u r := by
  refine resonanceConjecture_of_kernelSpectrum_normSq_le u r (sq_nonneg R) hRcap ?_
  intro k
  exact pow_le_pow_left₀ (norm_nonneg _) (hR k) 2

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_le_of_kernelSpectrum_norm_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceConjecture_of_kernelSpectrum_norm_le
