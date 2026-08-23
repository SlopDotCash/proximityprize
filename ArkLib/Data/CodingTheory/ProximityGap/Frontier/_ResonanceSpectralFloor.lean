/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralMean

/-!
# The one-step resonance spectral floor (#407 / #444)

`_ResonanceSpectralMean` pins the exact first moment of the one-step Gauss-period kernel:

`∑ k, ‖K̂(k)‖² = m·(m − 1)`.

This file extracts the unavoidable max/RMS consequence: at least one frequency has
`‖K̂(k)‖² ≥ m − 1`, and therefore any proposed uniform bound on the squared one-step spectrum must
be at least `m − 1`.

## Honest scope

This is a FLOOR / obstruction lemma only. It gives no upper bound on the worst frequency and makes
no CORE/prize cancellation claim. It simply records, axiom-clean, the Plancherel floor that any
door-(iv) anti-concentration theorem must beat from above: the spectral profile cannot be uniformly
below its exact mean.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **One-step spectral floor.** For any unit-modulus phase vector, some frequency has squared
one-step kernel spectrum at least the exact mean `m − 1`. This is just the finite average principle
applied to `∑ k, ‖K̂(k)‖² = m·(m−1)`. It is a lower floor, not an upper bound on the
worst frequency. -/
theorem exists_kernelSpectrum_normSq_ge_mean (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    ∃ k : ZMod m, (m : ℝ) - 1 ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2 := by
  classical
  have hsum := sum_normSq_kernelSpectrum_eq u hu
  have hconst : (∑ _k : ZMod m, ((m : ℝ) - 1)) = (m : ℝ) * ((m : ℝ) - 1) := by
    simp [ZMod.card]
    ring
  have hle : (∑ _k : ZMod m, ((m : ℝ) - 1))
      ≤ ∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 := by
    rw [hconst, hsum]
  obtain ⟨k, _hk_mem, hk⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (ZMod m))) (f := fun _ => ((m : ℝ) - 1))
    (g := fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2) Finset.univ_nonempty hle
  exact ⟨k, hk⟩

/-- **Uniform upper bounds must clear the Parseval floor.** If a number `B` bounds every squared
one-step kernel-spectrum frequency, then `m − 1 ≤ B`. Thus any door-(iv) upper-bound theorem cannot
push the whole spectrum below the exact mean. -/
theorem mean_le_of_kernelSpectrum_normSq_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    {B : ℝ} (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    (m : ℝ) - 1 ≤ B := by
  obtain ⟨k, hk⟩ := exists_kernelSpectrum_normSq_ge_mean u hu
  exact hk.trans (hB k)

/-- **No strict-below-mean spectrum.** The squared one-step kernel spectrum cannot be strictly below
`m − 1` at every frequency. This is the contradiction form of the same Plancherel floor. -/
theorem not_forall_kernelSpectrum_normSq_lt_mean (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    ¬ (∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 < (m : ℝ) - 1) := by
  rintro hlt
  obtain ⟨k, hk⟩ := exists_kernelSpectrum_normSq_ge_mean u hu
  exact not_lt_of_ge hk (hlt k)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.exists_kernelSpectrum_normSq_ge_mean
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.mean_le_of_kernelSpectrum_normSq_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.not_forall_kernelSpectrum_normSq_lt_mean
