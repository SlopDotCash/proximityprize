/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralCapDischarge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralFloor

/-!
# The one-step spectral cap corridor (#407 / #444)

The door-(iv) consumer is now localized to a single one-step squared-spectrum cap

`∀ k, ‖K̂(k)‖² ≤ B`.

`_ResonanceSpectralFloor` proves the necessary lower side: any such uniform cap must satisfy
`m - 1 ≤ B`, because the exact spectral mean is `m - 1`. `_ResonanceSpectralCapDischarge` proves the
sufficient upper side: if `B ≤ 2m log m`, then the resonance conjecture follows at every depth.

This file packages those two facts as the clean corridor for the missing door-(iv) theorem:

`m - 1 ≤ B ≤ 2m log m`.

Honest scope: this proves no cap `B`. It just records the exact nonvacuous window in which a future
anti-concentration/evaluation theorem must land. CORE remains open.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Necessary lower side of any squared spectral cap.** If the one-step kernel spectrum is
uniformly bounded by `B`, then `B` is at least the exact mean `m - 1`. -/
theorem kernelSpectrum_normSq_cap_ge_mean (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {B : ℝ}
    (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    (m : ℝ) - 1 ≤ B :=
  mean_le_of_kernelSpectrum_normSq_le u hu hB

/-- **Necessary lower side of any norm cap.** If `‖K̂(k)‖ ≤ R` uniformly, then `R²` is at
least the exact mean `m - 1`. -/
theorem kernelSpectrum_norm_cap_sq_ge_mean (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {R : ℝ}
    (hR : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ≤ R) :
    (m : ℝ) - 1 ≤ R ^ 2 := by
  exact kernelSpectrum_normSq_cap_ge_mean u hu (B := R ^ 2) fun k =>
    pow_le_pow_left₀ (norm_nonneg _) (hR k) 2

/-- **Squared-cap corridor.** A squared one-step spectral cap strong enough to discharge the
resonance conjecture is automatically squeezed between the spectral floor and the conjectural target:
`m - 1 ≤ B ≤ 2m log m`. -/
theorem kernelSpectrum_normSq_cap_corridor (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {B : ℝ}
    (hBcap : B ≤ 2 * (m : ℝ) * Real.log m)
    (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    (m : ℝ) - 1 ≤ B ∧ B ≤ 2 * (m : ℝ) * Real.log m :=
  ⟨kernelSpectrum_normSq_cap_ge_mean u hu hB, hBcap⟩

/-- **Norm-cap corridor.** In norm form, a cap `R` strong enough to discharge the resonance
conjecture must satisfy `m - 1 ≤ R² ≤ 2m log m`. -/
theorem kernelSpectrum_norm_cap_corridor (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {R : ℝ}
    (hRcap : R ^ 2 ≤ 2 * (m : ℝ) * Real.log m)
    (hR : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ≤ R) :
    (m : ℝ) - 1 ≤ R ^ 2 ∧ R ^ 2 ≤ 2 * (m : ℝ) * Real.log m :=
  ⟨kernelSpectrum_norm_cap_sq_ge_mean u hu hR, hRcap⟩

/-- **No squared cap below the Parseval floor.**  A proposed uniform squared-spectrum cap
`B < m - 1` contradicts the exact spectral mean.  This is the nonvacuity guard for the localized
one-step cap: the door-(iv) theorem cannot ask for a cap below the unavoidable average. -/
theorem not_kernelSpectrum_normSq_cap_lt_mean (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {B : ℝ}
    (hBlt : B < (m : ℝ) - 1) :
    ¬ ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B := by
  intro hB
  exact not_le_of_gt hBlt (kernelSpectrum_normSq_cap_ge_mean u hu hB)

/-- **No norm cap whose square lies below the Parseval floor.**  In norm form, any claimed
`‖K̂(k)‖ ≤ R` must have `m - 1 ≤ R²`; otherwise it contradicts the exact spectral mean. -/
theorem not_kernelSpectrum_norm_cap_sq_lt_mean (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {R : ℝ}
    (hRlt : R ^ 2 < (m : ℝ) - 1) :
    ¬ ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ≤ R := by
  intro hR
  exact not_le_of_gt hRlt (kernelSpectrum_norm_cap_sq_ge_mean u hu hR)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum_normSq_cap_ge_mean
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum_norm_cap_sq_ge_mean
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum_normSq_cap_corridor
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum_norm_cap_corridor
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.not_kernelSpectrum_normSq_cap_lt_mean
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.not_kernelSpectrum_norm_cap_sq_lt_mean
