/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceParsevalBridge

/-!
# Uniform one-step spectral cap discharges the resonance conjecture (#407 / #444)

The Parseval bridge says

`m · T r = ∑ k, ‖K̂(k)‖^(2r) = ∑ k, (‖K̂(k)‖²)^r`.

This file records the direct consumer lemma for door (iv): if the one-step Gauss-period kernel has a
uniform squared-spectrum cap `‖K̂(k)‖² ≤ B`, then the whole depth-`r` resonance moment satisfies
`T r ≤ B^r`. In particular, a cap `B ≤ 2m log m` proves `ResonanceConjecture u r`.

## Honest scope

This does not prove such a cap. It isolates the exact remaining target: a non-moment, non-completion
upper bound on the one-step worst-frequency spectrum. The previous floor file shows any such cap
must also satisfy `m − 1 ≤ B`; this file gives the matching upper-consumer direction.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Uniform one-step spectral cap ⇒ depth-`r` resonance-moment cap.** If every one-step
kernel-spectrum frequency has squared norm at most `B`, then the Parseval power mean gives
`T r ≤ B^r`. This is the exact consumer form of a door-(iv) worst-frequency bound. -/
theorem resonanceMoment_le_of_kernelSpectrum_normSq_le (u : ZMod m → ℂ) (r : ℕ) {B : ℝ}
    (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    resonanceMoment u r ≤ B ^ r := by
  classical
  have hmpos_nat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hbridge := resonanceMoment_eq_spectral_powerMean u r
  have hpow : (∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ (2 * r))
      ≤ ∑ _k : ZMod m, B ^ r := by
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hsq_nonneg : 0 ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2 := by positivity
    have hsq_pow : (‖kernelSpectrum (dftChar k) u‖ ^ 2) ^ r ≤ B ^ r :=
      pow_le_pow_left₀ hsq_nonneg (hB k) r
    simpa [pow_mul] using hsq_pow
  have hconst : (∑ _k : ZMod m, B ^ r) = (m : ℝ) * B ^ r := by
    simp [ZMod.card]
  have hmul : (m : ℝ) * resonanceMoment u r ≤ (m : ℝ) * B ^ r := by
    calc (m : ℝ) * resonanceMoment u r
        = ∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ (2 * r) := hbridge
      _ ≤ ∑ _k : ZMod m, B ^ r := hpow
      _ = (m : ℝ) * B ^ r := hconst
  exact le_of_mul_le_mul_left hmul hmpos

/-- **Door-(iv) consumer capstone.** A squared one-step spectral cap `B ≤ 2m log m` immediately
proves `ResonanceConjecture u r`. The theorem proves no cap itself; it pins the exact target any new
anti-concentration theorem must supply. -/
theorem resonanceConjecture_of_kernelSpectrum_normSq_le (u : ZMod m → ℂ) (r : ℕ) {B : ℝ}
    (hB0 : 0 ≤ B) (hBcap : B ≤ 2 * (m : ℝ) * Real.log m)
    (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    ResonanceConjecture u r := by
  unfold ResonanceConjecture
  exact (resonanceMoment_le_of_kernelSpectrum_normSq_le u r hB).trans
    (pow_le_pow_left₀ hB0 hBcap r)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_le_of_kernelSpectrum_normSq_le
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceConjecture_of_kernelSpectrum_normSq_le
