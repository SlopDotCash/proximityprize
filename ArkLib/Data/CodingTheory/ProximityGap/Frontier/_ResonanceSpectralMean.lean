/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceParsevalBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentBaseCase

/-!
# The spectral mean of the one-step Gauss-period kernel (#407 / #444)

Immediate consequence of the Parseval bridge `T r = (1/m) ∑_k |K̂(k)|^{2r}`
(`_ResonanceParsevalBridge.resonanceMoment_eq_spectral_powerMean`) at depth `r = 1`, combined with
the proven base-case value `T 1 = m − 1` for unit-modulus phases
(`_ResonanceMomentBaseCase.resonanceMoment_one_of_unit`):

> **`∑_k ‖kernelSpectrum (dftChar k) u‖² = m·(m − 1)`**, i.e. the spectral mean
> `(1/m) ∑_k |K̂(k)|² = m − 1`.

This pins the FIRST moment of the squared kernel-spectrum profile `{|K̂(k)|²}_k` exactly: its
average over the `m` frequencies is `m − 1`. This is the certain anchor for the power-mean view of
the resonance tower — the weights `w_k = |K̂(k)|²` in `T r = (1/m) ∑_k w_k^r` are nonnegative with
average `m − 1 ≥ 1`. (It is exactly the mean that drives the Chebyshev-sum monotonicity
`(m−1)·T r ≤ T (r+1)`, the matching lower bound to the proven `T(r+1) ≤ (m−1)²·T r` — that
monotonicity is left for a follow-on; here we lock only the mean, which is certain.)

## Honest scope

CERTAIN exact identity (Parseval bridge at `r=1` + base case), not a bound. It pins the FIRST moment
of `{|K̂(k)|²}`; it does NOT bound any individual `|K̂(k)|` — the worst-frequency value (the `max_b`
in CORE) is the open Gauss-period/BGK content, and a flat mean is consistent with a large worst-case
spike. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion / moment /
anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **The spectral mass of the one-step Gauss-period kernel: `∑_k ‖K̂(k)‖² = m·(m − 1)`** for a
unit-modulus phase vector. The Parseval bridge at depth `r = 1` (`∑_k ‖K̂(k)‖^{2·1} = m·T 1`) with the
base-case value `T 1 = m − 1`. The squared kernel-spectrum profile `{|K̂(k)|²}_k` has total mass
`m·(m − 1)` over the `m` frequencies, hence average (spectral mean) `m − 1`. -/
theorem sum_normSq_kernelSpectrum_eq (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    (∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2) = (m : ℝ) * ((m : ℝ) - 1) := by
  classical
  -- bridge at r = 1: m·T 1 = ∑_k ‖K̂(k)‖^{2·1}; rewrite the exponent and use T 1 = m-1.
  have hbridge := resonanceMoment_eq_spectral_powerMean u 1
  -- 2 * 1 = 2, so ∑_k ‖K̂(k)‖^{2*1} = ∑_k ‖K̂(k)‖^2
  simp only [Nat.mul_one] at hbridge
  rw [← hbridge, resonanceMoment_one_of_unit u hu]

/-- **The spectral mean is `m − 1`: `(1/m) ∑_k ‖K̂(k)‖² = m − 1`** (unit-modulus phases).
The average over the `m` frequencies of the squared one-step kernel spectrum. The certain anchor
for the power-mean view `T r = (1/m) ∑_k |K̂(k)|^{2r}` (the average weight is `m − 1 ≥ 1`). -/
theorem spectral_mean_eq (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    ((m : ℝ))⁻¹ * (∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2) = (m : ℝ) - 1 := by
  rw [sum_normSq_kernelSpectrum_eq u hu]
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne m
  rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.sum_normSq_kernelSpectrum_eq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.spectral_mean_eq
