/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectrumModulusLaw
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDFTParseval

/-!
# The Parseval bridge: the resonance moment as the spectral power-mean (#407 / #444)

This file lands the BRIDGE the door-(iv) campaign kept stalling before: the real-space resonance
moment `T r = ∑_c ‖phaseSum u r c‖²` (the named `√p`-free free variable) equals the spectral
`2r`-th power-mean of the ONE-step Gauss-period kernel:

> **`(m : ℝ)·(resonanceMoment u r) = ∑_k ‖kernelSpectrum (ψ_k) u‖^{2r}`**,
> i.e. `T r = (1/m) ∑_k |K̂(k)|^{2r}`,

where `ψ_k(c) = stdAddChar (−(c·k))` is the `k`-th additive character of `ZMod m` and
`K̂(k) = kernelSpectrum (ψ_k) u = ∑_{a≠0} u(a)·ψ_k(a)` is the one-step kernel spectrum at frequency
`k`. This is assembled from three already-proven, certain pieces:

* `dft_parseval` (`_ZModDFTParseval`): `∑_k ‖𝓕 Φ k‖² = m·∑_j ‖Φ j‖²` (Plancherel on `ZMod m`).
* `phaseSpectrum_eq_kernelSpectrum_pow` (`_ResonancePhaseSpectrumRecursion`): `ξ̂_r = K̂^r`.
* `normSq_phaseSpectrum_eq` (`_ResonanceSpectrumModulusLaw`): `‖ξ̂_r‖² = ‖K̂‖^{2r}` (the summand).

The Fourier transform `𝓕 (phaseSum u r) k = ∑_c stdAddChar(−(c·k))·phaseSum u r c` is exactly
`phaseSpectrum (ψ_k) u r` for the character `ψ_k`, so each DFT coefficient is `K̂(k)^r` and its
squared modulus is `|K̂(k)|^{2r}`. Summing and applying Plancherel gives the bridge.

## Why this is the high-value capstone

With this bridge the entire `r`-tower of the named free variable is the `2r`-th power-mean of ONE
function's spectrum `{K̂(k)}_k`. It makes the localization to the one-step Gauss-period kernel
PRECISE and citable, and it is the rung that turns spectral facts about `{|K̂(k)|²}` (e.g. the
mean `(1/m)∑_k|K̂(k)|² = m−1`, and Chebyshev-sum monotonicity) into statements about `T r` directly.

## Honest scope

CERTAIN exact identity (Plancherel + the proven spectral iterate), not a bound. It does NOT bound
`K̂(k)` — that spectral profile IS the open Gauss-period/BGK content; the bridge merely RE-EXPRESSES
`T r` through it. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion /
moment / anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators ComplexConjugate
open ProximityGap.Frontier.ZModDFTParseval

variable {m : ℕ} [NeZero m]

/-- The `k`-th additive character of `ZMod m` used by the `ZMod` DFT: `ψ_k(c) = stdAddChar(−(c·k))`. -/
noncomputable def dftChar (k : ZMod m) : ZMod m → ℂ := fun c => stdAddChar (-(c * k))

/-- `dftChar k` is multiplicative for addition: `ψ_k(x+y) = ψ_k(x)·ψ_k(y)`. -/
theorem dftChar_add (k : ZMod m) (x y : ZMod m) :
    dftChar k (x + y) = dftChar k x * dftChar k y := by
  unfold dftChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- `dftChar k 0 = 1`. -/
theorem dftChar_zero (k : ZMod m) : dftChar k 0 = 1 := by
  unfold dftChar
  simp

/-- **The DFT coefficient of the phase-sum is the `ψ_k`-phase-spectrum.**
`𝓕 (phaseSum u r) k = phaseSpectrum (dftChar k) u r`. The Mathlib `ZMod` DFT at frequency `k`,
applied to the depth-`r` phase-sum, is exactly the `ψ_k`-Fourier coefficient `ξ̂_r(k)`. -/
theorem dft_phaseSum_eq_phaseSpectrum (u : ZMod m → ℂ) (r : ℕ) (k : ZMod m) :
    (𝓕 (phaseSum u r)) k = phaseSpectrum (dftChar k) u r := by
  rw [dft_apply]
  unfold phaseSpectrum dftChar
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [smul_eq_mul, mul_comm]

/-- **Squared modulus of the DFT coefficient is `|K̂(k)|^{2r}`.**
`‖𝓕 (phaseSum u r) k‖² = ‖kernelSpectrum (dftChar k) u‖^{2r}`. Combines the DFT↔spectrum identity
with the proven squared-modulus depth law `‖ξ̂_r‖² = ‖K̂‖^{2r}`. -/
theorem normSq_dft_phaseSum_eq (u : ZMod m → ℂ) (r : ℕ) (k : ZMod m) :
    ‖(𝓕 (phaseSum u r)) k‖ ^ 2 = ‖kernelSpectrum (dftChar k) u‖ ^ (2 * r) := by
  rw [dft_phaseSum_eq_phaseSpectrum u r k,
    normSq_phaseSpectrum_eq (dftChar k) u (dftChar_add k) (dftChar_zero k) r]

/-- **The Parseval bridge (the door-(iv) Lane-2 capstone).**
`(m : ℝ)·(resonanceMoment u r) = ∑_k ‖kernelSpectrum (dftChar k) u‖^{2r}`, i.e.
`T r = (1/m) ∑_k |K̂(k)|^{2r}`. The named `√p`-free free variable is the `2r`-th power-mean of the
one-step Gauss-period kernel spectrum over the character group. Assembled from Plancherel on
`ZMod m` (`dft_parseval`) and the proven spectral iterate `ξ̂_r = K̂^r`. -/
theorem resonanceMoment_eq_spectral_powerMean (u : ZMod m → ℂ) (r : ℕ) :
    (m : ℝ) * resonanceMoment u r
      = ∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ (2 * r) := by
  classical
  -- Plancherel: ∑_k ‖𝓕(P_r) k‖² = m · ∑_c ‖P_r c‖² = m · T r
  have hpars := dft_parseval (Φ := phaseSum u r)
  -- rewrite each LHS DFT-coefficient squared modulus into |K̂(k)|^{2r}
  rw [resonanceMoment]
  rw [← hpars]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact normSq_dft_phaseSum_eq u r k

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.dftChar_add
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.dftChar_zero
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.dft_phaseSum_eq_phaseSpectrum
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.normSq_dft_phaseSum_eq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_eq_spectral_powerMean
