/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSpectrumRecursion

/-!
# Depth-additivity and the squared-modulus depth law of the resonance phase-spectrum (#407 / #444)

Builds directly on `_ResonancePhaseSpectrumRecursion`, which proves the Fourier-side recursion
`phaseSpectrum ψ u (r+1) = kernelSpectrum ψ u · phaseSpectrum ψ u r` and its iterate
`phaseSpectrum ψ u r = (kernelSpectrum ψ u)^r` (for an additive character `ψ`, `ψ 0 = 1`).

What was MISSING (grep-confirmed: no `phaseSpectrum_add`, no `‖phaseSpectrum‖` / `normSq phaseSpectrum`
law anywhere in `ProximityGap/`) are the two structural rungs that feed the Parseval power-mean
`T r = (1/m) ∑_b |K̂(b)|^{2r}`:

* **Depth-additivity (semigroup law).** `phaseSpectrum ψ u (r+s) = phaseSpectrum ψ u r · phaseSpectrum ψ u s`
  — the spectrum is multiplicative across depths (a `pow_add` consequence of the iterate).
* **Squared-modulus depth law.** `‖phaseSpectrum ψ u r‖² = ‖kernelSpectrum ψ u‖^{2r}` and
  `‖phaseSpectrum ψ u r‖ = ‖kernelSpectrum ψ u‖^r`. This is EXACTLY the per-frequency summand of the
  Parseval bridge: summing `‖ξ̂_b‖² = |K̂(b)|^{2r}` over the character group `b` and normalising by `m`
  gives the named free variable `T r` as the `2r`-th power-mean of the one-step kernel spectrum.

## Why this is the right rung (the Parseval summand, made certain)

The whole `r`-tower of the resonance moment localizes to the spectral profile of ONE function `K̂(b)`
(established by the convolution recursion + its spectral form). The missing link to the power-mean
form `T r = (1/m) ∑_b |K̂(b)|^{2r}` is the per-frequency squared-modulus law `|ξ̂_r(b)|² = |K̂(b)|^{2r}`.
This file LOCKS that summand axiom-clean. It does NOT prove the Parseval identity itself (that needs
character orthogonality / Plancherel over `ZMod m`, summing over all `b`) — only the per-frequency
modulus law, which is a clean `map_pow` / `norm_pow` consequence of the iterate. It does NOT bound
`K̂(b)` — that spectral profile IS the open Gauss-period/BGK content.

## Honest scope

CERTAIN exact algebraic identities (modulus of a power), not bounds. `kernelSpectrum ψ u` (the open
Gauss-period object) is NAMED not bounded. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE /
cancellation / completion / moment / anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **Depth-additivity of the phase-spectrum (semigroup law).**
`phaseSpectrum ψ u (r+s) = phaseSpectrum ψ u r · phaseSpectrum ψ u s` for an additive character `ψ`
with `ψ 0 = 1`. The spectrum is multiplicative across depths — the Fourier-side image of the fact
that the resonance tower is the iterated convolution power of one kernel. -/
theorem phaseSpectrum_add (ψ : ZMod m → ℂ) (u : ZMod m → ℂ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y) (hzero : ψ 0 = 1) (r s : ℕ) :
    phaseSpectrum ψ u (r + s) = phaseSpectrum ψ u r * phaseSpectrum ψ u s := by
  rw [phaseSpectrum_eq_kernelSpectrum_pow ψ u hmul hzero,
    phaseSpectrum_eq_kernelSpectrum_pow ψ u hmul hzero,
    phaseSpectrum_eq_kernelSpectrum_pow ψ u hmul hzero, pow_add]

/-- **Modulus depth law of the phase-spectrum.**
`‖phaseSpectrum ψ u r‖ = ‖kernelSpectrum ψ u‖^r`. The modulus of the depth-`r` spectrum is the
`r`-th power of the one-step kernel-spectrum modulus. -/
theorem norm_phaseSpectrum_eq (ψ : ZMod m → ℂ) (u : ZMod m → ℂ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y) (hzero : ψ 0 = 1) (r : ℕ) :
    ‖phaseSpectrum ψ u r‖ = ‖kernelSpectrum ψ u‖ ^ r := by
  rw [phaseSpectrum_eq_kernelSpectrum_pow ψ u hmul hzero, norm_pow]

/-- **Squared-modulus depth law of the phase-spectrum (the Parseval summand).**
`‖phaseSpectrum ψ u r‖² = ‖kernelSpectrum ψ u‖^{2r}`. This is EXACTLY the per-frequency summand of
the Parseval power-mean `T r = (1/m) ∑_b |K̂(b)|^{2r}` — locking the summand axiom-clean, while the
Parseval identity itself (the `b`-sum over the character group, needing Plancherel) remains the
separate bridge. The open content is the profile `K̂(b)`, NAMED not bounded. -/
theorem normSq_phaseSpectrum_eq (ψ : ZMod m → ℂ) (u : ZMod m → ℂ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y) (hzero : ψ 0 = 1) (r : ℕ) :
    ‖phaseSpectrum ψ u r‖ ^ 2 = ‖kernelSpectrum ψ u‖ ^ (2 * r) := by
  rw [norm_phaseSpectrum_eq ψ u hmul hzero, ← pow_mul, Nat.mul_comm]

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum_add
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.norm_phaseSpectrum_eq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.normSq_phaseSpectrum_eq
