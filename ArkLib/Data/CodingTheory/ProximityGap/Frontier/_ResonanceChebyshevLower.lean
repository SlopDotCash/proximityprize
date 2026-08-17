/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralMean
import Mathlib.Algebra.Order.Chebyshev

/-!
# The matching lower bound `(m−1)·T(r) ≤ T(r+1)` via Chebyshev's sum inequality (#407 / #444)

This file lands the matching LOWER bound to the proven aggregate L² recursion upper bound
`T(r+1) ≤ (m−1)²·T r` (`_ResonanceMomentConvolutionRecursion`), pinning the resonance recursion
two-sidedly with a genuine INEQUALITY:

> **`(m − 1)·(resonanceMoment u r) ≤ resonanceMoment u (r+1)`**  (unit-modulus phases).

The mechanism is **Chebyshev's sum inequality** on the spectral weights, via the Parseval bridge.
Writing `w_k = ‖kernelSpectrum (dftChar k) u‖² ≥ 0`, the bridge
`m·T r = ∑_k w_k^r` (`resonanceMoment_eq_spectral_powerMean`) and the spectral mean
`∑_k w_k = m·(m−1)` (`sum_normSq_kernelSpectrum_eq`) give, since `w^r` and `w` monovary
(both monotone non-decreasing in `w_k ≥ 0`),

  `(∑_k w_k^r)·(∑_k w_k) ≤ m·∑_k w_k^{r+1}`     (Chebyshev / `Monovary.sum_mul_sum_le_card_mul_sum`)
  ⟹ `(m·T r)·(m·(m−1)) ≤ m·(m·T(r+1))`
  ⟹ `(m−1)·T r ≤ T(r+1)`.

## Why this completes the two-sided pin (the matching lower bound, as an inequality)

The exact diagonal extraction `_ResonanceConvolutionDiagExtraction` showed `T(r+1) = (m−1)·T r + Off`
with `Off` (the convolution off-diagonal) probe-true `≥ 0` but NOT formalized (it routes through the
spectral profile). This file proves `Off ≥ 0` in its equivalent Chebyshev form — the lower bound is
now a kernel-checked theorem, not a probe. Together with the proven upper bound it brackets the
recursion: `(m−1)·T r ≤ T(r+1) ≤ (m−1)²·T r`, the gap factor `(m−1)` being the open cancellation
budget (the spread of the spectral profile `{|K̂(k)|²}` beyond its mean `m−1`).

## Honest scope

CERTAIN inequality (Chebyshev's sum inequality on the proven Parseval bridge + spectral mean), not a
CORE bound. It bounds `T` BELOW (toward the trivial regime), the SAFE direction — it does NOT bound
`max_b |K̂(b)|` ABOVE (the open prize direction); a large worst-frequency spike is fully consistent
with this lower bound. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation /
completion / moment-as-prize / anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Matching lower bound of the L² recursion: `(m − 1)·T r ≤ T (r+1)`** (unit-modulus phases).
Chebyshev's sum inequality on the spectral weights `w_k = |K̂(k)|²` via the Parseval bridge: with
`∑_k w_k^r = m·T r`, `∑_k w_k = m·(m−1)`, `∑_k w_k^{r+1} = m·T(r+1)`, and `w^r` monovarying with `w`
(both monotone in `w_k ≥ 0`), `(∑w^r)(∑w) ≤ m·∑w^{r+1}` collapses to `(m−1)·T r ≤ T(r+1)`. The
matching lower bound to the proven `T(r+1) ≤ (m−1)²·T r`; the gap factor `m−1` is the open
cancellation budget (spread of `{|K̂(k)|²}` beyond its mean). -/
theorem resonanceMoment_succ_ge (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    ((m : ℝ) - 1) * resonanceMoment u r ≤ resonanceMoment u (r + 1) := by
  classical
  set w : ZMod m → ℝ := fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2 with hw
  -- nonnegativity of weights
  have hwnn : ∀ k, 0 ≤ w k := fun k => by rw [hw]; positivity
  -- bridge facts: ∑_k w_k^r = m·T r,  ∑_k w_k^{r+1} = m·T(r+1)
  have hbridge_r : (∑ k : ZMod m, w k ^ r) = (m : ℝ) * resonanceMoment u r := by
    rw [hw]
    have h := resonanceMoment_eq_spectral_powerMean u r
    -- ∑_k (‖K̂ k‖^2)^r = ∑_k ‖K̂ k‖^{2r}
    rw [h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← pow_mul, Nat.mul_comm]
  have hbridge_succ : (∑ k : ZMod m, w k ^ (r + 1)) = (m : ℝ) * resonanceMoment u (r + 1) := by
    rw [hw]
    have h := resonanceMoment_eq_spectral_powerMean u (r + 1)
    rw [h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← pow_mul, Nat.mul_comm]
  -- spectral mean: ∑_k w_k = m·(m-1)
  have hmean : (∑ k : ZMod m, w k) = (m : ℝ) * ((m : ℝ) - 1) := by
    rw [hw]; exact sum_normSq_kernelSpectrum_eq u hu
  -- Chebyshev: (∑ w^r)·(∑ w) ≤ card · ∑ (w^r · w),  card = m, w^r·w = w^{r+1}
  have hmono : Monovary (fun k => w k ^ r) w := (monovary_self w).pow_left₀ hwnn r
  have hcheb := hmono.sum_mul_sum_le_card_mul_sum
  -- rewrite the scalar-product sum ∑ (w^r · w) = ∑ w^{r+1}
  have hprod : (∑ k : ZMod m, w k ^ r * w k) = ∑ k : ZMod m, w k ^ (r + 1) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← pow_succ]
  rw [hprod] at hcheb
  -- substitute the three sums; card (ZMod m) = m
  have hcard : (Fintype.card (ZMod m) : ℝ) = (m : ℝ) := by rw [ZMod.card]
  rw [hbridge_r, hmean, hbridge_succ, hcard] at hcheb
  -- hcheb : (m·T r)·(m·(m-1)) ≤ m·(m·T(r+1))
  -- divide by m > 0 twice ⟹ (m-1)·T r ≤ T(r+1)
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  -- ((m·T r)·(m·(m-1))) = m^2·((m-1)·T r); (m·(m·T(r+1))) = m^2·T(r+1)
  have hL : ((m : ℝ) * resonanceMoment u r) * ((m : ℝ) * ((m : ℝ) - 1))
      = (m : ℝ) ^ 2 * (((m : ℝ) - 1) * resonanceMoment u r) := by ring
  have hR : (m : ℝ) * ((m : ℝ) * resonanceMoment u (r + 1))
      = (m : ℝ) ^ 2 * resonanceMoment u (r + 1) := by ring
  rw [hL, hR] at hcheb
  have hsqpos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  exact le_of_mul_le_mul_left hcheb hsqpos

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_succ_ge
