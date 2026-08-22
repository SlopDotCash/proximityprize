/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralMean

/-!
# The r=2 cancellation budget IS the spectral variance (#407 / #444)

Two certain consequences of the Parseval bridge `T r = (1/m) ∑_k |K̂(k)|^{2r}`
(`resonanceMoment_eq_spectral_powerMean`) and the spectral mean `∑_k |K̂(k)|² = m·(m−1)`
(`sum_normSq_kernelSpectrum_eq`), specialised to the second moment. Writing
`w_k = ‖kernelSpectrum (dftChar k) u‖² ≥ 0` (mean `m−1`):

> **`∑_k (w_k − (m−1))² = m·(resonanceMoment u 2 − (m−1)²)`** , i.e. the centred second moment of
> the squared kernel-spectrum profile equals `m` times the gap `T 2 − (m−1)²`.

Equivalently the **spectral variance** `Var = (1/m) ∑_k (w_k − (m−1))²` satisfies
`Var = T 2 − (m−1)²`, and since the LHS is a sum of squares,

> **`(m − 1)² ≤ resonanceMoment u 2`** with equality iff the spectrum is FLAT (`w_k ≡ m−1`).

This identifies the `r=2` cancellation budget `T 2 − (m−1)²` EXACTLY as the spread (variance) of the
one-step Gauss-period kernel spectrum `{|K̂(k)|²}` about its mean `m−1`. The bracketing floor
`(m−1)²` (a special case of the proven tower floor) is now SHARPENED to an exact remainder = the
spectral variance, which is the open content: a flat spectrum saturates the floor, a spread spectrum
(the BGK regime) lifts it.

## Honest scope

CERTAIN exact identity (bridge at `r=2` + spectral mean + a square expansion), not a bound. The
spectral variance `(1/m)∑_k(w_k−(m−1))²` is NAMED not bounded — it is the open Gauss-period content
(a flat spectrum is consistent with the identity, as is a wildly spread one with a large worst-case
spike). It does NOT bound `max_b |K̂(b)|`. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE /
cancellation / completion / moment-as-prize / anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **The centred second moment of the kernel spectrum equals `m·(T 2 − (m−1)²)`.**
`∑_k (‖K̂(k)‖² − (m−1))² = m·(resonanceMoment u 2 − (m−1)²)` for unit-modulus phases. Expand the
square, use `∑_k ‖K̂(k)‖⁴ = m·T 2` (bridge at `r=2`) and `∑_k ‖K̂(k)‖² = m·(m−1)` (spectral mean). -/
theorem sum_sq_centered_kernelSpectrum_eq (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    (∑ k : ZMod m, (‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2)
      = (m : ℝ) * (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2) := by
  classical
  set w : ZMod m → ℝ := fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2 with hw
  -- ∑_k w_k^2 = m·T 2  (bridge at r=2: ∑_k ‖K̂‖^{2·2} = m·T 2 and ‖K̂‖^4 = (‖K̂‖²)²)
  have hsq : (∑ k : ZMod m, (w k) ^ 2) = (m : ℝ) * resonanceMoment u 2 := by
    rw [hw]
    have h := resonanceMoment_eq_spectral_powerMean u 2
    rw [h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← pow_mul]
  -- ∑_k w_k = m·(m-1)
  have hmean : (∑ k : ZMod m, w k) = (m : ℝ) * ((m : ℝ) - 1) := by
    rw [hw]; exact sum_normSq_kernelSpectrum_eq u hu
  -- expand each square: (w_k - c)² = w_k² - 2c·w_k + c²,  c = m-1
  have hpoint : ∀ k : ZMod m, (w k - ((m : ℝ) - 1)) ^ 2
      = (w k) ^ 2 - 2 * ((m : ℝ) - 1) * w k + ((m : ℝ) - 1) ^ 2 := by
    intro k; ring
  rw [Finset.sum_congr rfl (fun k _ => hpoint k)]
  -- distribute the sum over the three terms
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- ∑ 2c·w_k = 2c·∑ w_k;  ∑ c² = card·c²
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hsq, hmean]
  ring

/-- **The spectral floor at `r=2`: `(m-1)² ≤ T 2`** (unit-modulus phases), with the EXACT remainder
`T 2 - (m-1)² = (1/m)∑_k(‖K̂(k)‖²-(m-1))²` = the spectral variance. Equality iff the spectrum is flat. -/
theorem resonanceMoment_two_ge_sq (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    ((m : ℝ) - 1) ^ 2 ≤ resonanceMoment u 2 := by
  have hvar := sum_sq_centered_kernelSpectrum_eq u hu
  have hnn : (0 : ℝ) ≤ ∑ k : ZMod m, (‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => by positivity)
  rw [hvar] at hnn
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  -- 0 ≤ m·(T2 - (m-1)²) ⇒ 0 ≤ T2 - (m-1)²
  have hge : (0 : ℝ) ≤ resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2 :=
    (mul_nonneg_iff_of_pos_left hmpos).mp hnn
  linarith

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.sum_sq_centered_kernelSpectrum_eq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_two_ge_sq
