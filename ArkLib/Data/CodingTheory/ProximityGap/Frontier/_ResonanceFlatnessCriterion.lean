/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralVariance

/-!
# Floor saturation ⟺ flat (Ramanujan) spectrum (#407 / #444)

The exact equality condition in the spectral-variance identity
`∑_k (‖K̂(k)‖² − (m−1))² = m·(T 2 − (m−1)²)` (`sum_sq_centered_kernelSpectrum_eq`): the resonance
moment hits its `r=2` floor `(m−1)²` exactly when the squared kernel spectrum is FLAT (constant
`= m−1` at every frequency — the perfectly equidistributed / "Ramanujan" spectrum):

> **`resonanceMoment u 2 = (m−1)²  ↔  ∀ k, ‖kernelSpectrum (dftChar k) u‖² = m−1`.**

Since the centred second moment is a sum of squares, it vanishes (⟺ `T 2 = (m−1)²`) iff every term
vanishes (⟺ every `|K̂(k)|² = m−1`). This is the certain characterization of when the trivial floor
is saturated: a flat spectrum gives NO cancellation budget beyond the mean, hence `T 2` sits exactly
at the floor.

## Why this matters for the prize direction

The prize needs the OPPOSITE of saturation at the worst frequency: a flat spectrum has every
`|K̂(k)| = √(m−1)` (no spike, no dip), so `max_b |K̂(b)| = √(m−1) ≪ m−1` — i.e. a flat spectrum is
exactly the `√`-cancellation regime the prize targets. This criterion thus pins the prize's good case
(flat spectrum) as an exact, checkable spectral condition. It does NOT prove the spectrum IS flat for
the thin Gauss-period kernel — that flatness (near-Ramanujan up to `√log`) is the OPEN BGK content.

## Honest scope

CERTAIN exact characterization (vanishing of a sum of squares), not a bound. It does NOT prove
flatness holds for any prize-regime kernel — flatness is the open Gauss-period/BGK content. CORE
`M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion / moment-as-prize /
anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Floor saturation ⟺ flat spectrum.** `T 2 = (m−1)²` iff every squared kernel-spectrum value
equals the mean `m−1` (the perfectly equidistributed / Ramanujan spectrum). The centred second
moment is a sum of squares, so it vanishes iff each term does. -/
theorem resonanceMoment_two_eq_sq_iff_flat (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    resonanceMoment u 2 = ((m : ℝ) - 1) ^ 2 ↔
      ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 = (m : ℝ) - 1 := by
  classical
  have hvar := sum_sq_centered_kernelSpectrum_eq u hu
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  -- T 2 = (m-1)²  ↔  m·(T 2 - (m-1)²) = 0  ↔  ∑_k (w_k-(m-1))² = 0
  rw [show (resonanceMoment u 2 = ((m : ℝ) - 1) ^ 2)
        ↔ (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2 = 0) by
      constructor <;> intro h <;> linarith]
  rw [show (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2 = 0)
        ↔ ((m : ℝ) * (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2) = 0) by
      rw [mul_eq_zero]
      constructor
      · intro h; exact Or.inr h
      · rintro (h | h)
        · exact absurd h (ne_of_gt hmpos)
        · exact h]
  rw [← hvar]
  -- ∑_k (w_k-(m-1))² = 0  ↔  ∀k, (w_k-(m-1))² = 0  ↔  ∀k, w_k = m-1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)]
  constructor
  · intro h k
    have hk := h k (Finset.mem_univ k)
    have : ‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk
      exact this
    linarith
  · intro h k _
    rw [h k]
    simp

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_two_eq_sq_iff_flat
