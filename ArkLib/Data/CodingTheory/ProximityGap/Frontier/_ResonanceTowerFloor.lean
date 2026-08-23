/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceChebyshevLower
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentBaseCaseZero

/-!
# The iterated tower floor `T r ≥ (m−1)^r` of the resonance moment (#407 / #444)

Iterating the matching lower bound `(m−1)·T r ≤ T (r+1)`
(`_ResonanceChebyshevLower.resonanceMoment_succ_ge`) from the depth-`0` base case `T 0 = 1`
(`_ResonanceMomentBaseCaseZero.resonanceMoment_zero`) gives the exact geometric FLOOR of the
resonance tower:

> **`(m − 1)^r ≤ resonanceMoment u r`**  (unit-modulus phases).

Together with the proven iterated CEILING `T r ≤ m·(m−1)^{2(r−1)}` (general ceiling) this brackets
the whole `r`-tower of the named free variable between a geometric floor `(m−1)^r` and a geometric
ceiling `~ (m−1)^{2r}`. The prize regime `T r = Θ(m^r)` (the `√`-cancelled BGK target, `m = (p−1)/n`)
lies STRICTLY between: `(m−1)^r ≈ m^r` (the floor, order-matching the prize) and `(m−1)^{2r}` (the
trivial ceiling). The open content is the gap between the floor and the ceiling — the spread of the
spectral profile `{|K̂(k)|²}` beyond its mean.

## Why this is the right capstone (the tower floor, certain)

The floor `(m−1)^r` is the iterated form of the Chebyshev/power-mean lower bound: since
`T r = (1/m) ∑_k |K̂(k)|^{2r}` is the `2r`-th power-mean of `{|K̂(k)|²}` whose ARITHMETIC mean is
`m−1`, the power-mean inequality forces `T r ≥ (mean)^r = (m−1)^r`. This is a CERTAIN lower bound on
the free variable, NOT a CORE claim: it bounds `T` BELOW (toward the trivial regime), the SAFE
direction; the open prize is an UPPER bound on `max_b |K̂(b)|`, which a large floor does not address.

## Honest scope

CERTAIN inequality (induction on the proven Chebyshev lower bound from the proven base case), not a
CORE bound. It does NOT bound `max_b |K̂(b)|` ABOVE — that worst-frequency value is the open
Gauss-period/BGK content. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation /
completion / moment-as-prize / anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **The iterated tower floor: `(m − 1)^r ≤ T r`** for unit-modulus phases. Induction on `r`:
the base `T 0 = 1 = (m−1)^0`, and the step `(m−1)^{r+1} = (m−1)·(m−1)^r ≤ (m−1)·T r ≤ T (r+1)` using
the Chebyshev lower bound `resonanceMoment_succ_ge` and `0 ≤ m−1`. -/
theorem resonanceMoment_ge_pow (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    ((m : ℝ) - 1) ^ r ≤ resonanceMoment u r := by
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := NeZero.one_le
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  induction r with
  | zero =>
      rw [pow_zero, resonanceMoment_zero]
  | succ r ih =>
      calc ((m : ℝ) - 1) ^ (r + 1)
          = ((m : ℝ) - 1) * ((m : ℝ) - 1) ^ r := by rw [pow_succ, mul_comm]
        _ ≤ ((m : ℝ) - 1) * resonanceMoment u r := by
            exact mul_le_mul_of_nonneg_left ih hm1
        _ ≤ resonanceMoment u (r + 1) := resonanceMoment_succ_ge u hu r

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ge_pow
