/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentGeneralCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentBaseCaseZero

/-!
# The unconditional `∀ r` trivial ceiling of the resonance moment (#407 / #444)

`_ResonanceMomentGeneralCeiling` proves the aggregate `L²` trivial ceiling for unit phases
ONLY for `r ≥ 1`:

> `resonanceMoment_le_general`: `T r ≤ m·(m−1)^{2(r−1)}` for `r ≥ 1`.

With the depth-`0` base case `resonanceMoment u 0 = 1` (`_ResonanceMomentBaseCaseZero`) now pinned,
the `r ≥ 1` hypothesis is REMOVABLE: at `r = 0` the RHS uses `ℕ`-truncated subtraction, so
`(r − 1) = 0`, the RHS collapses to `m·(m−1)^0 = m`, and `T 0 = 1 ≤ m` holds (since `m ≥ 1`).
Hence the trivial ceiling holds **unconditionally for every `r`**:

> **`T r ≤ m·(m−1)^{2(r−1)}` for ALL `r`** (`resonanceMoment_le_unconditional`).

This removes the last `r ≥ 1` side-condition from the trivial-ceiling rung, so the ceiling is a
clean total bound on the resonance moment over the full recursion tower (the `r = 0` start
included). It is a CERTAIN inequality with no number-theoretic content; the order-tightness of this
ceiling (attained at `u ≡ 1`) is the SEPARATE proven fact `_ResonanceConstantVectorCeiling` /
`_ResonancePhaseMassFloor`, and the prize `√`-cancellation gap to `Θ(m^r)` lives precisely where
the unit-modulus PHASE structure forces the genuine Gauss phases below this ceiling.

PROBE: `scripts/probes/probe_r0_ceiling.py` confirms the `r = 0` RHS arithmetic (`= m`, and
`T 0 = 1 ≤ m`) across `m ∈ {2,3,5,7,11}`.

This makes NO CORE / cancellation / completion / moment / anti-concentration / capacity claim. The
prize `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407 / #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **Unconditional aggregate `L²` trivial ceiling: `T r ≤ m·(m−1)^{2(r−1)}` for ALL `r`** (unit
phases). For `r ≥ 1` this is `resonanceMoment_le_general`; for `r = 0` the `ℕ`-truncated `(r−1) = 0`
makes the RHS `= m`, and the depth-`0` base case `T 0 = 1 ≤ m` closes it (since `m ≥ 1`). -/
theorem resonanceMoment_le_unconditional (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (r : ℕ) :
    resonanceMoment u r ≤ (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) := by
  classical
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    rw [resonanceMoment_zero]
    have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
    simpa using hm
  · exact resonanceMoment_le_general u hu r hr1

end ArkLib.ProximityGap.GaussPhaseResonance
