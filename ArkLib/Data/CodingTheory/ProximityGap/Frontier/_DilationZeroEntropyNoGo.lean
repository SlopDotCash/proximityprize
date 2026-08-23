/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Zero-entropy no-go: the μ_n dilation is a single n-cycle, so no ergodic tool can bound the house (#444)

**The no-go.** A recurring "fresh" idea for the prize sup-norm `house = M(μ_n) = max_{b≠0}|η_b|` is to apply
an **ergodic / mixing / spectral-gap / dynamical** decay estimate to the **dilation dynamics** `x ↦ h·x` on the
2-power subgroup `μ_n` (`h` a generator). This file records the clean structural reason that route is
**permanently dead**, in the style of the in-tree `_TowerDescentNoSaving` / `_DecouplingTowerNoSaving` no-gos.

In additive coordinates `μ_n ≅ ZMod n` (dilation by a generator ≅ the shift `x ↦ x+1`), the dilation map is a
**single `n`-cycle**: its `k`-th iterate is `x ↦ x + k`, which is the identity iff `n ∣ k`, so it has order
**exactly `n`**. A finite-order measure-preserving map has **purely discrete spectrum** (here: the `n` `n`-th
roots of unity) and **zero entropy** — there is no mixing, no spectral gap, and no decay of correlations beyond
the hard period `n`. Every ergodic/dynamical decay theorem (mixing rates, spectral-gap bounds, Erdős–Turán–
Koksma discrepancy via a mixing dynamics, decay-of-correlations chaining) **requires** positive entropy or a
continuous/Lebesgue spectral component, which this system provably lacks. Hence **no ergodic/dynamical tool can
produce the `√log m` cancellation** the house needs — the dynamical-domain attack class is structurally void.

This complements the archimedean no-go map: the wall is the *phase* equidistribution of the `m=(p−1)/n` Gauss
sums (a `0`-dimensional, zero-entropy, rationally-structured object), not a decay/mixing phenomenon.

**What this file proves (axiom-clean).** The load-bearing finite fact: the shift on `ZMod n` has `k`-th iterate
`+k` and order exactly `n` (a single `n`-cycle). The dynamical no-go is the docstring interpretation. Issue #444.
-/

namespace ProximityGap.Frontier.DilationZeroEntropy

open Function

/-- The **dilation** in additive coordinates: the shift `σ(x) = x + 1` on `ZMod n` (`μ_n ≅ ZMod n`, dilation by
a generator ≅ `+1`). -/
def dilation (n : ℕ) : ZMod n → ZMod n := fun x => x + 1

/-- The `k`-th iterate of the dilation is `x ↦ x + k`. -/
theorem dilation_iterate (n : ℕ) (k : ℕ) (x : ZMod n) :
    (dilation n)^[k] x = x + (k : ZMod n) := by
  induction k with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih, dilation]
      push_cast; ring

/-- **Single `n`-cycle / zero entropy.** The dilation's `k`-th iterate is the identity **iff `n ∣ k`** — so the
dilation has order exactly `n` (a single `n`-cycle, purely discrete spectrum). For `n ≥ 1` no nonzero iterate
below `n` is the identity, so there is no mixing/decay mechanism: the ergodic/dynamical attack class is void. -/
theorem dilation_iterate_eq_id_iff (n : ℕ) (k : ℕ) :
    (dilation n)^[k] = id ↔ (n : ℕ) ∣ k := by
  constructor
  · intro h
    have h0 : (dilation n)^[k] 0 = (0 : ZMod n) := by rw [h]; rfl
    rw [dilation_iterate n k 0, zero_add] at h0
    exact (ZMod.natCast_eq_zero_iff k n).mp h0
  · intro h
    funext x
    rw [dilation_iterate n k x, id_eq]
    have : (k : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff k n).mpr h
    rw [this, add_zero]

/-- **No sub-period return.** For `0 < k < n`, the dilation's `k`-th iterate is NOT the identity: the orbit has
full period `n` (zero entropy, discrete spectrum) — the structural reason ergodic/mixing decay cannot apply. -/
theorem dilation_no_subperiod (n : ℕ) (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (dilation n)^[k] ≠ id := by
  intro h
  have : (n : ℕ) ∣ k := (dilation_iterate_eq_id_iff n k).mp h
  exact absurd (Nat.le_of_dvd hk0 this) (Nat.not_le.mpr hkn)

end ProximityGap.Frontier.DilationZeroEntropy

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DilationZeroEntropy.dilation_iterate_eq_id_iff
#print axioms ProximityGap.Frontier.DilationZeroEntropy.dilation_no_subperiod
