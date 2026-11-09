/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Zero-entropy no-go: the μ_n dilation is a single n-cycle, so mixing decay does not apply (#444)

**The (scoped) no-go.** A recurring "fresh" idea for the prize sup-norm
`house = M(μ_n) = max_{b≠0}|η_b|` is to apply a **mixing / decay-of-correlations** estimate to the
**dilation dynamics** `x ↦ h·x` on the 2-power subgroup `μ_n` (`h` a generator). This file records
the structural reason that *this specific* argument cannot work, in the style of the in-tree
`_TowerDescentNoSaving` / `_DecouplingTowerNoSaving` no-gos.

In additive coordinates `μ_n ≅ ZMod n` (dilation by a generator ≅ the shift `x ↦ x+1`), the dilation
map is a **single `n`-cycle**: its `k`-th iterate is `x ↦ x + k`, which is the identity iff `n ∣ k`,
so it has order **exactly `n`**. A finite-order measure-preserving map has purely discrete spectrum
(here: the `n` `n`-th roots of unity) and zero entropy, so it is not mixing and has no decay of
correlations beyond the hard period `n`: a genuine mixing-rate or decay-of-correlations bound for
this particular finite dilation map is unavailable.

**Scope (audit R-033, 2026-10-28).** This does **not** exclude every ergodic or dynamical tool, nor
auxiliary dynamics built on other spaces. Discrete-spectrum dynamics still supports exact
cancellation: for a nonconstant character of the `n`-cycle, the sum over one complete orbit is
zero by the geometric-series identity, despite zero entropy and periodicity. No theorem here
connects general ergodic/discrepancy tool classes to the house or proves their insufficiency; the
broader judgement that dynamical methods are unpromising for the house is an **unproved strategy
judgement**, not a consequence of the lemmas below.

Heuristically, the wall is the *phase* equidistribution of the `m=(p−1)/n` Gauss sums rather than a
decay/mixing phenomenon (an interpretation, not proved here).

**What this file proves (axiom-clean).** The finite fact: the shift on `ZMod n` has `k`-th iterate
`+k` and returns to the identity exactly when `n ∣ k` (a single `n`-cycle). The mixing no-go above
is the docstring interpretation of that fact for this one map. Issue #444.
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
dilation has order exactly `n` (a single `n`-cycle, purely discrete spectrum). For `n ≥ 1` no
nonzero iterate below `n` is the identity, so this map has no mixing/decay mechanism (this does not
by itself exclude other dynamical or exact-cancellation arguments). -/
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
full period `n` (zero entropy, discrete spectrum) — the structural reason mixing decay for this
finite dilation map cannot apply. -/
theorem dilation_no_subperiod (n : ℕ) (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (dilation n)^[k] ≠ id := by
  intro h
  have : (n : ℕ) ∣ k := (dilation_iterate_eq_id_iff n k).mp h
  exact absurd (Nat.le_of_dvd hk0 this) (Nat.not_le.mpr hkn)

end ProximityGap.Frontier.DilationZeroEntropy

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DilationZeroEntropy.dilation_iterate_eq_id_iff
#print axioms ProximityGap.Frontier.DilationZeroEntropy.dilation_no_subperiod
