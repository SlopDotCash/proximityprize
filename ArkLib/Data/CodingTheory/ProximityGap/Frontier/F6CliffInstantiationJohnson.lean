/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# The F6 explicit δ* lower bound, at the GUARD's cliff value `M_cross = n/4`, is JOHNSON-side (#444)

## Why this file exists — locating the F6 deliverable under the ASYMPTOTIC-CLAIM GUARD

`_BchksF6_ExplicitDeltaStarLower.lean` delivers, modulo three named residuals, the explicit lower
bound (on the `ρ = 1/4` axis)

  `δ*(n) ≥ 1 − ρ − (M_cross − 1)/n = 3/4 − (M_cross − 1)/n`,

where `M_cross` is the complete-homogeneous crossing fold (the binding depth `m*`). Whether this is a
**beyond-Johnson** (capacity-side, `→ 3/4`) bound or only a **Johnson-side** (`→ 1/2`) bound depends
entirely on the asymptotics of `M_cross`, which F6 leaves as the open residual.

The dossier's **ASYMPTOTIC-CLAIM GUARD** says the binding fold **hugs the DFT-uncertainty cliff**
`s_top ≈ n/2`, so on the `ρ = 1/4` axis `M_cross = m* = s* − k ≈ n/2 − n/4 = n/4` — **linear in `n`**.
This file evaluates the F6 lower bound **at that cliff-consistent value** `M_cross = n/4` and pins
exactly where it lands:

> **At `M_cross = n/4` the F6 bound is `1/2 + 1/n`, which `→ 1/2` (the Johnson side), NOT `3/4`
> (capacity).** By contrast, a *bounded* `M_cross = c = O(1)` gives `3/4 − (c−1)/n → 3/4` (capacity).
> The two readings give **exactly `1/2` vs `3/4`** in the limit on the *same* unproven `M_cross`.

So the F6 deliverable does **not, by itself, prove a beyond-Johnson gap**: that requires
`M_cross = o(n)` (sub-linear), which the 6-point `c*` table does **not** entail (companion brick
`CStarExtrapolationUnderdetermined`). The whole prize lives in this `o(n)`-vs-`Θ(n)` dichotomy for
`M_cross`, = the open BGK wall.

### Honest scope (rules 1, 3, 4, 6)
* **NOT a CORE closure** — BGK `M(n) ≤ C√(n·log(p/n))` stays OPEN. This *locates* the F6 bound under
  the guard; it does not prove which reading is correct (that IS the prize).
* **NOT a proof of the cliff** — we evaluate F6 *conditionally* at `M_cross = n/4`; we do not assert
  `M_cross` equals `n/4` (the DFT-uncertainty bound is necessary-not-sufficient, c.348).
* Pure ℚ/ℝ arithmetic on F6's own gap identity; NON-MOMENT; EXTEND-locates F6's
  `deltaStar_lower_of_mStar_le` / `deltaStar_master_gap_identity`.

Probe: `scripts/probes/probe_f6_cliff_instantiation_johnson.py` (exact `Fraction`: cliff value gives
`1/2 + 1/n`; bounded value gives `3/4 − (c−1)/n`).

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/

namespace ArkLib.ProximityGap.F6CliffInstantiationJohnson

/-- The F6 explicit lower-bound value on the `ρ = 1/4` axis as a function of the crossing fold
`M_cross` (real): `lb(n, M) = 1 − 1/4 − (M − 1)/n`. This is exactly the RHS of F6's
`explicit_deltaStar_lower_bound` with `ρ = 1/4`. -/
noncomputable def f6LowerBound (n M : ℝ) : ℝ := 1 - 1/4 - (M - 1) / n

/-! ### The cliff reading `M_cross = n/4` — the bound is `1/2 + 1/n`, the JOHNSON side -/

/-- **At the cliff-consistent fold `M_cross = n/4`, the F6 bound equals `1/2 + 1/n`.** Exact identity
for `n ≠ 0`: substituting `M = n/4` into `1 − 1/4 − (M−1)/n` gives `3/4 − (n/4 − 1)/n = 1/2 + 1/n`. -/
theorem f6_at_cliff_eq (n : ℝ) (hn : n ≠ 0) :
    f6LowerBound n (n / 4) = 1/2 + 1/n := by
  unfold f6LowerBound
  field_simp
  ring

/-- **The cliff-reading bound is strictly BELOW capacity `3/4` for every `n > 0`.** `1/2 + 1/n < 3/4`
iff `1/n < 1/4` iff `n > 4`; stated for `n > 4` (the prize regime `n = 2^a ≥ 8`). The F6 bound at the
cliff value never reaches capacity. -/
theorem f6_at_cliff_lt_capacity (n : ℝ) (hn : 4 < n) :
    f6LowerBound n (n / 4) < 3/4 := by
  rw [f6_at_cliff_eq n (by linarith)]
  have h1 : (1:ℝ) / n < 1 / 4 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- **The cliff-reading bound is strictly ABOVE the Johnson side `1/2` by exactly `1/n`** (`n > 0`):
`f6(n, n/4) = 1/2 + 1/n > 1/2`. So the cliff reading sits in `(1/2, 3/4)`, riding *down* to `1/2`
(Johnson) as `n → ∞`, NOT up to `3/4` (capacity). -/
theorem f6_at_cliff_gt_johnson (n : ℝ) (hn : 0 < n) :
    1/2 < f6LowerBound n (n / 4) := by
  rw [f6_at_cliff_eq n (ne_of_gt hn)]
  have : (0:ℝ) < 1 / n := by positivity
  linarith

/-! ### The bounded reading `M_cross = c = O(1)` — the bound is `3/4 − (c−1)/n → 3/4`, CAPACITY -/

/-- **At a bounded fold `M_cross = c`, the F6 bound equals `3/4 − (c−1)/n`.** Exact identity
(`n ≠ 0`): `1 − 1/4 − (c−1)/n = 3/4 − (c−1)/n`, whose limit as `n → ∞` is `3/4` (capacity). -/
theorem f6_at_bounded_eq (n c : ℝ) (hn : n ≠ 0) :
    f6LowerBound n c = 3/4 - (c - 1) / n := by
  unfold f6LowerBound
  ring

/-! ### The dichotomy — the SAME unproven `M_cross` gives `1/2` vs `3/4` in the limit -/

/-- **HEADLINE — the cliff and bounded readings differ by exactly `1/4` in the `δ*` limit.** At any
finite `n > 4`, the *gap* between the bounded-reading bound `3/4 − (c−1)/n` and the cliff-reading
bound `1/2 + 1/n` is `1/4 − c/n`, which `→ 1/4` as `n → ∞`. So the SAME F6 deliverable, under the two
asymptotic readings of its open residual `M_cross`, yields `δ*` limits a full Johnson-to-capacity
`1/4` apart. The beyond-Johnson gap is *exactly* the unproven claim that `M_cross = o(n)`. -/
theorem f6_reading_gap (n c : ℝ) (hn : n ≠ 0) :
    f6LowerBound n c - f6LowerBound n (n / 4) = 1/4 - c / n := by
  rw [f6_at_bounded_eq n c hn, f6_at_cliff_eq n hn]
  field_simp
  ring

/-- **The cliff reading is strictly Johnson-side of any bounded reading at large `n`.** For a fixed
bounded fold `c` and `n > 4·c`, the cliff-reading bound is strictly below the bounded-reading bound:
`f6(n, n/4) < f6(n, c)`. So once `n` is large the cliff fold pulls `δ*` strictly toward Johnson
relative to any constant fold — the two readings genuinely separate. -/
theorem f6_cliff_below_bounded (n c : ℝ) (hc : 0 ≤ c) (hn : 4 * c < n) (hn0 : 0 < n) :
    f6LowerBound n (n / 4) < f6LowerBound n c := by
  have hgap : f6LowerBound n c - f6LowerBound n (n / 4) = 1/4 - c / n :=
    f6_reading_gap n c (ne_of_gt hn0)
  have hpos : 0 < 1/4 - c / n := by
    rw [sub_pos, div_lt_iff₀ hn0]
    linarith
  linarith

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}):
#print axioms f6_at_cliff_eq
#print axioms f6_at_cliff_lt_capacity
#print axioms f6_at_cliff_gt_johnson
#print axioms f6_at_bounded_eq
#print axioms f6_reading_gap
#print axioms f6_cliff_below_bounded

end ArkLib.ProximityGap.F6CliffInstantiationJohnson
