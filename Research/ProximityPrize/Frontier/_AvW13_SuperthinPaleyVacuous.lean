/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# The super-thin floor pivot is refuted: no-wraparound ⟹ vacuous Paley bound (#444)

A well-motivated analytic floor pivot (mirroring the Dirichlet *ceiling* pivot
`_TZDirichletUnconditional`) proposed: take a Dirichlet prime `p ≡ 1 (mod n)` so large that `μ_n` is
super-thin and there is NO char-`p` wraparound up to the moment saddle `r* ≈ ln p`; then the proven
char-0 Wick bound transfers, giving the per-frequency Paley bound `M ≤ √(n log p)` unconditionally,
and (the hope) the MCA floor `δ* ≥ window-edge`.

**This file proves why that pivot fails — a clean regime incompatibility.** The no-wraparound
condition at depth `r` is `p > (2r)^{n/2}` (in-tree `_AvND.no_wraparound_at_depth`). Even at the
shallowest useful depth `r ≥ 2` this forces `p > 2^n`, hence `log₂ p > n`, hence the *best possible*
transferred bound `√(n · log₂ p) ≥ √(n·n) = n` — **vacuous**, no better than the trivial
`|η_b| ≤ |G| = n`. So the regime where the char-0 Wick bound transfers (no wraparound) is exactly the
regime where the bound it yields is useless. The non-vacuous regime (`log p < n`, e.g. the prize
`β = 4`) is precisely where wraparound is present and the bound is open.

The deeper reason the *ceiling* pivot succeeds where the *floor* pivot fails: the ceiling needs only
the **existence** of a good prime (a large prime automatically avoids the finite bad-collision set),
which is size-monotone and Dirichlet supplies; the floor needs a non-vacuous **cancellation** (the
incidence `√q`-bound / BCHKS Conj 1.12, a bad-scalar *count*), which no soft existence/no-wraparound
argument supplies — the energy moment that no-wraparound controls has the offset additive character
divided out, so it bounds only the per-frequency period sup, not the offset-twisted incidence.

## Results (axiom-clean)
* `noWrap_threshold_ge_twoPow` — `r ≥ 2 ⟹ (2r)^{nHalf} ≥ 2^{2·nHalf}`: no-wraparound at any depth
  `≥ 2` forces the field past `2^n` (`n = 2·nHalf`).
* `paley_bound_vacuous_of_large_field` — `2^n ≤ p ⟹ n ≤ √(n · log₂ p)`: past `2^n` the Paley bound
  is `≥ n`, i.e. vacuous against the trivial bound.
* `superthin_paley_vacuous` — the composite: no-wraparound at depth `r ≥ 2` with `n = 2·nHalf` and
  field `p > (2r)^{nHalf}` gives `(n : ℝ) ≤ √(n · log₂ p)` (the transferred bound is vacuous).

NOT prize closure — this is honest negative knowledge that formally closes the super-thin floor
pivot and pins the ceiling/floor asymmetry.
-/

namespace ArkLib.ProximityGap.Frontier.AvW13

open Real

/-- **No-wraparound forces a huge field.** For `r ≥ 2`, the no-wraparound threshold `(2r)^{nHalf}`
is at least `2^{2·nHalf} = 2^n` (with `n = 2·nHalf`), since `2r ≥ 4 = 2²`. So any prime exceeding
the threshold exceeds `2^n`. -/
theorem noWrap_threshold_ge_twoPow (r nHalf : ℕ) (hr : 2 ≤ r) :
    (2 : ℕ) ^ (2 * nHalf) ≤ (2 * r) ^ nHalf := by
  calc (2 : ℕ) ^ (2 * nHalf) = (2 ^ 2) ^ nHalf := by rw [pow_mul]
    _ = (4 : ℕ) ^ nHalf := by norm_num
    _ ≤ (2 * r) ^ nHalf := Nat.pow_le_pow_left (by omega) nHalf

/-- **Past `2^n` the Paley bound is vacuous.** If `2^n ≤ p` (so `log₂ p ≥ n`), then the transferred
Paley bound `√(n · log₂ p)` is at least `n` — no better than the trivial sup bound `|η_b| ≤ n`. -/
theorem paley_bound_vacuous_of_large_field (n p : ℕ) (hp : (2 : ℕ) ^ n ≤ p) :
    (n : ℝ) ≤ Real.sqrt ((n : ℝ) * Real.logb 2 (p : ℝ)) := by
  have h2npos : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) n
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := lt_of_lt_of_le h2npos hp
    exact_mod_cast this
  -- (2:ℝ)^n ≤ p (npow, nat cast), then log p ≥ n·log 2, then log₂ p = log p / log 2 ≥ n
  have hlen : (2 : ℝ) ^ n ≤ (p : ℝ) := by exact_mod_cast hp
  have hlogp : (n : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
    have h := Real.log_le_log (by positivity) hlen
    rwa [Real.log_pow] at h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : (n : ℝ) ≤ Real.logb 2 (p : ℝ) := by
    rw [Real.logb, le_div_iff₀ hlog2]; linarith [hlogp]
  -- n·log₂ p ≥ n·n = n², so √(n·log₂p) ≥ √(n²) = n
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have key : (n : ℝ) ^ 2 ≤ (n : ℝ) * Real.logb 2 (p : ℝ) := by nlinarith [hlogb, hn0]
  calc (n : ℝ) = Real.sqrt ((n : ℝ) ^ 2) := (Real.sqrt_sq hn0).symm
    _ ≤ Real.sqrt ((n : ℝ) * Real.logb 2 (p : ℝ)) := Real.sqrt_le_sqrt key

/-- **The super-thin floor pivot is vacuous (composite).** With `n = 2·nHalf`, if the field `p`
exceeds the no-wraparound threshold `(2r)^{nHalf}` at depth `r ≥ 2` (the condition under which the
char-0 Wick bound transfers), then the transferred Paley bound `√(n · log₂ p)` is `≥ n` — vacuous.
So no-wraparound and a non-vacuous per-frequency bound are mutually exclusive regimes. -/
theorem superthin_paley_vacuous (r nHalf p : ℕ) (hr : 2 ≤ r)
    (hp : (2 * r) ^ nHalf < p) :
    ((2 * nHalf : ℕ) : ℝ) ≤ Real.sqrt (((2 * nHalf : ℕ) : ℝ) * Real.logb 2 (p : ℝ)) := by
  have hfield : (2 : ℕ) ^ (2 * nHalf) ≤ p :=
    le_of_lt (lt_of_le_of_lt (noWrap_threshold_ge_twoPow r nHalf hr) hp)
  exact paley_bound_vacuous_of_large_field (2 * nHalf) p hfield

end ArkLib.ProximityGap.Frontier.AvW13

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW13.noWrap_threshold_ge_twoPow
#print axioms ArkLib.ProximityGap.Frontier.AvW13.paley_bound_vacuous_of_large_field
#print axioms ArkLib.ProximityGap.Frontier.AvW13.superthin_paley_vacuous
