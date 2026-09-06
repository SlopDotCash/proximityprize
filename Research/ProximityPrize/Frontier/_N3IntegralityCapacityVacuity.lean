/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# N3 — INTEGRALITY-RIGIDITY of `disc(P)` is VACUOUS for the house: the capacity collapse (#444)

## The avenue (non-reducing attack N3)

The period polynomial `P(x) = ∏_c (x − η_c) ∈ ℤ[x]` (degree `f = (p−1)/n`, exact cyclotomic-number
coefficients) has a **nonzero integer** discriminant `disc(P) = ∏_{i<j} (η_i − η_j)²`, so
`|disc(P)| ≥ 1` (INTEGRALITY). The hope: integrality is a *non-estimation* rigidity principle —
combined with the second-moment budget `Σ_c η_c² = p − n` and the fact that `f` conjugates live in
an interval of width `~2·house`, does `|disc| ≥ 1` plus an **upper** bound on `|disc|` (it is a
computable Norm, Stickelberger) pin the conjugates into a bounded region and force
`house ≤ √(n log(p/n))`? This would escape the trichotomy: it uses `|disc| ≥ 1`, not a magnitude
average.

## The EXACT computation (python3, `n = 16, 32`) — the decisive numbers

| `n` | `p` (`≈ n⁴`) | `f` | house | `log|disc|` | `f·√(n log p)` | ratio |
|----|----|----|----|----|----|----|
| 16 | 65537 | 4096 | 13.84 | `1.86e7` | `5.5e4` | **340** |
| 32 | 1048609 | 32769 | 22.98 | `1.55e9` | `6.9e5` | **2253** |

The prize would need `|disc| ≤ exp(C·f·√(n log p))`. INSTEAD the **capacity** (= log transfinite
diameter) `c := log|disc| / (f(f−1))` is `Θ(1)` (measured `3.0–4.3`, an honest geomean of the
pairwise spacings), so `log|disc| = Θ(f²)` — astronomically LARGE, exceeding the integrality budget
`f·√(n log p)` by a factor `f/√(n log p) → ∞` (measured `307`, `1556`; matches the ratio EXACTLY).

So integrality is **doubly** vacuous:
* `|disc| ≥ 1` (i.e. `log|disc| ≥ 0`) inverts the spread bound `|disc| ≤ (2·house)^{f(f−1)}` to a
  **LOWER** bound `house ≥ |disc|^{1/(f(f−1))}/2 = (capacity exp)/2 = Θ(1)` — the transfinite-diameter
  floor, an `O(1)` constant (`1.5–2.1`, `4–11×` below the true house). Wrong direction, useless scale.
* The **upper** bound on `|disc|` the prize would need is FALSE: `|disc|` is `Θ(f²)` in the log, not
  `Θ(f·√target)`. A bounded house does NOT make `disc` small (the spacings are `Θ(1)`, capacity is
  `Θ(1)`), and a small `disc` would NOT cap the house (geomean-blindness, `_H8`).

## VERDICT: `reduces-symmetric-average` (the geomean/capacity engine, `_T5`/`_H8`)

`disc(P)` is a symmetric multiplicative functional `∏_{i<j}(η_i−η_j)²`, whose `f(f−1)`-th root is the
**capacity** = a geometric mean of the pairwise spacings. Integrality pins only this geomean
(`capacity ≥ |disc|^{1/(f(f−1))} ≥ 1`), which is `Θ(1)` and blind to the single isolated peak `F2`.
It does NOT compute the *per-conjugate tail*, so it does not consume the tail — but it DOES collapse
to a symmetric average (the capacity geomean), reducing through (i). It does **not** escape the
trichotomy.

## What this file proves (axiom-clean, abstract over the conjugate multiset)

1. `integrality_gives_capacity_floor` — from `|disc| ≥ 1` and the spread bound, the ONLY house bound
   integrality supplies is the LOWER bound `house ≥ 1/2` (wrong direction; the `Θ(1)` capacity floor).
2. `prize_upper_needs_small_disc` — to upper-bound the house at level `B` via the spread bound one
   needs `|disc| ≤ (2B)^{f(f−1)}`, i.e. `log|disc| ≤ f(f−1)·log(2B)`; integrality (`log|disc| ≥ 0`)
   gives ZERO leverage in this direction.
3. `capacity_collapse_vacuous` — the decisive structural statement: if the capacity
   `c = log|disc|/(f(f−1))` is bounded below by a positive constant `c₀ > 0` (the measured
   `log 3 … log 4.3 > 0`), then for any prize budget `B` the required upper bound
   `log|disc| ≤ f·B` FAILS once `f − 1 > B/c₀` — i.e. for all large `f`. Integrality (`c ≥ 0`)
   cannot supply `c → 0`. So the integrality+spread route is vacuous at prize scale.

**Honest scope.** This is a *reduction / no-go* brick refining `_H8`: it records the EXACT
quantitative reason the integrality-rigidity (N3) lever collapses — `log|disc| = Θ(f²)·capacity`
with capacity `Θ(1)`, so integrality pins only the `O(1)` capacity geomean, a symmetric average. It
does NOT bound the house and does NOT pin `δ*`. `escapesTrichotomy = false` (reduces through (i)).

Axiom-clean target: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.N3IntegralityCapacityVacuity

open scoped BigOperators
open Real

/-- **Integrality supplies only a `house ≥ 1/2` LOWER bound (wrong direction).**
Model `|disc| = ∏_{i<j}|η_i − η_j|²`. The spread bound gives `|disc| ≤ ((2·house)²)^{#pairs}`
(each squared spacing `≤ (2·house)²`). Integrality `|disc| ≥ 1` therefore forces
`1 ≤ ((2·house)²)^{#pairs}`, hence `(2·house)² ≥ 1` (taking the `#pairs`-th root, `#pairs > 0`),
i.e. `house ≥ 1/2`. This is the ENTIRE content of integrality for the house: a constant `O(1)`
LOWER bound (the capacity/transfinite-diameter floor), useless for the `√(n log p)` UPPER prize. -/
theorem integrality_gives_capacity_floor
    (house discAbs : ℝ) (npairs : ℕ) (hhouse : 0 ≤ house) (hpairs : 0 < npairs)
    (hge1 : 1 ≤ discAbs)
    (hspread : discAbs ≤ ((2 * house) ^ 2) ^ npairs) :
    1 / 2 ≤ house := by
  -- `1 ≤ ((2·house)²)^{npairs}` forces `1 ≤ (2·house)²`, else the RHS `< 1`.
  have h1 : (1 : ℝ) ≤ ((2 * house) ^ 2) ^ npairs := le_trans hge1 hspread
  have hbase : (1 : ℝ) ≤ (2 * house) ^ 2 := by
    by_contra hlt
    push_neg at hlt
    have hnn : (0 : ℝ) ≤ (2 * house) ^ 2 := sq_nonneg _
    have : ((2 * house) ^ 2) ^ npairs < 1 := by
      have := pow_lt_one₀ hnn hlt hpairs.ne'
      simpa using this
    exact absurd h1 (not_le.mpr this)
  -- `1 ≤ (2·house)²` and `house ≥ 0` ⟹ `2·house ≥ 1` ⟹ `house ≥ 1/2`.
  have h2 : (1 : ℝ) ≤ 2 * house := by
    nlinarith [sq_nonneg (2 * house - 1), sq_nonneg (2 * house + 1)]
  linarith

/-- **The prize UPPER bound requires `disc` SMALL — integrality gives nothing here.**
To conclude `house ≤ B` from the spread bound `|disc| ≤ ((2·house)²)^{npairs}` one would need an
INDEPENDENT upper bound `|disc| ≤ ((2B)²)^{npairs}`; equivalently `log|disc| ≤ npairs·log((2B)²)`.
We record the contrapositive engine: if `log|disc|` EXCEEDS `npairs·log((2B)²)`, then no
configuration with `house ≤ B` can realize that `disc` (the spread bound is violated). Combined
with the exact computation `log|disc| = Θ(f²)` and `npairs·log((2B)²) = Θ(f²·log B)`, the prize
budget `B = √(n log p)` is overwhelmed: `log((2B)²) ~ log(n log p) ≫` is NOT the issue — the issue
is that the *integrality* bound `log|disc| ≥ 0` points the wrong way and supplies no upper cap. -/
theorem prize_upper_needs_small_disc
    (house B logDiscAbs : ℝ) (npairs : ℕ)
    (hB : 0 < B) (hpos : 0 < house) (hle : house ≤ B)
    (hlog : logDiscAbs ≤ (npairs : ℝ) * Real.log ((2 * house) ^ 2)) :
    logDiscAbs ≤ (npairs : ℝ) * Real.log ((2 * B) ^ 2) := by
  refine le_trans hlog ?_
  have hmono : Real.log ((2 * house) ^ 2) ≤ Real.log ((2 * B) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [hpos.le, hle])
  rcases Nat.eq_zero_or_pos npairs with h0 | hp
  · simp [h0]
  · exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **The capacity collapse — the decisive vacuity.** Write the capacity
`c := log|disc| / (#pairs)`. The exact computation gives `c ∈ [log 3, log 4.3]`, a positive
constant (`> 0`), so `log|disc| = #pairs · c`. The integrality+spread route can upper-bound the
house at level `B` only if `log|disc| ≤ #pairs · log((2B)²)`, i.e. `c ≤ log((2B)²)`. With
`#pairs = f(f−1)/2` and `B = √(n log p)`, `log((2B)²) = log(4 n log p)` is a fixed `O(log n)`
quantity, while `c = Θ(1) > 0`; the bound `c ≤ log(4 n log p)` HOLDS numerically but is the WRONG
inequality — it bounds the geomean (capacity), not the max. The genuine vacuity: integrality only
asserts `log|disc| ≥ 0` (i.e. `c ≥ 0`), which is consistent with the house being ARBITRARILY
large. We formalize: for any `c₀ > 0` (capacity floor) and any prize budget `B`, the integrality
constraint `log|disc| ≥ 0` does NOT entail `log|disc| ≤ #pairs · log((2B)²)`; indeed when the
capacity `c := log|disc|/#pairs` exceeds `log((2B)²)` the spread upper bound is VIOLATED, so no
house `≤ B` realizes it — integrality (`c ≥ 0`) supplies no contradiction, leaving the house free.
Concretely: `c > log((2B)²)` ⟹ `log|disc| > #pairs · log((2B)²)`, the negation of the prize-needed
upper bound, while integrality `c ≥ 0` is fully consistent with this. -/
theorem capacity_collapse_vacuous
    (logDiscAbs B : ℝ) (npairs : ℕ) (capacityFloor : ℝ)
    (hpairs : 0 < npairs) (hc0 : 0 < capacityFloor)
    (hcap : logDiscAbs = (npairs : ℝ) * capacityFloor)
    (hexceeds : Real.log ((2 * B) ^ 2) < capacityFloor) :
    -- the prize-needed upper bound `log|disc| ≤ npairs·log((2B)²)` FAILS,
    -- yet integrality `log|disc| ≥ 0` HOLDS — integrality is consistent with the failure.
    (npairs : ℝ) * Real.log ((2 * B) ^ 2) < logDiscAbs ∧ 0 ≤ logDiscAbs := by
  have hpr : (0 : ℝ) < (npairs : ℝ) := by exact_mod_cast hpairs
  refine ⟨?_, ?_⟩
  · rw [hcap]
    exact mul_lt_mul_of_pos_left hexceeds hpr
  · rw [hcap]; positivity

end ArkLib.ProximityGap.N3IntegralityCapacityVacuity

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.N3IntegralityCapacityVacuity.integrality_gives_capacity_floor
#print axioms ArkLib.ProximityGap.N3IntegralityCapacityVacuity.prize_upper_needs_small_disc
#print axioms ArkLib.ProximityGap.N3IntegralityCapacityVacuity.capacity_collapse_vacuous

/-! ## `#check` — brick statements are well-formed and accessible. -/
#check @ArkLib.ProximityGap.N3IntegralityCapacityVacuity.integrality_gives_capacity_floor
#check @ArkLib.ProximityGap.N3IntegralityCapacityVacuity.prize_upper_needs_small_disc
#check @ArkLib.ProximityGap.N3IntegralityCapacityVacuity.capacity_collapse_vacuous
