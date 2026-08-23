/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFSaddleAssembled

/-!
# The saddle floor in prize SHAPE: `log(2q²)/y* ≤ (3/√2)·√(n·log q)` (#444 §6.2)

`CoshMGFSaddleAssembled.period_le_saddle_closedForm` lands the closed-form saddle bound
`‖η_{b₀}‖ ≤ log(2·q²)/y*` (conditional on the single open MGF inequality), at the saddle
`y*² = 2·log q / n`.  Its docstring asserts (**as prose, never as a theorem**) that

> "With `y* = √(2 log q / n)` this is `(log 2 + 2 log q)/√(2 log q / n) = Θ(√(n log q))`, the prize
> floor shape `C·√(n·log(q/n))` up to the absolute constant `C`."

That `Θ(√(n log q))` collapse, with an **explicit absolute constant**, is what this file discharges.

## What is proved here

The pure-ℝ analytic shape lemma (`saddle_closedForm_le_sqrt_shape`): for `n > 0`, `q ≥ 2`, and
`y > 0` with `y² = 2·log q / n`,
```
        log(2·q²) / y  ≤  (3/√2) · √(n · log q).
```
The constant `3/√2 = 2.1213…` is uniform over the **entire** range `q ≥ 2`, `n > 0` (not just the
prize regime); it is **tight at `q = 2`** and decreases to the asymptotic leading constant `√2` as
`q → ∞` (in the prize regime `q = nᵝ`, `β ≥ 4`, `n ≥ 16` the realised ratio is `≈ 1.44`).
Probe: `scripts/probes/probe_saddle_floor_shape.py` (0/88 violations; uniform `C = 3/√2` confirmed,
tight at `q = 2`).

Chaining onto the in-tree saddle consumer gives `period_le_floor_shape`: the explicit
**prize-floor-shape** sup-norm bound
```
        ‖η_{b₀}‖  ≤  (3/√2) · √(n · log q),
```
**conditional on the single open MGF inequality** `MGF(y*) ≤ q·exp(n·y*²/2)` (the char-`p` Wick
bound at depth `r ≈ log q`, the recognised open BGK core of #444).  This file adds NO analytic
input beyond the elementary algebra; it does NOT prove the open inequality.

## The arithmetic (why `3/√2`, and why uniform)

`log(2·q²) = log 2 + 2·log q`.  Writing `L = log q ≥ log 2 > 0` (from `q ≥ 2`), `y = √(2L/n)`,
squaring the target (both sides `≥ 0`) reduces it to `(log 2 + 2L)² · n/(2L) ≤ (9/2)·n·L`, i.e.
(cancel `n/(2L) > 0`) `(log 2 + 2L)² ≤ 9·L²`, i.e. `log 2 + 2L ≤ 3L`, i.e. `log 2 ≤ L = log q`. That
final inequality is exactly `q ≥ 2`.  The whole reduction is monotone, so the constant is forced and
tight at the `q = 2` boundary.

## Honesty

This is a NON-MOMENT, real-analytic SHAPE extraction: it converts the already-proven closed-form
saddle bound into the literal prize floor `C·√(n·log q)` with an explicit `C`.  It is
**conditional on the open core** (it inherits the `hMGF` hypothesis verbatim) and makes NO
beyond-Johnson / capacity claim, so it is asymptotic-guard-compliant (a positive SHAPE of a
conditional floor, not a lower bound on the gap).  All results axiom-clean
(`{propext, Classical.choice, Quot.sound}`).  Issue #444.
-/

namespace ProximityGap.Frontier.CoshMGFSaddleFloorShape

open ProximityGap.Frontier.CoshMGFSaddleAssembled
open ProximityGap.Frontier.CoshMGFSaddle
open ProximityGap.Frontier.CoshMGFIdentity
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-- **The saddle floor in prize shape (pure ℝ).**  For `n > 0`, `q ≥ 2`, and `y > 0` with
`y² = 2·log q / n`, the closed-form saddle bound `log(2·q²)/y` is at most `(3/√2)·√(n·log q)`.
The constant `3/√2` is uniform over all `q ≥ 2`, `n > 0` and tight at `q = 2`. -/
theorem saddle_closedForm_le_sqrt_shape {n q y : ℝ} (hn : 0 < n) (hq : 2 ≤ q) (hy : 0 < y)
    (hsaddle : y ^ 2 = 2 * Real.log q / n) :
    Real.log (2 * q ^ 2) / y ≤ (3 / Real.sqrt 2) * Real.sqrt (n * Real.log q) := by
  -- `L = log q ≥ log 2 > 0`.
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq
  set L : ℝ := Real.log q with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hq
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le hlog2pos hL2
  -- rewrite `log(2 q²) = log 2 + 2 L`.
  have hlogexpand : Real.log (2 * q ^ 2) = Real.log 2 + 2 * L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  -- numerator is positive.
  have hnum_pos : (0 : ℝ) < Real.log 2 + 2 * L := by positivity
  -- RHS and a clean square comparison. Strategy: both sides nonneg; compare squares.
  have hRHS_nonneg : (0 : ℝ) ≤ (3 / Real.sqrt 2) * Real.sqrt (n * Real.log q) := by positivity
  have hLHS_nonneg : (0 : ℝ) ≤ Real.log (2 * q ^ 2) / y := by
    rw [hlogexpand]; positivity
  -- It suffices to compare squares.
  rw [← Real.sqrt_sq hLHS_nonneg, ← Real.sqrt_sq hRHS_nonneg]
  apply Real.sqrt_le_sqrt
  -- LHS² = (log2 + 2L)² / y² = (log2+2L)² * n/(2L).
  have hy2 : y ^ 2 = 2 * L / n := hsaddle
  have hy2_ne : y ^ 2 ≠ 0 := by rw [hy2]; positivity
  have h2L_ne : (2 : ℝ) * L ≠ 0 := by positivity
  have hn_ne : n ≠ 0 := ne_of_gt hn
  have hLHSsq : (Real.log (2 * q ^ 2) / y) ^ 2 = (Real.log 2 + 2 * L) ^ 2 * (n / (2 * L)) := by
    rw [hlogexpand, div_pow, hy2]
    rw [div_eq_iff (by positivity : (2 : ℝ) * L / n ≠ 0)]
    field_simp
  -- RHS² = (9/2) * (n * L).
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnLnonneg : (0 : ℝ) ≤ n * Real.log q := by positivity
  have hRHSsq : ((3 / Real.sqrt 2) * Real.sqrt (n * Real.log q)) ^ 2 = (9 / 2) * (n * L) := by
    rw [mul_pow, div_pow, Real.sq_sqrt hnLnonneg, hsqrt2sq]
    rw [← hL]
    ring
  rw [hLHSsq, hRHSsq]
  -- Reduce to (log2 + 2L)² ≤ 9 L²  via the common positive factor n/(2L).
  -- (log2+2L)² * (n/(2L)) ≤ (9/2)*(n*L)  ⟺  (log2+2L)² ≤ 9 L²  (mult by 2L/n > 0).
  have key : (Real.log 2 + 2 * L) ^ 2 ≤ 9 * L ^ 2 := by
    have h1 : Real.log 2 + 2 * L ≤ 3 * L := by linarith
    nlinarith [hnum_pos, hLpos, h1]
  -- Multiply `key` by `n/(2L) > 0`.
  have hfac_pos : (0 : ℝ) < n / (2 * L) := by positivity
  calc (Real.log 2 + 2 * L) ^ 2 * (n / (2 * L))
      ≤ (9 * L ^ 2) * (n / (2 * L)) := by
        apply mul_le_mul_of_nonneg_right key hfac_pos.le
    _ = (9 / 2) * (n * L) := by
        rw [eq_comm, ← sub_eq_zero]
        field_simp
        ring

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The explicit prize-floor-SHAPE sup-norm bound (conditional on the open MGF inequality).**
At the saddle `y*` (`y*² = 2·log q / n`, `y* > 0`, `n = |G| > 0`, `q = |F| ≥ 2`), if the char-`p`
even-moment MGF obeys the single open inequality `MGF(y*) ≤ q·exp(n·y*²/2)`, then the Gauss period
satisfies the **explicit prize floor**
`‖η_{b₀}‖ ≤ (3/√2)·√(|G|·log|F|)`.

Composition of the in-tree closed-form saddle bound (`period_le_saddle_closedForm`) with the pure-ℝ
shape lemma (`saddle_closedForm_le_sqrt_shape`).  This pins the absolute constant `C = 3/√2` in the
prize floor `C·√(n·log q)`, discharging the saddle file's asserted-but-unproven `Θ(√(n log q))`
collapse.  Conditional on the open core; no beyond-Johnson claim. -/
theorem period_le_floor_shape {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (b₀ : F)
    (hn : 0 < (G.card : ℝ))
    (hq2 : (2 : ℝ) ≤ (Fintype.card F : ℝ))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hMGF : (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
              ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    ‖eta ψ G b₀‖
      ≤ (3 / Real.sqrt 2) * Real.sqrt ((G.card : ℝ) * Real.log (Fintype.card F : ℝ)) := by
  have hclosed := period_le_saddle_closedForm (F := F) hψ G hy b₀ hn hsaddle hMGF
  have hshape := saddle_closedForm_le_sqrt_shape (n := (G.card : ℝ))
    (q := (Fintype.card F : ℝ)) (y := y) hn hq2 hy hsaddle
  exact hclosed.trans hshape

end ProximityGap.Frontier.CoshMGFSaddleFloorShape

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, NO sorryAx)
open ProximityGap.Frontier.CoshMGFSaddleFloorShape in
#print axioms saddle_closedForm_le_sqrt_shape
open ProximityGap.Frontier.CoshMGFSaddleFloorShape in
#print axioms period_le_floor_shape
