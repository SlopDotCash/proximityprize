/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (lane saddletarget)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFSaddleFloorShape

/-!
# The saddle floor in the LITERAL prize TARGET shape `C·√(n·log(q/n))` (#444 §6.2)

`CoshMGFSaddleFloorShape.period_le_floor_shape` lands the conditional sup-norm bound
`‖η_{b₀}‖ ≤ (3/√2)·√(n·log q)`, pinning the absolute constant in the floor shape **with `log q`**.
The prize TARGET, however, is stated with `log(q/n)`:
```
        M(μ_n) = max_{b≠0} ‖η_b‖ ≤ C·√(n·log(p/n)).
```
`CoshMGFSaddleAssembled`'s docstring asserts (**as prose, never as a theorem**) that the saddle
collapse is the prize floor shape `C·√(n·log(q/n))` "up to the absolute constant `C`".  This file
discharges the remaining `log q → log(q/n)` conversion and pins the TARGET-shape absolute constant.

## What is proved here

### (1) The pure-ℝ conversion lemma (`sqrt_logq_le_sqrt_target`).

For `n > 0`, `log(q/n) > 0`, and the **prize-regime hypothesis** `log q ≤ 2·log(q/n)`,
```
        √(n·log q)  ≤  √2 · √(n·log(q/n)).
```
The hypothesis `log q ≤ 2·log(q/n)` is **exactly `β ≥ 2`** when `q = n^β` (then
`log q = β·log n`, `log(q/n) = (β−1)·log n`, and `β ≤ 2(β−1) ⟺ β ≥ 2`).  The prize regime is
`β ≈ 4–5`, comfortably inside.  The factor `√2` is uniform and **tight at `β = 2`**.
Probe: `scripts/probes/probe_saddle_target_shape.py` (0/63 violations; tight at `β = 2`).

### (2) The composed TARGET-shape saddle bound (`saddle_closedForm_le_sqrt_target`).

Chaining (1) onto `CoshMGFSaddleFloorShape.saddle_closedForm_le_sqrt_shape`:
```
        log(2·q²)/y*  ≤  3 · √(n·log(q/n)),
```
with the **absolute constant `3`** (`= (3/√2)·√2`), uniform over the prize regime `β ≥ 2`.

### (3) The TARGET-shape sup-norm floor (`period_le_target_shape`).

Chaining onto `CoshMGFSaddleFloorShape.period_le_floor_shape`:
```
        ‖η_{b₀}‖  ≤  3 · √(n·log(q/n)),
```
**conditional on the single open MGF inequality** (the char-`p` Wick bound at depth `r ≈ log q`,
the recognised open BGK core of #444).  This is now the LITERAL prize target shape `C·√(n·log(q/n))`
with `C = 3` pinned — the saddle lane's reduction is fully discharged down to the named open core.

## Honesty (rules 1, 3, 6 + ASYMPTOTIC GUARD)

NOT a CORE closure.  A NON-MOMENT, real-analytic SHAPE conversion that converts the already-proven
conditional `log q` floor into the literal prize TARGET form `C·√(n·log(q/n))` with `C = 3`.  It is
**conditional on the open core** (it inherits `hMGF` verbatim through `period_le_floor_shape`), adds
NO analytic input, and does NOT prove the open inequality.  It makes NO beyond-Johnson / capacity /
growth-law claim (a positive SHAPE of a conditional floor, not a lower bound on the gap), so it is
asymptotic-guard-compliant; the cliff-at-`n/2` is untouched.  The prize-regime hypothesis
`log q ≤ 2·log(q/n)` (`β ≥ 2`) is threaded as an EXPLICIT named hypothesis — nothing about the
regime is silently assumed.  All results axiom-clean (`{propext, Classical.choice, Quot.sound}`).
Issue #444.
-/

namespace ProximityGap.Frontier.CoshMGFSaddleTargetShape

open ProximityGap.Frontier.CoshMGFSaddleFloorShape
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-- **The `log q → log(q/n)` conversion (pure ℝ).** For `n > 0`, `logqn > 0`, and the prize-regime
hypothesis `Real.log q ≤ 2·logqn` (which is `β ≥ 2` when `q = n^β`, `logqn = log(q/n)`),
`√(n·log q) ≤ √2·√(n·logqn)`.  The factor `√2` is uniform and tight at `β = 2`. -/
theorem sqrt_logq_le_sqrt_target {n q logqn : ℝ} (hn : 0 < n) (hlogqn : 0 < logqn)
    (hregime : Real.log q ≤ 2 * logqn) :
    Real.sqrt (n * Real.log q) ≤ Real.sqrt 2 * Real.sqrt (n * logqn) := by
  -- RHS = √(2·n·logqn) since √2·√(n·logqn) = √(2·(n·logqn)) (all nonneg).
  have hnlogqn_nonneg : (0 : ℝ) ≤ n * logqn := by positivity
  have hRHS : Real.sqrt 2 * Real.sqrt (n * logqn) = Real.sqrt (2 * (n * logqn)) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (n * logqn)]
  rw [hRHS]
  -- monotonicity of √ + n·log q ≤ 2·n·logqn from the regime hypothesis.
  apply Real.sqrt_le_sqrt
  -- n·log q ≤ n·(2·logqn) = 2·(n·logqn).
  have hstep : n * Real.log q ≤ n * (2 * logqn) :=
    mul_le_mul_of_nonneg_left hregime hn.le
  calc n * Real.log q ≤ n * (2 * logqn) := hstep
    _ = 2 * (n * logqn) := by ring

/-- **The saddle floor in the literal prize TARGET shape (pure ℝ).** For `n > 0`, `q ≥ 2`, `y > 0`
with `y² = 2·log q / n`, `log(q/n) > 0`, and the prize-regime hypothesis `log q ≤ 2·log(q/n)`,
```
        log(2·q²)/y  ≤  3 · √(n·log(q/n)).
```
The absolute constant `3 = (3/√2)·√2` is uniform over the prize regime `β ≥ 2`.  Composition of
`CoshMGFSaddleFloorShape.saddle_closedForm_le_sqrt_shape` (the `log q` shape) with
`sqrt_logq_le_sqrt_target` (the `log q → log(q/n)` conversion). -/
theorem saddle_closedForm_le_sqrt_target {n q y logqn : ℝ} (hn : 0 < n) (hq : 2 ≤ q) (hy : 0 < y)
    (hsaddle : y ^ 2 = 2 * Real.log q / n) (hlogqn : 0 < logqn)
    (hregime : Real.log q ≤ 2 * logqn) :
    Real.log (2 * q ^ 2) / y ≤ 3 * Real.sqrt (n * logqn) := by
  -- (3/√2)·√(n·log q) ≤ (3/√2)·(√2·√(n·logqn)) = 3·√(n·logqn).
  have hshape := saddle_closedForm_le_sqrt_shape hn hq hy hsaddle
  have hconv := sqrt_logq_le_sqrt_target (n := n) (q := q) (logqn := logqn) hn hlogqn hregime
  have hcoef : (0 : ℝ) ≤ 3 / Real.sqrt 2 := by positivity
  -- chain: LHS ≤ (3/√2)·√(n logq) ≤ (3/√2)·√2·√(n logqn) = 3·√(n logqn).
  have hmid : (3 / Real.sqrt 2) * Real.sqrt (n * Real.log q)
      ≤ (3 / Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt (n * logqn)) :=
    mul_le_mul_of_nonneg_left hconv hcoef
  have hcollapse : (3 / Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt (n * logqn))
      = 3 * Real.sqrt (n * logqn) := by
    have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hs2)]
  calc Real.log (2 * q ^ 2) / y
      ≤ (3 / Real.sqrt 2) * Real.sqrt (n * Real.log q) := hshape
    _ ≤ (3 / Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt (n * logqn)) := hmid
    _ = 3 * Real.sqrt (n * logqn) := hcollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The explicit prize-TARGET-shape sup-norm bound (conditional on the open MGF inequality).**
At the saddle `y*` (`y*² = 2·log q / n`, `y* > 0`, `n = |G| > 0`, `q = |F| ≥ 2`), with
`log(q/n) > 0` and the prize-regime hypothesis `log q ≤ 2·log(q/n)` (i.e. `β ≥ 2`), if the
char-`p` even-moment MGF obeys the single open inequality `MGF(y*) ≤ q·exp(n·y*²/2)`, then the
Gauss period satisfies the **literal prize target floor**
```
        ‖η_{b₀}‖ ≤ 3·√(|G|·log(q/n)).
```
Composition of `CoshMGFSaddleFloorShape.period_le_floor_shape` (the `log q` floor) with
`sqrt_logq_le_sqrt_target`.  This pins the absolute constant `C = 3` in the literal prize target
shape `C·√(n·log(q/n))`, discharging the saddle lane's asserted-but-unproven target collapse down
to the single named open core.  Conditional on the open MGF inequality; no beyond-Johnson claim. -/
theorem period_le_target_shape {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y logqn : ℝ} (hy : 0 < y) (b₀ : F)
    (hn : 0 < (G.card : ℝ))
    (hq2 : (2 : ℝ) ≤ (Fintype.card F : ℝ))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hlogqn : 0 < logqn)
    (hregime : Real.log (Fintype.card F : ℝ) ≤ 2 * logqn)
    (hMGF : (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
              ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    ‖eta ψ G b₀‖ ≤ 3 * Real.sqrt ((G.card : ℝ) * logqn) := by
  have hfloor := period_le_floor_shape (F := F) hψ G hy b₀ hn hq2 hsaddle hMGF
  have hconv := sqrt_logq_le_sqrt_target (n := (G.card : ℝ))
    (q := (Fintype.card F : ℝ)) (logqn := logqn) hn hlogqn hregime
  -- ‖η‖ ≤ (3/√2)·√(n logq) ≤ (3/√2)·√2·√(n logqn) = 3·√(n logqn).
  have hcoef : (0 : ℝ) ≤ 3 / Real.sqrt 2 := by positivity
  have hmid : (3 / Real.sqrt 2) * Real.sqrt ((G.card : ℝ) * Real.log (Fintype.card F : ℝ))
      ≤ (3 / Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt ((G.card : ℝ) * logqn)) :=
    mul_le_mul_of_nonneg_left hconv hcoef
  have hcollapse : (3 / Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt ((G.card : ℝ) * logqn))
      = 3 * Real.sqrt ((G.card : ℝ) * logqn) := by
    have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hs2)]
  calc ‖eta ψ G b₀‖
      ≤ (3 / Real.sqrt 2) * Real.sqrt ((G.card : ℝ) * Real.log (Fintype.card F : ℝ)) := hfloor
    _ ≤ (3 / Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt ((G.card : ℝ) * logqn)) := hmid
    _ = 3 * Real.sqrt ((G.card : ℝ) * logqn) := hcollapse

end ProximityGap.Frontier.CoshMGFSaddleTargetShape

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, NO sorryAx)
open ProximityGap.Frontier.CoshMGFSaddleTargetShape in
#print axioms sqrt_logq_le_sqrt_target
open ProximityGap.Frontier.CoshMGFSaddleTargetShape in
#print axioms saddle_closedForm_le_sqrt_target
open ProximityGap.Frontier.CoshMGFSaddleTargetShape in
#print axioms period_le_target_shape
