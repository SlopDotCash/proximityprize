/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Census F3-11: the iid-Gaussian / EVT direct-proof shape is EXACTLY CIRCULAR (#444)

## The route (F3, sub-Gaussian tail / extreme-value)

Empirically the Paley/BGK maximum `M(n) = max_{b≠0}‖η_b‖` tracks the iid-Gaussian
extreme-value law
  `M ≈ C_evt · √(2 n log N)`,  with `C_evt → 1` from below   (`N = q-1` periods).
This is the prize SHAPE. The proposed **direct proof** is:

1. Show the period family `{η_b}` is *sub-Gaussian to depth `log N`*: there is a constant
   `c > 0` with `P(|η_b| > t·√n) ≤ e^{-c t²}` for all `t ≤ √(2 log N)`.
2. Union-bound over the `N` periods: the expected count of `b` with `|η_b| > t√n` is
   `≤ N·e^{-c t²}`, which falls below `1` at the threshold `t⋆` solving `c t⋆² = log N`,
   i.e. `t⋆ = √(log N / c)`. Hence `M ≤ t⋆√n = √(n log N / c)`.

If step 1 held with a *fixed* `c`, step 2 would deliver `M ≤ √(1/c)·√(n log N)` — the prize.

## The circularity (this file, machine-checked)

Normalize by `n log N` and work with squares (avoids `√`):

* the **union-bound ceiling** the route would prove:   `U² := (M_ceiling)²/(n log N) = 1/c`;
* the **EVT value** the route is trying to reach:        `V² := (M_emp)²/(n log N) = 2·C_evt²`.

For the proof to be *non-vacuous* it must produce `U² ≤ V²` from data independent of `C_evt`.
But the sub-Gaussian constant `c` is not free: calibrating the tail to the *observed* EVT
behaviour forces exactly

      `c = 1 / (2·C_evt²)`              (the F3-11 identity).

Substituting this `c` into the union-bound ceiling gives `U² = 1/c = 2·C_evt² = V²` — an
**identity for every `C_evt`**, not a bound. The constant `c` the proof *assumes* (sub-Gaussian
depth) is the constant `C_evt` the proof is *trying to establish* (EVT amplitude); they are the
same datum re-expressed. So the route is **CIRCULAR** (death-mode CIRCULAR): the only `c` that
makes step 2 reach the empirical `M` is the one already encoding `M`.

This sharpens the prior census status of F3-11 from "could not find the flaw" to a
**machine-checked algebraic equivalence**: `U² = V²` holds *identically* under the calibration
`c = 1/(2C²)`, hence the union bound never improves on its own input.

This does NOT refute Paley (Paley may still be true; the empirical `C_evt < 1` is consistent
with it). It refutes the *direct-proof shape*: an EVT/sub-Gaussian argument cannot prove Paley
because its only free constant is fixed by the very quantity it targets.
-/

namespace ProximityGap.Frontier.CensusF311

/-- The sub-Gaussian rate `c` that calibrates the tail `P(|η_b|>t√n) ≤ e^{-c t²}` to the
empirical EVT amplitude `C` (= `C_evt`).  This is the F3-11 calibration: `c = 1/(2C²)`. -/
noncomputable def cCalib (C : ℚ) : ℚ := 1 / (2 * C ^ 2)

/-- The **union-bound ceiling**, squared and normalized by `n log N`: `U²(c) = 1/c`. -/
noncomputable def U2 (c : ℚ) : ℚ := 1 / c

/-- The **EVT value**, squared and normalized by `n log N`: `V²(C) = 2 C²`. -/
def V2 (C : ℚ) : ℚ := 2 * C ^ 2

/-- **The F3-11 circularity identity.** Under the only calibration that lets the union bound
reach the empirical extreme-value law, the certified ceiling `U²` *equals* the target `V²`
for every `C ≠ 0`. The union bound therefore returns exactly its input: it is circular. -/
theorem ceiling_eq_target_under_calibration (C : ℚ) (hC : C ≠ 0) :
    U2 (cCalib C) = V2 C := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hCsq : C ^ 2 ≠ 0 := pow_ne_zero 2 hC
  unfold U2 cCalib V2
  field_simp

/-- Equivalent dual statement: the calibrated rate `c` is exactly the reciprocal of the EVT
target, `cCalib C = 1 / V2 C`. The "sub-Gaussian depth" datum and the "EVT amplitude" datum are
literally reciprocal, i.e. one and the same fact. -/
theorem calib_eq_inv_target (C : ℚ) : cCalib C = 1 / V2 C := by
  unfold cCalib V2
  ring

/-- **Concrete circular witness** at the empirical `C_evt = 0.964` (the `n = 64` fit, the largest
clean data point with `C_evt < 1`). The union-bound ceiling equals the EVT value exactly as a
rational — `decide`-checkable, no `native_decide`. -/
theorem circular_witness_C964 :
    U2 (cCalib (241 / 250)) = V2 (241 / 250) := by
  unfold U2 cCalib V2
  norm_num

/-- **The route proves nothing.** Formalized as: there is NO constant `C` for which the union
ceiling is *strictly below* the EVT value (a strict gain would be a genuine, non-circular bound).
Under the calibration the ceiling never beats the target — equality always. -/
theorem no_strict_improvement (C : ℚ) (hC : C ≠ 0) :
    ¬ (U2 (cCalib C) < V2 C) := by
  rw [ceiling_eq_target_under_calibration C hC]
  exact lt_irrefl _

/-- The gap `V² − U²` is identically zero under calibration: the certified ceiling has *zero
slack* over the empirical value, for all `C ≠ 0`. There is no room for the argument to do work. -/
theorem zero_slack (C : ℚ) (hC : C ≠ 0) : V2 C - U2 (cCalib C) = 0 := by
  rw [ceiling_eq_target_under_calibration C hC]; ring

end ProximityGap.Frontier.CensusF311
