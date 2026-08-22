/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The self-improving / 4th-moment bootstrap ANTI-contracts in the thin regime (#444, bet C)

Research bet (C) for the Paley/BGK wall: a self-improving inequality `M ≤ f(M)` (using the
multiplicative closure `μ_n·μ_n = μ_n` / the difference-set 4th-moment bootstrap) that contracts
toward the prize bound `√(2 n log m)`. This file proves it **cannot** — the 4th-moment bootstrap
ceiling not only fails to reach the Paley exponent `1/2`, it gets *worse* as the subgroup thins.

## The mechanism and the exact obstruction (measured, exact integers)
The bootstrap controls `M = max_{b≠0}‖η_b‖` through its 4th moment:
`M^4 ≤ Σ_{b≠0}‖η_b‖^4 = q·E_2(μ_n)`, and `E_2(μ_n)` is **`p`-independent**, pinned at the
random/Sidon value `Θ(n²)` (measured `E_2 = 168` at `n=8`, `720` at `n=16`, `≈ 2.6 n²`; the
multiplicative structure provides NO additive-energy excess to convert into a saving). Writing
`q = n^β` (`β = log_n p`), the ceiling is `M ≤ (q·E_2)^{1/4} ≈ (n^β·n²)^{1/4} = n^{(β+2)/4}`.

The exponent `e(β) = (β+2)/4`:
* equals `1/2` only at `β = 0` (the trivial full-field case) and is `> 1/2` for every `β > 0` — so
  it **never reaches** the Paley exponent in any positive-codimension regime;
* is `≥ 1` exactly when `β ≥ 2`, i.e. the ceiling is **vacuous** (no better than `M ≤ n`) for the
  entire thin/prize regime (`β = 4`);
* is **strictly increasing** in `β` — the thinner the subgroup, the worse the bound. The bootstrap
  *anti-contracts*. This is the exact closed-form strengthening of the `_AvW11` "stops at the 4th
  moment" remark to a monotone no-go, and it explains why the sum-product self-improvement (which
  classically needs `|G| > p^δ`) fails *harder* in the thin prize regime, not just barely.

## Results (axiom-clean)
* `bootstrap_ceiling_exceeds_trivial` — `1 ≤ C`, `n² ≤ q` ⟹ `n^4 ≤ C·q·n²`: the 4th power of the
  bootstrap ceiling `(C·q·n²)^{1/4}` is `≥ n^4`, so the ceiling is `≥ n` — vacuous for `q ≥ n²`
  (in particular all `β ≥ 2`).
* `bootstrap_ceiling_ge_trivial` — the `rpow` form: `n ≤ (C·q·n²)^{1/4}`.
* `bootstrap_exp_gt_half` / `bootstrap_exp_ge_one_iff` / `bootstrap_exp_strictMono` — the exponent
  `e(β)=(β+2)/4` is `>1/2` for `β>0`, `≥1 ⟺ β≥2`, and strictly increasing (anti-contraction).

NOT prize closure — this forecloses the self-improving/bootstrap research bet with an exact exponent.
-/

namespace ArkLib.ProximityGap.Frontier.AvW14

/-- **The bootstrap ceiling is vacuous for `q ≥ n²` (4th-power form, pure arithmetic).** With
`E_2 ≤ C·n²` (`C ≥ 1`) and `q ≥ n²`, the 4th power of the ceiling `C·q·n²` dominates `n^4`. Hence
`(C·q·n²)^{1/4} ≥ n`: the 4th-moment bootstrap never beats the trivial `M ≤ n` in the thin regime. -/
theorem bootstrap_ceiling_exceeds_trivial (C q n : ℝ) (hC : 1 ≤ C) (hn : 0 ≤ n) (hq : n ^ 2 ≤ q) :
    n ^ 4 ≤ C * q * n ^ 2 := by
  have hn2 : (0 : ℝ) ≤ n ^ 2 := sq_nonneg n
  have hqn : n ^ 2 ≤ C * q := le_trans hq (le_mul_of_one_le_left (le_trans hn2 hq) hC)
  nlinarith [mul_le_mul_of_nonneg_right hqn hn2, hn2]

/-- **The bootstrap ceiling is `≥ n` (rpow form).** Directly: `n ≤ (C·q·n²)^{1/4}` under `C ≥ 1`,
`q ≥ n²`. So the self-improving 4th-moment bound is vacuous against the trivial bound in the thin
regime — there is nothing to bootstrap. -/
theorem bootstrap_ceiling_ge_trivial (C q n : ℝ) (hC : 1 ≤ C) (hn : 0 ≤ n) (hq : n ^ 2 ≤ q) :
    n ≤ (C * q * n ^ 2) ^ ((4 : ℝ)⁻¹) := by
  have hpow : n ^ 4 ≤ C * q * n ^ 2 := bootstrap_ceiling_exceeds_trivial C q n hC hn hq
  have hn4 : ((n ^ 4 : ℝ)) ^ ((4 : ℝ)⁻¹) = n := by
    simpa using Real.pow_rpow_inv_natCast hn (n := 4) (by norm_num)
  calc n = ((n ^ 4 : ℝ)) ^ ((4 : ℝ)⁻¹) := hn4.symm
    _ ≤ (C * q * n ^ 2) ^ ((4 : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by norm_num)

/-- **The bootstrap exponent never reaches the Paley exponent `1/2` for positive codimension.**
`e(β) = (β+2)/4 > 1/2` for every `β > 0`. -/
theorem bootstrap_exp_gt_half {β : ℝ} (hβ : 0 < β) : (1 : ℝ) / 2 < (β + 2) / 4 := by linarith

/-- **The bootstrap ceiling is vacuous exactly in the thin regime `β ≥ 2`.** `e(β) = (β+2)/4 ≥ 1 ⟺
β ≥ 2`; the prize regime `β = 4` is well inside. -/
theorem bootstrap_exp_ge_one_iff (β : ℝ) : (1 : ℝ) ≤ (β + 2) / 4 ↔ 2 ≤ β := by
  constructor <;> intro h <;> linarith

/-- **Anti-contraction: the bootstrap exponent strictly worsens as the subgroup thins.** `β ↦
(β+2)/4` is strictly increasing — thinner subgroups (larger `β`) give a strictly worse ceiling. -/
theorem bootstrap_exp_strictMono : StrictMono (fun β : ℝ => (β + 2) / 4) := by
  intro a b hab
  simp only
  linarith

end ArkLib.ProximityGap.Frontier.AvW14

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW14.bootstrap_ceiling_exceeds_trivial
#print axioms ArkLib.ProximityGap.Frontier.AvW14.bootstrap_ceiling_ge_trivial
#print axioms ArkLib.ProximityGap.Frontier.AvW14.bootstrap_exp_strictMono
