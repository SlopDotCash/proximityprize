/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodSidonBound

/-!
# The Sidon worst-period bound in explicit fourth-root / `√` form (#389/#444)

`WorstPeriodSidonBound.worst_period_sidon_le` proves the *fourth-power* form
`‖η_b‖⁴ ≤ 3·q·|G|²` for every Gauss period under the Sidon (rep-≤ 2) hypothesis, and its docstring
states the sup-norm consequence `max_b ‖η_b‖ ≤ (3q)^{1/4}·√|G|` only as PROSE — the explicit
`Real.rpow` / `Real.sqrt` inequality was never a theorem. This file supplies it:

> `worst_period_sidon_sqrt_le` :  `‖η_b‖ ≤ (3·q)^{1/4} · √|G|`   (every `b`, Sidon regime).

Proof: take the positive 4th root of `‖η_b‖⁴ ≤ 3·q·|G|²` (`Real.rpow` with exponent `1/4`,
`Real.pow_rpow_inv_natCast`), and `(|G|²)^{1/4} = √|G|`, `(3q·|G|²)^{1/4} = (3q)^{1/4}·√|G|`.

The companion `worst_period_sidon_below_sqrt_q` records the sub-`√q` consequence cleanly: in the thin
range `3|G|² ≤ q` the worst period is `≤ √q` (the completion bound), with strict slack growing as
`|G|` shrinks below `√(q/3)`.

## Honesty (scope)

This is the `r = 2` (Sidon / rep-≤ 2) instance of the dyadic √-cancellation conjecture, in explicit
sup-norm form. It is a genuine SUB-`√q` bound but only in the very thin range `|G| ≤ √(q/3)`; at the
prize scale `q = n^β` (`β > 2`) this range is met, but the bound `(3q)^{1/4}√n ≈ q^{1/4}√n` is the
`r = 2` ceiling, NOT the prize target `√(n·log q)` (which needs the bound at every depth `r ≈ log q`).
CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN — this only extends the proven `r = 2` brick to its stated
sup-norm conclusion.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.WorstPeriodSidon

namespace ProximityGap.Frontier.SidonWorstPeriodSqrt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Explicit fourth-root / `√` form of the Sidon worst-period bound.** Under the Sidon (rep-≤ 2)
hypothesis, every Gauss period obeys `‖η_b‖ ≤ (3·q)^{1/4}·√|G|`. The 4th-root of the proven
`‖η_b‖⁴ ≤ 3·q·|G|²`. -/
theorem worst_period_sidon_sqrt_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ 2) (b : F) :
    ‖eta ψ G b‖
      ≤ (3 * (Fintype.card F : ℝ)) ^ ((4 : ℝ)⁻¹) * Real.sqrt (G.card : ℝ) := by
  have hpow4 : ‖eta ψ G b‖ ^ 4 ≤ 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 :=
    worst_period_sidon_le hψ G hrep b
  have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  have hrhs_nn : (0 : ℝ) ≤ 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by positivity
  -- ‖η_b‖ = (‖η_b‖⁴)^{1/4} ≤ (3q|G|²)^{1/4}
  have h4ne : (4 : ℕ) ≠ 0 := by norm_num
  have hstep : ‖eta ψ G b‖ ≤ (3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2) ^ ((4 : ℝ)⁻¹) := by
    have hb4 : (‖eta ψ G b‖ ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ)⁻¹) = ‖eta ψ G b‖ :=
      Real.pow_rpow_inv_natCast hnn h4ne
    calc ‖eta ψ G b‖
        = (‖eta ψ G b‖ ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ)⁻¹) := hb4.symm
      _ ≤ (3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2) ^ (((4 : ℕ) : ℝ)⁻¹) :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow4) (by positivity)
      _ = (3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2) ^ ((4 : ℝ)⁻¹) := by norm_num
  -- (3q·|G|²)^{1/4} = (3q)^{1/4}·√|G|
  have hsplit : (3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2) ^ ((4 : ℝ)⁻¹)
      = (3 * (Fintype.card F : ℝ)) ^ ((4 : ℝ)⁻¹) * Real.sqrt (G.card : ℝ) := by
    have h3q : (0 : ℝ) ≤ 3 * (Fintype.card F : ℝ) := by positivity
    have hG2 : (0 : ℝ) ≤ (G.card : ℝ) ^ 2 := by positivity
    rw [Real.mul_rpow h3q hG2]
    congr 1
    -- (|G|²)^{1/4} = √|G|
    rw [show (G.card : ℝ) ^ 2 = (G.card : ℝ) ^ (2 : ℕ) by norm_num,
        ← Real.rpow_natCast (G.card : ℝ) 2, ← Real.rpow_mul (by positivity),
        Real.sqrt_eq_rpow]
    norm_num
  rw [hsplit] at hstep
  exact hstep

/-- **Sub-`√q` consequence in `√` form.** In the thin Sidon range `3|G|² ≤ q`, the worst period is at
most the completion bound `√q`. (From `worst_period_sidon_le_completion_pow4 : ‖η_b‖⁴ ≤ q²`, take the
4th root: `‖η_b‖ ≤ (q²)^{1/4} = √q`.) -/
theorem worst_period_sidon_below_sqrt_q {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ 2) (b : F)
    (hthin : 3 * G.card ^ 2 ≤ Fintype.card F) :
    ‖eta ψ G b‖ ≤ Real.sqrt (Fintype.card F : ℝ) := by
  have hpow4 : ‖eta ψ G b‖ ^ 4 ≤ (Fintype.card F : ℝ) ^ 2 :=
    worst_period_sidon_le_completion_pow4 hψ G hrep b hthin
  have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  have h4ne : (4 : ℕ) ≠ 0 := by norm_num
  have hb4 : (‖eta ψ G b‖ ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ)⁻¹) = ‖eta ψ G b‖ :=
    Real.pow_rpow_inv_natCast hnn h4ne
  calc ‖eta ψ G b‖
      = (‖eta ψ G b‖ ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ)⁻¹) := hb4.symm
    _ ≤ ((Fintype.card F : ℝ) ^ 2) ^ (((4 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow4) (by positivity)
    _ = Real.sqrt (Fintype.card F : ℝ) := by
          rw [show (Fintype.card F : ℝ) ^ 2 = (Fintype.card F : ℝ) ^ (2 : ℕ) by norm_num,
              ← Real.rpow_natCast (Fintype.card F : ℝ) 2, ← Real.rpow_mul (by positivity),
              Real.sqrt_eq_rpow]
          norm_num

end ProximityGap.Frontier.SidonWorstPeriodSqrt

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SidonWorstPeriodSqrt.worst_period_sidon_sqrt_le
#print axioms ProximityGap.Frontier.SidonWorstPeriodSqrt.worst_period_sidon_below_sqrt_q
