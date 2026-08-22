/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Analysis.MeanInequalities

/-!
# height-gate POWER-MEAN: the higher-moment generalization of the AM-GM norm bound (#407)

`HeightGateAMGM.lean` proves the quadratic-mean (`r = 1`) norm bound

    `|N_{K/ℚ}(α)|² ≤ ( (1/m) Σ_σ ‖σα‖² )^m`,   `m = [K:ℚ]`,

the `GM ≤ QM` instance of AM-GM applied to the conjugate moduli `‖σα‖²`.  This file generalizes
it to **every even moment `2r` (`r ≥ 1`)**:

    `|N_{K/ℚ}(α)|^{2r} ≤ ( (1/m) Σ_σ ‖σα‖^{2r} )^m`.

(the `r = 1` case recovers `abs_norm_sq_le_quadratic_mean`.)  This is the **moment-method tool**
the prize's character-sum face actually consumes: the open core's face 3
(`GaussPeriodMomentBound.lean`) bounds `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` by a power-mean / `2r`-th
moment, then *minimizes over `r ≈ ln q`* to get the `√(2n ln q)` worst-case incomplete-sum bound —
a single fixed mean inequality (`r = 1`) gives only the exponent-`n/4` house regime, while the
free moment order `r` is what lets the Sidon/energy bootstrap drive the exponent down toward
`O(log)`.  This lemma is the analytic crux that lets the norm be controlled by the **`2r`-th
conjugate moment** rather than the second moment alone, so a sharper moment input (smaller
`Σ_σ ‖σα‖^{2r}` than the trivial `m·(max)^{2r}`) buys a sharper norm bound at the SAME `r` —
exactly the lever a power-mean tower needs.

## What is PROVED here (axiom-clean)

* `abs_norm_pow_le_power_mean` : the general `2r`-th power-mean norm bound (unconditional, any
  number field, any `r ≥ 1`).
* `abs_norm_sq_le_quadratic_mean'` : the `r = 1` specialization (re-derivation of the AM-GM crux,
  showing this file strictly subsumes the `HeightGateAMGM` analytic content).
* `abs_norm_pow_le_card_mul_max_moment` : the immediately consumable corollary — if every
  conjugate moment `‖σα‖^{2r} ≤ M`, then `|N(α)|^{2r} ≤ M^m`.  This is the shape the moment-method
  bootstrap plugs the energy bound into.

The bound is sharper than the house bound `|N| ≤ (max ‖σα‖)^m` for the same reason as `r = 1`:
the `2r`-th power mean of the conjugate moduli can be far below their max under cyclotomic
cancellation.  It does NOT, by itself, beat the intrinsic `n = 64` height-gate ceiling
(`HeightGateThresholdAnalysis.leverH_ceiling_is_64`) at a *fixed* `r`; its value is as the
`r`-parametrized substrate for the moment-method tower.
-/
set_option linter.style.longLine false
set_option autoImplicit false


open Finset NumberField Module Real

namespace ArkLib.ProximityGap.GatePowerMean

variable {K : Type*} [Field K] [NumberField K]

/-! ## The power-mean analytic crux (general even moment) -/

/-- **Power-mean / `2r`-th-moment norm bound.**  For any `α : K` in a number field and any
`r ≥ 1`,
`|N_{K/ℚ}(α)|^{2r} ≤ ( (1/m) Σ_σ ‖σα‖^{2r} )^m` with `m = #(K →ₐ[ℚ] ℂ) = [K:ℚ]`.

This is the geometric-mean–arithmetic-mean inequality `GM ≤ M_{2r}` applied to the `m` nonnegative
reals `‖σα‖^{2r}`, using `|N(α)| = ∏_σ ‖σα‖` (`Algebra.norm_eq_prod_embeddings`).  Specializing
`r = 1` recovers the quadratic-mean (AM-GM) bound; larger `r` controls the norm by a higher
conjugate moment, the lever the moment method exploits. -/
theorem abs_norm_pow_le_power_mean (α : K) (r : ℕ) (_hr : 1 ≤ r) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ^ (2 * r) ≤
      ((∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) / (Fintype.card (K →ₐ[ℚ] ℂ)))
        ^ (Fintype.card (K →ₐ[ℚ] ℂ)) := by
  classical
  set m := Fintype.card (K →ₐ[ℚ] ℂ) with hm
  have hmpos : 0 < m := by
    rw [hm, AlgHom.card_of_splits ℚ K ℂ (fun _ ↦ IsAlgClosed.splits _)]; exact finrank_pos
  -- `|N(α)| = ∏_σ ‖σα‖`
  have key : (algebraMap ℚ ℂ) (Algebra.norm ℚ α) = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  have hnabs : ((|Algebra.norm ℚ α| : ℚ) : ℝ) = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ := by
    have h0 : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
      simp [eq_ratCast, Complex.norm_ratCast, Rat.cast_abs]
    rw [← h0, key, norm_prod]
  -- `|N(α)|^{2r} = ∏_σ ‖σα‖^{2r}`
  have hpw : ((|Algebra.norm ℚ α| : ℚ) : ℝ) ^ (2 * r) = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r) := by
    rw [hnabs, ← Finset.prod_pow]
  -- AM-GM (uniform weights) on `z σ = ‖σα‖^{2r}`
  have hamgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (K →ₐ[ℚ] ℂ))
    (fun _ => (1 : ℝ)) (fun σ => ‖σ α‖ ^ (2 * r)) (fun _ _ => zero_le_one)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]; exact_mod_cast hmpos)
    (fun _ _ => pow_nonneg (norm_nonneg _) _)
  simp only [rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    at hamgm
  -- raise both sides to power `m`
  have hprodnn : (0 : ℝ) ≤ ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r) :=
    Finset.prod_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hlhsnn : (0 : ℝ) ≤ (∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) ^ ((m : ℝ)⁻¹) :=
    rpow_nonneg hprodnn _
  have hpow := pow_le_pow_left₀ hlhsnn hamgm m
  have hLHS : ((∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) ^ ((m : ℝ)⁻¹)) ^ m
      = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r) := by
    rw [← rpow_natCast ((∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) ^ ((m : ℝ)⁻¹)) m, ← rpow_mul hprodnn,
      inv_mul_cancel₀ (by exact_mod_cast hmpos.ne'), rpow_one]
  rw [hLHS] at hpow
  rw [hpw]; exact hpow

/-- **The `r = 1` specialization** (re-derivation of the AM-GM quadratic-mean crux).  Confirms this
file subsumes the analytic content of `HeightGateAMGM.abs_norm_sq_le_quadratic_mean`. -/
theorem abs_norm_sq_le_quadratic_mean' (α : K) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ^ 2 ≤
      ((∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) / (Fintype.card (K →ₐ[ℚ] ℂ)))
        ^ (Fintype.card (K →ₐ[ℚ] ℂ)) := by
  have h := abs_norm_pow_le_power_mean α 1 le_rfl
  simpa using h

/-! ## The consumable corollary: a uniform moment cap gives a norm bound -/

/-- **Moment-method consumer shape.**  If every conjugate `2r`-th moment is capped, `‖σα‖^{2r} ≤ M`
for all `σ` (with `0 ≤ M`), then `|N(α)|^{2r} ≤ M^m`, `m = [K:ℚ]`.

This is exactly the shape the open-core moment method (`GaussPeriodMomentBound.lean`) feeds the
energy bound `E_r(μ_n) ≤ (2r−1)‼·n^r` into: a per-conjugate moment cap `M` ⟹ a norm cap `M^m`, and
minimizing the resulting bound over the free moment order `r` is what drives the exponent below the
fixed-`r` house regime. -/
theorem abs_norm_pow_le_card_mul_max_moment (α : K) (r : ℕ) (hr : 1 ≤ r)
    {M : ℝ} (_hM : 0 ≤ M) (hcap : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r) ≤ M) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ^ (2 * r) ≤ M ^ (Fintype.card (K →ₐ[ℚ] ℂ)) := by
  classical
  set m := Fintype.card (K →ₐ[ℚ] ℂ) with hm
  have hmpos : 0 < m := by
    rw [hm, AlgHom.card_of_splits ℚ K ℂ (fun _ ↦ IsAlgClosed.splits _)]; exact finrank_pos
  refine (abs_norm_pow_le_power_mean α r hr).trans ?_
  -- the power mean is `≤ M` since each summand `≤ M`.
  have hsum_le : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) ≤ (m : ℝ) * M := by
    calc (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r))
        ≤ ∑ _σ : K →ₐ[ℚ] ℂ, M := Finset.sum_le_sum (fun σ _ => hcap σ)
      _ = (m : ℝ) * M := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hmean_le : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) / (m : ℝ) ≤ M := by
    rw [div_le_iff₀ (by positivity)]
    calc (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) ≤ (m : ℝ) * M := hsum_le
      _ = M * (m : ℝ) := by ring
  have hmean_nn : (0 : ℝ) ≤ (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ (2 * r)) / (m : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)) (by positivity)
  exact pow_le_pow_left₀ hmean_nn hmean_le m

end ArkLib.ProximityGap.GatePowerMean

#print axioms ArkLib.ProximityGap.GatePowerMean.abs_norm_pow_le_power_mean
#print axioms ArkLib.ProximityGap.GatePowerMean.abs_norm_sq_le_quadratic_mean'
#print axioms ArkLib.ProximityGap.GatePowerMean.abs_norm_pow_le_card_mul_max_moment
