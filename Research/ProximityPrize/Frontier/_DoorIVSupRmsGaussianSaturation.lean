/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Door IV: the worst-`b` saturates the GAUSSIAN extreme-value prediction `M ≈ √(n·log(p/n))` with
# no marginal slack — the L2 scale lower-bounds the sup (moments bound from the wrong side)

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_sup_vs_sndmoment_slack.py`.

## The probe verdict (reproducible, proper `μ_n`, p ≫ n³, never n = q−1, over coset reps)

Writing `rmsM = √(mean_b |η_b|²)` (the exact L2/Plancherel scale) and `M = max_b |η_b|`:

* `rmsM / √n = 1.000` to machine precision — confirms the Plancherel identity `mean_b |η_b|² = n`.
* `M / rmsM ≈ √(log(p/n))` with a NEARLY CONSTANT prefactor (measured `(M/rms)/√log ≈ 1.1–1.33`
  across n = 16…128, β = 4–4.5): the sup overshoots the L2 scale by exactly the prize's `√log`
  factor, i.e. `M ≈ √n · C·√(log(p/n))` saturates the prize form `M ≤ C√(n·log(p/n))`.
* the kurtosis `mean|η|⁴ / (mean|η|²)² → 3` (2.81, 2.90, 2.94, 2.97 ↑): the `|η_b|` marginal converges
  to the **Gaussian-modulus** law, whose extreme value over `N ≈ p/n` samples is `σ√(2 log N)` — exactly
  the observed `√log` overshoot.

So the worst-`b` sits **at** the Gaussian extreme-value prediction with **no slack in the marginal**.
A door-(iv) crack cannot come from the marginal distribution of `|η_b|` (Gaussian, EVT-saturated,
moment-determined = door (iii) = BGK); if one exists it must live in the JOINT correlation structure
across `b` that the marginal moments cannot see.

## The formalizable kernel (this file): the L2 scale is a LOWER bound on the sup

The exact mechanism by which moments bound the sup *from the wrong (lower) side*: for any finite
nonneg family, `(max)² ≥ mean of squares`. So `M ≥ rmsM = √n` — the Plancherel floor — and no
single-moment object can push the sup *down* below the EVT scale; it only certifies the easy lower
bound. This proves nothing about CORE and uses no completion; it pins the moment route as a
lower-bracket (wrong-side) lever, matching the probe's `rmsM/√n = 1` floor.
-/

namespace ProximityGap.Frontier.DoorIVSupRmsGaussianSaturation

open Finset

variable {ι : Type*}

/-- The squared maximum dominates the mean of squares: for a nonempty finite family of nonnegative
reals, `(max_i f_i)² ≥ (1/N) Σ f_i²`. Equivalently the sup is at least the L2 / rms scale `rmsM`.

This is the exact Plancherel floor mechanism (`M ≥ √(mean |η_b|²) = √n`): moments bound the sup from
the LOWER side only. -/
theorem sq_max_ge_mean_sq
    (f : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, (f i) ^ 2) / (s.card : ℝ)
      ≤ (s.sup' hs f) ^ 2 := by
  classical
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  rw [div_le_iff₀ hcard]
  -- Σ f_i² ≤ Σ (max)² = card · (max)²
  have hbound : ∑ i ∈ s, (f i) ^ 2 ≤ ∑ _i ∈ s, (s.sup' hs f) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hle : f i ≤ s.sup' hs f := Finset.le_sup' f hi
    have h0 : 0 ≤ f i := hf i hi
    exact pow_le_pow_left₀ h0 hle 2
  calc ∑ i ∈ s, (f i) ^ 2 ≤ ∑ _i ∈ s, (s.sup' hs f) ^ 2 := hbound
    _ = (s.card : ℝ) * (s.sup' hs f) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.sup' hs f) ^ 2 * (s.card : ℝ) := by ring

/-- Restated as a sup-vs-rms floor: the maximum is at least the root-mean-square. This is the
Plancherel lower bound `M ≥ rmsM`; combined with the probe's `rmsM = √n`, it is the floor
`M ≥ √n`. The moment route therefore only certifies the EASY (lower) side of the prize gap. -/
theorem max_ge_rms
    (f : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt ((∑ i ∈ s, (f i) ^ 2) / (s.card : ℝ)) ≤ s.sup' hs f := by
  have hsupnn : 0 ≤ s.sup' hs f := by
    obtain ⟨j, hj⟩ := hs
    exact le_trans (hf j hj) (Finset.le_sup' f hj)
  rw [show s.sup' hs f = Real.sqrt ((s.sup' hs f) ^ 2) from (Real.sqrt_sq hsupnn).symm]
  exact Real.sqrt_le_sqrt (sq_max_ge_mean_sq f s hs hf)

end ProximityGap.Frontier.DoorIVSupRmsGaussianSaturation

#print axioms ProximityGap.Frontier.DoorIVSupRmsGaussianSaturation.sq_max_ge_mean_sq
#print axioms ProximityGap.Frontier.DoorIVSupRmsGaussianSaturation.max_ge_rms
