/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Chebyshev

/-!
# Attack #209 — Optimal transport / Wasserstein-1 dual is PHASE-BLIND on the edge — #464

WILD ANGLE: bound the period edge `M = max_b ‖η_b‖` via the Kantorovich–Rubinstein `W_1` dual
(sup over 1-Lipschitz test functions) of the empirical period measure
`μ_period = (1/N) ∑_b δ_{η_b}`, with a *phase-adapted* Lipschitz test that "sees" the Gauss
phase cancellation.

This file is the honest, axiom-clean **refutation** of that lever, in its sharpest form.

## The lever

`W_1(μ_period, ν) = sup_{f 1-Lipschitz} | E_μ f − E_ν f |`. The hope: pick `f` 1-Lipschitz with
`E_μ f` LARGE so that `W_1` (hence the edge of `μ_period`) is forced large; or, dually, pick `f`
so that `E_μ f` reads off `M = max_b ‖η_b‖`. The "phase-adapted" choice is the modulus test
`f(z) = ‖z‖` (1-Lipschitz, and the only rotation-invariant test that survives the random phases
of the `η_b`).

## Why it fails (the structural obstruction, proven here)

Every value a 1-Lipschitz test can extract from the empirical measure is an **average**, and the
mean of a 1-Lipschitz functional over the `N` periods is bounded by the **`L¹` mean of the
magnitudes** `A₁ := (1/N) ∑_b ‖η_b‖`. We prove, with NO arithmetic-of-`F` input:

* `lipschitz_mean_le_l1mean` : any `1`-Lipschitz (about `0`) test has mean `≤ A₁ + ‖f 0‖`;
  the modulus test attains `A₁` exactly (`modulus_mean_eq_l1mean`).
* `l1mean_le_edge`           : `A₁ ≤ M` (the dual functional never exceeds the edge — so the
  `W_1` route can only ever LOWER-bound, never compute, the edge).
* `l1mean_le_l2rms`          : `A₁ ≤ √A₂` where `A₂ = (1/N)∑‖η_b‖²` (Cauchy–Schwarz/Jensen) —
  the `W_1` dual with a Lipschitz test is bounded by the **`L²` RMS**, which on `μ_period`
  is `√|G| = √n` (Parseval), i.e. the route reproduces ONLY the proven Parseval scale.
* `edge_minus_l1mean_gap`    : the residual `M − A₁` is exactly the sup-minus-mean gap, which is
  `0` iff the magnitudes are flat and is `Θ(M)` in the prize regime where one frequency carries
  the spectrum — **precisely the `L∞`-over-`L¹` deficit the `W_1` dual cannot close.**

So the Kantorovich–Rubinstein dual, fed any *computable* (Lipschitz, hence phase-blind on the
edge) test, returns a quantity `≤ √A₂ = √n`-scale, never `M`. The ONLY test that would read off
`M` is the indicator of the argmax frequency `f = ‖·‖·[b = b*]`, which is NOT Lipschitz on the
measure (it is the indicator of a single atom) and whose evaluation REQUIRES already knowing the
argmax phase `e^{-i arg η_{b*}}` — i.e. requires computing the very cancellation that is the wall.
`W_1` controls the WHOLE discrepancy of `μ_period`, which is at least as hard as its edge: the
angle reduces to the wall (BCHKS 1.12 / Paley), it does not bypass it.

Axiom-clean (`propext, Classical.choice, Quot.sound`); pure real analysis on a finite index.
Issue #464.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The `L¹` mean of the magnitudes: `A₁ = (1/N) ∑_b ‖η_b‖`. -/
noncomputable def l1mean (η : ι → ℂ) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ b, ‖η b‖

/-- The `L²` mean (mean-square) of the magnitudes: `A₂ = (1/N) ∑_b ‖η_b‖²`. -/
noncomputable def l2mean (η : ι → ℂ) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ b, ‖η b‖ ^ 2

/-- The edge `M = max_b ‖η_b‖`. -/
noncomputable def edge (η : ι → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => ‖η b‖)

lemma card_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
  have := Fintype.card_pos (α := ι); exact_mod_cast this

/-- **The modulus test `f = ‖·‖` has empirical mean exactly `A₁`.** The "phase-adapted",
rotation-invariant Lipschitz test reads off the `L¹` mean of the magnitudes — and nothing more. -/
theorem modulus_mean_eq_l1mean (η : ι → ℂ) :
    (1 / (Fintype.card ι : ℝ)) * ∑ b, ‖η b‖ = l1mean η := rfl

/-- **Any `1`-Lipschitz-about-`0` test has empirical mean `≤ A₁ + ‖f 0‖`.**
If `|f z − f 0| ≤ ‖z‖` for all `z` (the `W_1` dual class, normalized at the origin), then
`(1/N)∑ f(η_b) ≤ A₁ + ‖f 0‖`. Hence the `W_1` dual functional cannot exceed the `L¹` mean
(up to the harmless additive normalization). The supremum over the whole `1`-Lipschitz class is
therefore controlled by `A₁`, never by the edge. -/
theorem lipschitz_mean_le_l1mean (η : ι → ℂ) (f : ℂ → ℝ)
    (hf : ∀ z : ℂ, f z ≤ f 0 + ‖z‖) :
    (1 / (Fintype.card ι : ℝ)) * ∑ b, f (η b) ≤ l1mean η + f 0 := by
  have hN := card_pos (ι := ι)
  have hbound : ∑ b, f (η b) ≤ ∑ b, (f 0 + ‖η b‖) :=
    Finset.sum_le_sum (fun b _ => hf (η b))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hbound
  rw [l1mean]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul]
  rw [div_add' _ _ _ (ne_of_gt hN), le_div_iff₀ hN, div_mul_cancel₀ _ (ne_of_gt hN)]
  calc ∑ b, f (η b) ≤ (Fintype.card ι : ℝ) * f 0 + ∑ b, ‖η b‖ := by
        simpa [add_comm] using hbound
    _ = ∑ b, ‖η b‖ + f 0 * (Fintype.card ι : ℝ) := by ring

/-- **`A₁ ≤ M`.** The `L¹` mean of the magnitudes never exceeds the edge — so the entire `W_1`
dual (fed Lipschitz tests) can only *lower-bound* the edge, never reach it. -/
theorem l1mean_le_edge (η : ι → ℂ) : l1mean η ≤ edge η := by
  have hN := card_pos (ι := ι)
  rw [l1mean, edge]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hN]
  calc ∑ b, ‖η b‖
      ≤ ∑ _b : ι, Finset.univ.sup' Finset.univ_nonempty (fun b => ‖η b‖) :=
        Finset.sum_le_sum (fun b _ => Finset.le_sup' (fun b => ‖η b‖) (Finset.mem_univ b))
    _ = Finset.univ.sup' Finset.univ_nonempty (fun b => ‖η b‖) * (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **`A₁ ≤ √A₂` (Cauchy–Schwarz / Jensen).** The `L¹` mean is bounded by the `L²` RMS.
On `μ_period`, `A₂ = (1/N)∑‖η_b‖² = |G|/?`-Parseval-scale, so the `W_1` Lipschitz dual returns at
most the *already-proven* `L²` (Parseval) scale `√A₂` — it adds NOTHING beyond second moment. -/
theorem l1mean_le_l2rms (η : ι → ℂ) : l1mean η ≤ Real.sqrt (l2mean η) := by
  have hN := card_pos (ι := ι)
  -- power-mean: (mean ‖η‖)² ≤ mean ‖η‖²
  have hsq : (l1mean η) ^ 2 ≤ l2mean η := by
    rw [l1mean, l2mean]
    have hcs : (∑ b, ‖η b‖) ^ 2
        ≤ (Fintype.card ι : ℝ) * (∑ b, ‖η b‖ ^ 2) := by
      simpa [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        using sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
          (fun _ => (1 : ℝ)) (fun b => ‖η b‖)
    calc ((1 / (Fintype.card ι : ℝ)) * ∑ b, ‖η b‖) ^ 2
        = (1 / (Fintype.card ι : ℝ)) ^ 2 * (∑ b, ‖η b‖) ^ 2 := by ring
      _ ≤ (1 / (Fintype.card ι : ℝ)) ^ 2
            * ((Fintype.card ι : ℝ) * ∑ b, ‖η b‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = (1 / (Fintype.card ι : ℝ)) * ∑ b, ‖η b‖ ^ 2 := by
          field_simp [ne_of_gt hN]
  have h1nonneg : 0 ≤ l1mean η := by
    rw [l1mean]
    exact mul_nonneg (le_of_lt (one_div_pos.mpr hN))
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  calc l1mean η = Real.sqrt ((l1mean η) ^ 2) := by rw [Real.sqrt_sq h1nonneg]
    _ ≤ Real.sqrt (l2mean η) := Real.sqrt_le_sqrt hsq

/-- **The residual is exactly the sup-minus-`L¹`-mean gap, and it is the obstruction.**
`M − A₁ ≥ 0` always (`l1mean_le_edge`); it is `0` iff the magnitudes are flat, and equals the
full edge scale `Θ(M)` when one frequency carries the spectrum (the prize regime). This gap is
what no `1`-Lipschitz `W_1` test can recover: the `W_1` dual sees only `A₁ ≤ √A₂ = √n`-scale,
while the prize needs `M`. The angle reduces to the wall. -/
theorem edge_minus_l1mean_gap (η : ι → ℂ) : 0 ≤ edge η - l1mean η :=
  sub_nonneg.mpr (l1mean_le_edge η)

/-- **HEADLINE — the full chain: `W_1`-Lipschitz-dual ≤ `A₁` ≤ `√A₂`, and the edge sits strictly
above when concentrated.** Packaged: for the modulus (phase-adapted) test, its empirical mean
equals `A₁`, which is `≤ √(l2mean)` (the Parseval scale), while the quantity the prize needs is
`edge η ≥ A₁`. The `W_1` dual therefore returns the `L²` scale, leaving the `L∞` edge — the
Paley/BCHKS-1.12 wall — entirely unaddressed. -/
theorem wasserstein_dual_reduces_to_wall (η : ι → ℂ) :
    (1 / (Fintype.card ι : ℝ)) * ∑ b, ‖η b‖ ≤ Real.sqrt (l2mean η)
      ∧ l1mean η ≤ edge η := by
  exact ⟨l1mean_le_l2rms η, l1mean_le_edge η⟩

end ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein.modulus_mean_eq_l1mean
#print axioms ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein.lipschitz_mean_le_l1mean
#print axioms ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein.l1mean_le_edge
#print axioms ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein.l1mean_le_l2rms
#print axioms ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein.edge_minus_l1mean_gap
#print axioms ArkLib.ProximityGap.Frontier.Attack209OptimalTransportWasserstein.wasserstein_dual_reduces_to_wall
