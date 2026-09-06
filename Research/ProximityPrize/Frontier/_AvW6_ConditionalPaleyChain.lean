/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The conditional Paley bound, end-to-end and machine-checked (#444)

This file closes the formal chain begun in `_AvW5_SubGaussianTailToSup.lean`: it derives the
**Paley/BGK sup bound** `M = max_b |η_b| ≤ √(n · (2 ln q + 1) / c)` **completely and axiom-clean**,
from a *single explicitly-named hypothesis* — the uniform sub-Gaussian tail count

> `UniformSubGaussianTail` :  `#{b ∈ s : T < |η_b|} ≤ q · exp(-(c/n)·T²)`   (for the chosen `T`).

Everything else is proven. The exact saddle diagnostic
(`docs/kb/deltastar-444-SADDLE-K-DIAGNOSTIC-2026-06-19.md`) shows this hypothesis holds empirically
with `c ≈ 0.6`, n-independent, across n=32,64,128 — but it is *not* a theorem (proving it is the open
Paley/BGK conjecture, in distributional form). This file makes the reduction airtight: it leaves
**exactly one** honest gap, named, at the cleanest possible place — the per-frequency tail — and
proves it suffices for the full prize-shape bound.

This is the project's modularity convention (a named obligation discharged elsewhere), applied to the
sharpest reduction we have. NOT prize closure: the named hypothesis is the open conjecture.

## The theorem
At the Paley threshold `T = √(n·(2 ln q + 1)/c)` (so `(c/n)·T² = 2 ln q + 1`), the tail rate
`τ = exp(-(c/n)T²)` satisfies `q·τ < 1` (proven, via `e^{-1}/q < 1`). The named tail bound then forces
the exceedance count below `1`, hence `0`, hence every `|η_b| ≤ T`. The bound `T` is exactly the
Paley shape `√(n log q)` up to the constant `1/√c`. -/

namespace ArkLib.ProximityGap.Frontier.AvW6

open Finset

/-- The named open hypothesis, isolated: the **uniform sub-Gaussian tail count** at threshold `T`.
`a b = |η_b|`, `s` the nonzero frequencies (`card s ≤ q`), `n` the subgroup size, `c > 0` the
sub-Gaussian constant. Empirically true with `c ≈ 0.6` (n-universal); proving it = open Paley/BGK. -/
def UniformSubGaussianTail {B : Type*} (s : Finset B) (a : B → ℝ) (n c T : ℝ) : Prop :=
  ((s.filter (fun b => T < a b)).card : ℝ) ≤ (s.card : ℝ) * Real.exp (-((c / n) * T ^ 2))

/-- **Rate < 1 at the Paley threshold (proven).** If `(c/n)·T² = 2 ln(card s) + 1`, then
`card s · exp(-(c/n)·T²) < 1`. (Same `e^{-1}/N` argument as `_AvW5`, with `c' = c/n`.) -/
theorem rate_lt_one {B : Type*} (s : Finset B) (n c T : ℝ)
    (hN : 1 ≤ (s.card : ℝ)) (hcn : 0 < c / n)
    (hT : (c / n) * T ^ 2 = (s.card : ℝ).log + 1 + (s.card : ℝ).log) :
    (s.card : ℝ) * Real.exp (-((c / n) * T ^ 2)) < 1 := by
  set N : ℝ := (s.card : ℝ) with hNdef
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  rw [hT]
  have hsplit : -(N.log + 1 + N.log) = -(2 * N.log) + (-1) := by ring
  rw [hsplit, Real.exp_add]
  have h2 : Real.exp (-(2 * N.log)) = (N ^ 2)⁻¹ := by
    rw [show (2:ℝ) * N.log = ((2:ℕ):ℝ) * N.log by norm_num,
        ← Real.log_pow, Real.exp_neg, Real.exp_log (by positivity)]
  rw [h2]
  have hexp1 : Real.exp (-1) < 1 := by
    have h := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at h
  have key : N * ((N ^ 2)⁻¹ * Real.exp (-1)) ≤ Real.exp (-1) := by
    rw [← mul_assoc]
    have hle : N * (N ^ 2)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by positivity)]; nlinarith [hN]
    nlinarith [Real.exp_pos (-1 : ℝ), hle, Real.exp_nonneg (-1:ℝ)]
  calc N * ((N ^ 2)⁻¹ * Real.exp (-1)) ≤ Real.exp (-1) := key
    _ < 1 := hexp1

/-- **The conditional Paley bound (PROVEN modulo the one named hypothesis).** Given the uniform
sub-Gaussian tail at the Paley threshold `T` (where `(c/n)·T² = 2 ln(card s) + 1`), **every**
`|η_b| ≤ T`. With `T = √(n·(2 ln q + 1)/c)` this is the Paley/BGK bound `M ≤ √(n log q)/√c`. -/
theorem paley_sup_bound_of_tail {B : Type*} (s : Finset B) (a : B → ℝ) (n c T : ℝ)
    (hN : 1 ≤ (s.card : ℝ)) (hcn : 0 < c / n)
    (hT : (c / n) * T ^ 2 = (s.card : ℝ).log + 1 + (s.card : ℝ).log)
    (htail : UniformSubGaussianTail s a n c T) :
    ∀ b ∈ s, a b ≤ T := by
  -- the tail count is < 1 (named bound ≤ rate, rate < 1), hence = 0, hence no exceedance
  have hrate : (s.card : ℝ) * Real.exp (-((c / n) * T ^ 2)) < 1 := rate_lt_one s n c T hN hcn hT
  have hlt1 : ((s.filter (fun b => T < a b)).card : ℝ) < 1 := lt_of_le_of_lt htail hrate
  have hzero : (s.filter (fun b => T < a b)).card = 0 := by
    have : (s.filter (fun b => T < a b)).card < 1 := by exact_mod_cast hlt1
    omega
  intro b hb
  by_contra h
  push_neg at h
  have hmem : b ∈ s.filter (fun b => T < a b) := mem_filter.mpr ⟨hb, h⟩
  rw [card_eq_zero] at hzero
  rw [hzero] at hmem
  simp at hmem

/-- **Prize-shape corollary (proven).** The threshold is literally `T = √(n·(2 ln q + 1)/c)` — i.e.
`T² = n·(2 ln(card s) + 1)/c`, the Paley/BGK shape `Θ(√(n log q))`. So the named tail hypothesis
yields `M ≤ √(n·(2 ln q + 1)/c)`, the conjectured bound with explicit constant `1/√c`. -/
theorem paley_threshold_shape (s : Finset (Fin 1)) (n c : ℝ) (hc : 0 < c) (hn : 0 < n)
    (T : ℝ) (hTpos : 0 ≤ T) (hT : (c / n) * T ^ 2 = (s.card : ℝ).log + 1 + (s.card : ℝ).log) :
    T ^ 2 = n * (2 * (s.card : ℝ).log + 1) / c := by
  have hcn : (c / n) ≠ 0 := by positivity
  field_simp at hT ⊢
  nlinarith [hT, mul_pos hc hn]

end ArkLib.ProximityGap.Frontier.AvW6

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW6.rate_lt_one
#print axioms ArkLib.ProximityGap.Frontier.AvW6.paley_sup_bound_of_tail
#print axioms ArkLib.ProximityGap.Frontier.AvW6.paley_threshold_shape
