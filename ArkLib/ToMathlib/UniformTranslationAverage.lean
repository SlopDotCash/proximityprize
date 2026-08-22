/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ENNReal.Inv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Uniform translation-averaging over a finite word space

A self-contained averaging identity over a finite "word space" `ι → F`: averaging an event
`P (u₀ + γ • w)` over a uniformly random base word `u₀` and a uniformly random slope `γ ∈ F`
equals the uniform-word event `P u`.  Concretely, with `|ι → F|⁻¹` / `|F|⁻¹` the uniform weights,

`∑_{u₀} |ι→F|⁻¹ · (∑_{γ} |F|⁻¹ · 𝟙[P (u₀ + γ•w)])  =  ∑_{u} |ι→F|⁻¹ · 𝟙[P u]`.

The proof distributes the outer weight into the slope sum, swaps the two finite sums, applies the
translation bijection `u₀ ↦ u₀ + γ•w` (whose uniform weight is constant, hence invariant), and
collapses the now slope-independent sum via `|F| · |F|⁻¹ = 1`.

## Motivation (ABF26 Lemma 4.19 / DG25 Theorem 2.5, issue #77)

This is the measure-theoretic heart of the **covering-radius sampling** lower bound for the
correlated-agreement error `ε_ca`.  Once a word `w` is chosen beyond the covering radius (so the
pair `(u₀, w)` is never jointly `δ`-close), the `ε_ca` supremum over word-pairs dominates the
`u₀`-average of the line event, and this identity re-uniformizes that average into
`Pr_{u}[δᵣ(u, C) ≤ δ]`:

`ε_ca(C, δ) ≥ ⨆_{u₀} (line prob) ≥ ∑_{u₀} unif(u₀)·(line prob) = Pr_u[δᵣ(u,C) ≤ δ]`.

It is stated in raw `Finset.sum` / `(card)⁻¹` `ENNReal` form (no `Probability`/`MeasureTheory`
imports) so it is reusable and cheap to build; downstream the `Pr_{...}` notation is bridged to
these sums via `ProbabilityTheory.Pr_eq_tsum_indicator` + `tsum_fintype` + `uniformOfFintype_apply`.
-/

open scoped NNReal ENNReal BigOperators

namespace ArkLib

variable {F : Type} [Field F] [Fintype F] [Nonempty F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Uniform translation-averaging identity (the DG25 L4.19 sampling heart), `ENNReal` form.**

Averaging the line event `P (u₀ + γ•w)` over a uniform base word `u₀` and uniform slope `γ`
equals the uniform-word event `P u`. -/
theorem sum_uniform_line_indicator_eq (P : (ι → F) → Prop) [DecidablePred P] (w : ι → F) :
    (∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        ∑ γ : F, (Fintype.card F : ℝ≥0∞)⁻¹ * (if P (u₀ + γ • w) then (1 : ℝ≥0∞) else 0))
      = ∑ u : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * (if P u then (1 : ℝ≥0∞) else 0) := by
  classical
  -- distribute the outer constant into the γ-sum, then swap the two finite sums
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- translation invariance per slope γ: reindex u₀ ↦ u₀ + γ•w (a bijection)
  have tr : ∀ γ : F,
      (∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P (u₀ + γ • w) then (1 : ℝ≥0∞) else 0)))
        = ∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0)) := by
    intro γ
    exact Fintype.sum_equiv (Equiv.addRight (γ • w))
      (fun u₀ => (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P (u₀ + γ • w) then (1 : ℝ≥0∞) else 0)))
      (fun u => (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u then (1 : ℝ≥0∞) else 0)))
      (fun u₀ => rfl)
  simp_rw [tr]
  -- the inner sum no longer depends on γ; collapse the γ-sum (|F| copies)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hcard : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htop : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine Finset.sum_congr rfl (fun u₀ _ => ?_)
  calc (Fintype.card F : ℝ≥0∞) * ((Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0)))
      = (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          (((Fintype.card F : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹) *
            (if P u₀ then (1 : ℝ≥0∞) else 0)) := by ring
    _ = (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0) := by
          rw [ENNReal.mul_inv_cancel hcard htop, one_mul]

/-- **A uniform weighted average is at most the supremum.** Over a finite nonempty index, the
uniform average `∑_a |α|⁻¹ · f a` is bounded above by `⨆_a f a`.  Used to pass from the `ε_ca`
supremum over word-pairs to the `u₀`-average of the line event. -/
theorem sum_uniform_mul_le_iSup {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ≥0∞) :
    (∑ a : α, (Fintype.card α : ℝ≥0∞)⁻¹ * f a) ≤ ⨆ a, f a := by
  classical
  have hcard : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htop : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (∑ a : α, (Fintype.card α : ℝ≥0∞)⁻¹ * f a)
      ≤ ∑ _a : α, (Fintype.card α : ℝ≥0∞)⁻¹ * (⨆ b, f b) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul' le_rfl (le_iSup f a))
    _ = ⨆ b, f b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel hcard htop, one_mul]

end ArkLib
