/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WeightedAgreement
import Mathlib.FieldTheory.Finite.Basic

/-!
# Why the weighted-agreement axioms carry `0 < sqrtRate`

The four weighted-agreement axioms in `WeightedAgreement.lean` bound the agreement set from below
by thresholds that divide by `sqrtRate deg domain`. Lean defines `x / 0 = 0`, so at `deg = 0`
(Reed-Solomon code `{0}`, `sqrtRate = 0`) every such threshold collapses to `0`. The remaining
hypothesis then only asks for one curve point with agreement `≥ α` against the zero word, and that
point can be `u 0 + u 1 = 0` with `u 0 = 1`, `u 1 = -1`, while no common agreement set exists.

`UnguardedCurvePrimed` is the statement of `weighted_correlated_agreement_for_parameterized_curves'`
as it stood before the `hrate` hypothesis was added. `not_unguardedCurvePrimed` proves that
statement is false, so the guard cannot be removed.
-/

open ProximityGap.WeightedAgreement NNReal

namespace ProximityGap.WeightedAgreement.Degenerate

/-- The primed curve axiom without the `0 < sqrtRate` guard. -/
def UnguardedCurvePrimed : Prop :=
  ∀ {ι : Type} [Fintype ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {l : ℕ} {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F}
    {μ : ι → Set.Icc (0 : ℚ) 1} {M m : ℕ},
    3 ≤ m →
    (∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
    ∀ {α : ℝ≥0},
    ReedSolomon.sqrtRate deg domain * (1 + 1 / (2 * m : ℝ)) ≤ α →
    (Finset.card ({z : F | agree_set μ (Curve.polynomialCurveEval (F := F) (A := F) u z)
        (ReedSolomon.finCarrier domain deg) ≥ α} : Finset F) : ℝ) >
      max ((1 + 1 / (2 * m : ℝ)) ^ 7 * m ^ 7 * (Fintype.card ι) ^ 2 * (l + 1) /
            (3 * (ReedSolomon.sqrtRate deg domain : ℝ) ^ 3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) /
            (ReedSolomon.sqrtRate deg domain).toReal) →
    ∃ v : Fin (l + 2) → ι → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      mu_set μ { i : ι | ∀ j, u j i = v j i } ≥ α

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- One coordinate in `ZMod 3`. -/
def dom : Fin 1 ↪ ZMod 3 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

lemma code_zero {w : Fin 1 → ZMod 3} (hw : w ∈ ReedSolomon.code dom 0) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := hw
  have : y = 0 := by simpa [Polynomial.mem_degreeLT] using hy
  subst this
  simp

lemma dim0 : LinearCode.dim (ReedSolomon.code (ι := Fin 1) (F := ZMod 3) dom 0) = 0 :=
  ReedSolomon.dim_eq_deg_of_le' (ι := Fin 1) (F := ZMod 3) (α := dom) (by simp)

/-- At `deg = 0` the square-root rate is `0`, so the guard `0 < sqrtRate` excludes this case. -/
lemma sqrtRate_zero_deg : ReedSolomon.sqrtRate (ι := Fin 1) (F := ZMod 3) 0 dom = 0 := by
  unfold ReedSolomon.sqrtRate LinearCode.rate
  rw [dim0]
  simp

lemma finCarrier_zero_deg :
    ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0 = {0} := by
  ext w
  simp only [ReedSolomon.finCarrier, Set.mem_toFinset, Finset.mem_singleton]
  constructor
  · intro h; exact code_zero h
  · rintro rfl; exact Submodule.zero_mem _

/-- `u 0 = 1`, `u 1 = -1`, so `u 0 + 1 • u 1 = 0`. -/
def u : Fin (0 + 2) → Fin 1 → ZMod 3 := ![fun _ => 1, fun _ => -1]

/-- Unit weights. -/
def mu : Fin 1 → Set.Icc (0 : ℚ) 1 := fun _ => ⟨1, by simp⟩

lemma agree_zero_ge : (1 : ℝ) ≤ agree_set mu (0 : Fin 1 → ZMod 3)
    (ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0) := by
  have h0 : (0 : Fin 1 → ZMod 3) ∈
      ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0 := by
    rw [finCarrier_zero_deg]; simp
  have := Finset.le_max' (Finset.image (agree mu (0 : Fin 1 → ZMod 3))
    (ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0)) (agree mu 0 0)
    (Finset.mem_image_of_mem _ h0)
  refine le_trans ?_ this
  simp [agree, mu]

/-- The unguarded statement is false: it is refuted at `deg = 0`. -/
theorem not_unguardedCurvePrimed : ¬ UnguardedCurvePrimed := by
  intro hax
  have hsq := sqrtRate_zero_deg
  have h := hax (ι := Fin 1) (F := ZMod 3) (l := 0) (u := u) (deg := 0)
    (domain := dom) (μ := mu) (M := 1) (m := 3) (by norm_num) (fun i => ⟨1, by simp [mu]⟩)
    (α := 1 / 2) (by simp [hsq]) (by
      rw [hsq]
      simp only [Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        pow_zero, one_smul, Nat.mod_succ, pow_one, one_div, NNReal.coe_inv, NNReal.coe_ofNat,
        ge_iff_le, Nat.cast_ofNat, mul_inv_rev, Fintype.card_unique, Nat.cast_one, one_pow,
        mul_one, CharP.cast_eq_zero, zero_add, coe_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, div_zero, max_self, gt_iff_lt, Nat.cast_pos,
        Finset.card_pos]
      refine ⟨1, ?_⟩
      have e : u 0 + (1 : ZMod 3) • u 1 = 0 := by
        funext i; simp [u]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show ((2 : ℝ)⁻¹) ≤ agree_set mu (u 0 + (1 : ZMod 3) • u 1)
        (ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0)
      rw [e]
      exact le_trans (by norm_num) agree_zero_ge)
  obtain ⟨v, hv, hmu⟩ := h
  have h0 : v 0 0 = 0 := by
    have := code_zero (hv 0); simp [this]
  have hempty : ({i : Fin 1 | ∀ j : Fin (0 + 2), u j i = v j i} : Finset (Fin 1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    have hh : ∀ j : Fin (0 + 2), u j i = v j i := (Finset.mem_filter.mp hi).2
    have := hh 0
    have hi' : i = 0 := Subsingleton.elim _ _
    subst hi'
    rw [h0] at this
    simp [u] at this
  rw [hempty] at hmu
  simp [mu_set] at hmu
  norm_num at hmu

end ProximityGap.WeightedAgreement.Degenerate
