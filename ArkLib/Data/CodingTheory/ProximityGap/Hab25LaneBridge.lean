/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AlgebraicBridge

/-!
# The lane bridge — bad scalars inject into the close-proximity index

The §5 list-decoding lane indexes its per-place data by
`coeffs_of_close_proximity k ωs δ u₀ u₁` (scalars whose fold is `δ`-close to
`RS[ωs, k+1]` in relative Hamming distance), while the Johnson endgame's cells carry
`hab25McaBadScalars` (the `mcaEvent` filter).  This file proves the translation:
**every bad scalar is close** — the `mcaEvent` witness set of size `≥ (1-δ)·n` with exact
agreement bounds the relative distance by `δ`.  Consequently the lane's per-`z` machinery
(`Pz`, matching sets, weld nodes) restricts to every Johnson cell.

Degree convention: the lane's `RS[ωs, k+1]` (degree `≤ k`) is the endgame's
`ReedSolomon.code ωs (k+1)` (degree `< k+1`) — same code, parameter shifted by one.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open _root_.ProximityGap Code
open scoped NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [DecidableEq (RatFunc F)]

open Classical in
/-- **Bad scalars are close.**  Every `mcaEvent`-bad scalar of the degree-`(k+1)` code
lies in the lane's close-proximity index at any rational radius dominating `δ`. -/
theorem hab25McaBadScalars_subset_coeffs_of_close_proximity
    {n k : ℕ} [NeZero n] (ωs : Fin n ↪ F) (δ : ℝ≥0) (δq : ℚ)
    (hδ : (δ : ℝ) ≤ (δq : ℝ))
    (u : WordStack F (Fin 2) (Fin n)) :
    hab25McaBadScalars ωs (k + 1) δ u
      ⊆ _root_.ProximityGap.coeffs_of_close_proximity
          (F := F) k ωs δq (u 0) (u 1) := by
  intro γ hγ
  rw [hab25McaBadScalars, Finset.mem_filter] at hγ
  obtain ⟨-, S, hScard, ⟨w, hwC, hwagree⟩, -⟩ := hγ
  rw [_root_.ProximityGap.coeffs_of_close_proximity, Set.mem_toFinset, Set.mem_setOf_eq]
  refine ⟨⟨w, hwC⟩, ?_⟩
  -- the disagreement set lies outside `S`
  have hdis : Finset.univ.filter (fun i => (u 0 + γ • u 1) i ≠ w i) ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_compl]
    intro hiS
    have := hwagree i hiS
    simp only [Finset.mem_filter, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    exact hi.2 (by rw [this]; ring)
  -- count: `|disagree| ≤ n - |S| ≤ δ·n`
  have hcount : (Finset.univ.filter (fun i => (u 0 + γ • u 1) i ≠ w i)).card
      ≤ Fintype.card (Fin n) - S.card := by
    calc (Finset.univ.filter (fun i => (u 0 + γ • u 1) i ≠ w i)).card
        ≤ Sᶜ.card := Finset.card_le_card hdis
      _ = Fintype.card (Fin n) - S.card := Finset.card_compl S
  -- relative distance ≤ δ ≤ δq
  have hn0 : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos
    exact_mod_cast this
  have hrel : ((relHammingDist (u 0 + γ • u 1) (w : Fin n → F) : ℚ≥0) : ℝ) ≤ (δ : ℝ) := by
    have hdef : ((relHammingDist (u 0 + γ • u 1) (w : Fin n → F) : ℚ≥0) : ℝ)
        = ((Finset.univ.filter (fun i => (u 0 + γ • u 1) i ≠ w i)).card : ℝ)
          / (Fintype.card (Fin n) : ℝ) := by
      rw [relHammingDist]
      push_cast
      rfl
    rw [hdef, div_le_iff₀ hn0]
    -- `|S| ≥ (1-δ)·n` in `ℝ≥0` gives `n - |S| ≤ δ·n` in `ℝ`
    have hS : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card (Fin n) : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hScard
    have h1δ : (1 : ℝ) - (δ : ℝ) ≤ ((1 - δ : ℝ≥0) : ℝ) := by
      rcases le_total (δ : ℝ≥0) 1 with h | h
      · rw [NNReal.coe_sub h]
        simp
      · have h1 : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
          rw [tsub_eq_zero_of_le h]; rfl
        have h2 : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h
        linarith
    have hSle : S.card ≤ Fintype.card (Fin n) := Finset.card_le_univ S
    have hcount' : ((Finset.univ.filter (fun i => (u 0 + γ • u 1) i ≠ w i)).card : ℝ)
        ≤ (Fintype.card (Fin n) : ℝ) - (S.card : ℝ) := by
      have h := hcount
      have : ((Fintype.card (Fin n) - S.card : ℕ) : ℝ)
          = (Fintype.card (Fin n) : ℝ) - (S.card : ℝ) := by
        push_cast [Nat.cast_sub hSle]
        ring
      rw [← this]
      exact_mod_cast h
    nlinarith [hS, h1δ, hn0]
  -- assemble into the lane's `ℚ` comparison
  have : ((relHammingDist (u 0 + γ • u 1) (w : Fin n → F) : ℚ≥0) : ℝ) ≤ (δq : ℝ) :=
    le_trans hrel hδ
  exact_mod_cast this

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25McaBadScalars_subset_coeffs_of_close_proximity
