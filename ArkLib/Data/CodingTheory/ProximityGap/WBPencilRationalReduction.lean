/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilBound
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilSymmetry

/-!
# Theorem WB-2: the rational-pair reduction (#371)

**Below the unique-decoding radius, the MCA supremum is carried by doubly-rational
stacks.**  Combining the pencil bound (WB-1), the absorption lemma, and the
γ-inversion symmetry: every stack with at least one WB-far row has bad-scalar count
≤ `w + 3`, so

  `ε_mca(RS, δ) ≤ max( (w+3)/q ,  sup over stacks with BOTH rows WB-solvable )`

for every radius `δ ≤ w/n`.  The exceptional family — both rows of rational form
`R/ℓ` with `deg ℓ ≤ w`, `deg R ≤ w+k−1` — is exactly where the known ceiling
constructions live (the adjacent-pair stacks are rational pairs), and is now the
PROVEN location of the below-UDR adversary.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Every MCA-bad scalar of a line is WB-solvable for that line (size-cast form of
the absorption lemma): at radius `δ ≤ w/n` a witness has `≥ n − w` points. -/
theorem mcaEvent_implies_wbSolvable (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) (hw : w ≤ n)
    {u₀ u₁ : Fin n → F} {γ : F}
    (h : mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) :
    WBSolvable dom k w (fun i => u₀ i + γ * u₁ i) := by
  obtain ⟨S, hsz, ⟨c, hc, hag⟩, -⟩ := h
  refine wbSolvable_of_explainable dom hk hw ⟨S, ?_, c, hc, ?_⟩
  · -- (1−δ)·n ≥ n − w, then uncast
    have h1 : ((n - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      have hnw : ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by
        rw [Nat.cast_tsub]
      have hδ1 : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)
          = (Fintype.card (Fin n) : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
        rw [tsub_mul, one_mul]
      have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
        rw [Fintype.card_fin]
      calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := hnw
        _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
            exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
        _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
            rw [hδ1, hcardn]
        _ ≤ (S.card : ℝ≥0) := hsz
    exact_mod_cast h1
  · intro i hi
    have := hag i hi
    simpa [smul_eq_mul] using this

open Classical in
/-- The per-stack bound when the direction row is WB-far: bad count ≤ `w + 2`. -/
theorem badScalars_card_le_of_far_snd (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} (hfar : ¬ WBSolvable dom k w u₁) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ w + 2 := by
  have hw : w ≤ n := by omega
  refine le_trans (Finset.card_le_card (t := Finset.univ.filter (fun γ : F =>
      WBSolvable dom k w (fun i => u₀ i + γ * u₁ i))) ?_)
    (wbSolvable_line_card_le dom hk hwk (u₀ := u₀) hfar)
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, mcaEvent_implies_wbSolvable dom hk hδn hw hγ.2⟩

open Classical in
/-- **THEOREM WB-2 (the rational-pair reduction).**  Below the unique-decoding
radius, the MCA error is at most the larger of `(w+3)/q` and the supremum over
**doubly-WB-solvable** (rational-pair) stacks: the below-UDR adversary provably
lives in the rational-pair family. -/
theorem epsMCA_le_max_doublyRational (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ max (((w + 3 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
          (⨆ u : {u : Code.WordStack F (Fin 2) (Fin n) //
              WBSolvable dom k w (u 0) ∧ WBSolvable dom k w (u 1)},
            Pr_{let γ ← $ᵖ F}[mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
              ((u.1) 0) ((u.1) 1) γ]) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  by_cases h1 : WBSolvable dom k w (u 1)
  · by_cases h0 : WBSolvable dom k w (u 0)
    · -- doubly rational: absorbed into the sup
      refine le_trans ?_ (le_max_right _ _)
      exact le_iSup (fun v : {u : Code.WordStack F (Fin 2) (Fin n) //
        WBSolvable dom k w (u 0) ∧ WBSolvable dom k w (u 1)} =>
          Pr_{let γ ← $ᵖ F}[mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            ((v.1) 0) ((v.1) 1) γ]) ⟨u, h0, h1⟩
    · -- first row far: swap + pencil bound, ≤ (w+2) + 1
      refine le_trans ?_ (le_max_left _ _)
      rw [prob_uniform_eq_card_filter_div_card]
      refine ENNReal.div_le_div_right ?_ _
      have hswap := badScalars_card_swap_le
        (rsCode dom k : Submodule F (Fin n → F)) δ (u 0) (u 1)
      have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
        (u₀ := u 1) (u₁ := u 0) h0
      exact_mod_cast le_trans hswap (by omega)
  · -- second row far: the pencil bound directly, ≤ w + 2 ≤ w + 3
    refine le_trans ?_ (le_max_left _ _)
    rw [prob_uniform_eq_card_filter_div_card]
    refine ENNReal.div_le_div_right ?_ _
    have := badScalars_card_le_of_far_snd dom hk hwk hδn
      (u₀ := u 0) (u₁ := u 1) h1
    exact_mod_cast le_trans this (by omega)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.mcaEvent_implies_wbSolvable
#print axioms ProximityGap.WBPencil.badScalars_card_le_of_far_snd
#print axioms ProximityGap.WBPencil.epsMCA_le_max_doublyRational
