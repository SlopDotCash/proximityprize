/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Incremental soundness helper lemmas

Helper lemmas for `ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental`.

This file provides:
* `iterated_fold_first` — the "peel first step" analogue of `iterated_fold_last`: folding
  `steps + 1` times starting at level `i` with challenges `Fin.cons r_new rest` equals folding
  `steps` times starting at level `midIdx = i + 1` of the single-step fold `fold(f, r_new)`.
* `fiberwiseClose_implies_UDRClose` — the close-branch hypothesis carries the ordinary source
  UDR closeness fact needed by codeword extraction.
-/

set_option maxHeartbeats 1000000

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- **Peel the first step (new-API).** Folding `steps + 1` times starting at level `i` with
challenges `Fin.cons r_new rest` equals folding `steps` times starting at level `midIdx = i + 1`
of the single-step fold `fold(f, r_new)` (with challenges `rest`).

Proved by induction on `steps`, peeling the *last* step on both sides with `iterated_fold_last`. -/
theorem iterated_fold_first (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin (steps + 1) → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps + 1)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := r_challenges) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := steps)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := midIdx)
        (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
        (r_chal := r_challenges 0))
      (r_challenges := fun j => r_challenges j.succ) := by
  -- `midIdx` is determined by `i` (both have `.val = i.val + 1` once `steps = 0`); we keep it as a
  -- parameter so the recursion lines up. Reduce to the canonical `⟨i+1,_⟩` index up front.
  induction steps generalizing destIdx midIdx with
  | zero =>
    -- `destIdx = midIdx` (both have val `i + 1`); substitute so both `fold`s share an index.
    have h_dm : destIdx = midIdx := Fin.ext (by omega)
    subst h_dm
    -- `iterated_fold (i) 1 (cons r_new ![])` = `fold(iterated_fold(i) 0 (init …), last)`.
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
      (midIdx := i) (destIdx := destIdx)
      (h_midIdx := by omega) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) f r_challenges]
    -- RHS: `iterated_fold (destIdx) 0 (fold f r_challenges 0)` is the `0`-step identity = `fold f …`.
    funext y
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)]
    -- LHS: the inner `iterated_fold (i) 0 (init r_challenges)` is also the `0`-step identity = `f`.
    rw [show (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
        (destIdx := i) (by omega) (by omega) f (Fin.init r_challenges)) = f from by
      funext z
      rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (h_destIdx := rfl) (h_destIdx_le := by omega)]
      rfl]
    -- both sides are `fold i (destIdx) f (r_challenges 0) y` (last 0 = 0, point transports trivially)
    simp only [Fin.last_zero]
    rfl
  | succ n ih =>
    -- expose `.val` facts for `omega`
    have hd : destIdx.val = i.val + (n + 1 + 1) := h_destIdx
    have hm : midIdx.val = i.val + 1 := h_midIdx
    -- bounds for the intermediate `Fin r` indices appearing below
    have h_mid_bound : i.val + (n + 1) < r := by
      have : destIdx.val < r := destIdx.isLt; omega
    have h_midmid_bound : midIdx.val + n < r := by
      have : destIdx.val < r := destIdx.isLt; omega
    -- Peel the last step on the LHS, using the *shared* `midIdx := ⟨midIdx+n,_⟩` index.
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := n + 1)
      (midIdx := ⟨midIdx.val + n, h_midmid_bound⟩) (destIdx := destIdx)
      (h_midIdx := show midIdx.val + n = i.val + (n + 1) by omega)
      (h_destIdx := hd) (h_destIdx_le := h_destIdx_le)
      f r_challenges]
    -- Peel the last step on the RHS (same shared `midIdx` index).
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := n)
      (midIdx := ⟨midIdx.val + n, h_midmid_bound⟩) (destIdx := destIdx)
      (h_midIdx := rfl) (h_destIdx := show destIdx.val = midIdx.val + n + 1 by omega)
      (h_destIdx_le := h_destIdx_le)]
    -- The two inner `n`-step folds are related by the inductive hypothesis `ih`. Use the *shared*
    -- destination index `⟨midIdx+n,_⟩` so the IH LHS matches the goal's peeled inner fold exactly.
    have h_ih := ih (destIdx := ⟨midIdx.val + n, h_midmid_bound⟩) (midIdx := midIdx)
      (h_midIdx := h_midIdx)
      (h_destIdx := show midIdx.val + n = i.val + (n + 1) by omega)
      (h_destIdx_le := show (⟨midIdx.val + n, h_midmid_bound⟩ : Fin r) ≤ ℓ by
        show midIdx.val + n ≤ ℓ; omega)
      (r_challenges := Fin.init r_challenges)
    -- Both outer `fold`s now share the same start index; the last challenges agree by `succ_last`,
    -- and the inner `n`-step folds agree by the IH (via `congr`, which closes the residual by IH/defeq).
    rw [Fin.succ_last]
    congr 1
    all_goals first | exact h_ih | rfl

/-- The close-branch hypothesis carries ordinary source UDR closeness. -/
lemma fiberwiseClose_implies_UDRClose
    (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps]
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f →
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f := by
  intro hclose
  exact UDRClose_of_fiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f hclose

end

end Binius.BinaryBasefold
