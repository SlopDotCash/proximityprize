/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-!
# Transcript recomposition for sequentially-composed protocols

The inverse of `FullTranscript.append_fst` / `append_snd`: splitting an appended-protocol full
transcript into its two halves and re-appending recovers the original. Useful for the right-block
run characterization of `Prover.append_run` (reconciling the appended transcript with
`transcript₁ ++ₜ transcript₂`).
-/

open ProtocolSpec

namespace ProtocolSpec.FullTranscript

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Transcript recomposition**: splitting an appended-protocol transcript into its two halves and
re-appending recovers it (inverse of `append_fst` / `append_snd`). -/
theorem fst_append_snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : T.fst ++ₜ T.snd = T := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [append, fst, Fin.happend_left]
  · simp [append, snd, Fin.happend_right]

end ProtocolSpec.FullTranscript

#print axioms ProtocolSpec.FullTranscript.fst_append_snd

namespace ProtocolSpec

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The appended protocol's round `Type` at a right interior round `natAdd m k` is exactly
`pSpec₂`'s round `Type` at `k` (the `Type`-level analogue of `append_dir_natAdd`). -/
theorem append_Type_natAdd (k : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m k) = pSpec₂.«Type» k := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_right]

end ProtocolSpec

namespace ProtocolSpec.Transcript

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Append a full `pSpec₁` transcript and a *partial* `pSpec₂` transcript into a partial transcript
for the concatenated protocol — the right-block analogue of the partial `fst`/`snd` projections,
needed to state the right-block run characterization of `Prover.append_run` (#13). -/
def appendRight (T₁ : FullTranscript pSpec₁) {k : Fin (n + 1)} (T₂ : pSpec₂.Transcript k) :
    (pSpec₁ ++ₚ pSpec₂).Transcript ⟨m + k.val, by omega⟩ :=
  fun i =>
    if hi : i.val < m then
      cast (Fin.vappend_left_of_lt pSpec₁.Type pSpec₂.Type ⟨i.val, by omega⟩ hi).symm
        (T₁ ⟨i.val, hi⟩)
    else
      have hi2 : i.val - m < k.val := by have := i.isLt; simp only [Fin.val_mk] at this; omega
      cast (Fin.vappend_right_of_not_lt pSpec₁.Type pSpec₂.Type ⟨i.val, by omega⟩ hi).symm
        (T₂ ⟨i.val - m, hi2⟩)

/-- **`appendRight` commutes with a final `concat`** (right-block per-round growth): appending a
`pSpec₂`-message-extended transcript equals extending the appended transcript by that message,
recast at the appended round `natAdd m k`. The per-round transcript brick for the right-block run
characterization of `Prover.append_run` (#13). -/
theorem appendRight_concat (T₁ : FullTranscript pSpec₁) {k : Fin n} (msg : pSpec₂.«Type» k)
    (T₂ : pSpec₂.Transcript k.castSucc) :
    HEq (appendRight T₁ (Transcript.concat msg T₂))
        (Transcript.concat (m := Fin.natAdd m k) (cast (append_Type_natAdd k).symm msg)
          (appendRight T₁ T₂)) := by
  refine Function.hfunext ?_ ?_
  · congr 1
  · intro i j hij
    have hv : i.val = j.val := (Fin.heq_ext_iff (by simp [Fin.val_succ]; omega)).mp hij
    simp only [appendRight, Transcript.concat, Fin.snoc]
    have hisz : i.val < m + k.val + 1 := by have h := i.isLt; simp only [Fin.val_succ] at h; omega
    rcases lt_or_ge i.val m with hlt | hge
    · -- `↑i < m`: both pick the left transcript `T₁`
      rw [dif_pos hlt]
      have hj1 : (j : Fin _).val < (Fin.natAdd m k).val := by rw [Fin.val_natAdd]; omega
      rw [dif_pos hj1]
      simp only [Fin.coe_castLT]
      rw [dif_pos (show (j : Fin _).val < m from hv ▸ hlt)]
      refine (cast_heq _ _).trans (HEq.trans ?_ ((cast_heq _ _).trans (cast_heq _ _)).symm)
      rw [show (⟨↑i, hlt⟩ : Fin m) = ⟨↑j, hv ▸ hlt⟩ from by ext; exact hv]
    · rcases lt_or_ge (i.val - m) k.val with hlt2 | hge2
      · -- `m ≤ ↑i < m + ↑k`: both pick a `T₂` round
        rw [dif_neg (by omega), dif_pos hlt2]
        have hj1 : (j : Fin _).val < (Fin.natAdd m k).val := by rw [Fin.val_natAdd]; omega
        rw [dif_pos hj1]
        simp only [Fin.coe_castLT]
        rw [dif_neg (show ¬ (j : Fin _).val < m by omega)]
        refine ((cast_heq _ _).trans (cast_heq _ _)).trans
          (HEq.trans ?_ ((cast_heq _ _).trans (cast_heq _ _)).symm)
        congr 1
        ext
        simp [Fin.coe_castLT]
        omega
      · -- `↑i = m + ↑k`: both pick the appended message `msg`
        have hik : i.val - m = k.val := by omega
        rw [dif_neg (by omega), dif_neg (by omega)]
        have hj0 : ¬ (j : Fin _).val < (Fin.natAdd m k).val := by rw [Fin.val_natAdd]; omega
        rw [dif_neg hj0]
        exact ((cast_heq _ _).trans (cast_heq _ _)).trans
          (((cast_heq _ _).trans (cast_heq _ _)).symm)

/-- **`appendRight` of the empty `pSpec₂` transcript** is just `T₁` (heterogeneously): the base of
the right-block recursion, where no `pSpec₂` rounds have run yet. -/
theorem appendRight_empty (T₁ : FullTranscript pSpec₁) :
    HEq (appendRight T₁ (default : pSpec₂.Transcript (0 : Fin (n + 1)))) T₁ := by
  refine Function.hfunext ?_ ?_
  · congr 1
  · intro i j hij
    have hv : i.val = j.val := (Fin.heq_ext_iff (by simp)).mp hij
    simp only [appendRight]
    rw [dif_pos (show i.val < m from by have := i.isLt; simp at this; omega)]
    refine (cast_heq _ _).trans ?_
    rw [show (⟨i.val, by have := i.isLt; simp at this; omega⟩ : Fin m) = j from by ext; exact hv]

/-- **`appendRight` of two FULL transcripts equals `FullTranscript.append` (`++ₜ`).**  The final
transcript reconciliation for the right-block run characterization: when both halves are complete,
`appendRight` coincides with the standard transcript append. -/
theorem appendRight_full (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    appendRight (k := Fin.last n) T₁ T₂ = T₁ ++ₜ T₂ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [appendRight, FullTranscript.append, Fin.happend_left, Fin.coe_castAdd, Fin.val_last]
    split
    · apply eq_of_heq
      refine (cast_heq _ _).trans (HEq.trans ?_ (cast_heq _ _).symm)
      rw [show (⟨(j : ℕ), by omega⟩ : Fin m) = j from by ext; rfl]
    · omega
  · simp only [appendRight, FullTranscript.append, Fin.happend_right, Fin.val_natAdd, Fin.val_last]
    split
    · omega
    · apply eq_of_heq
      refine (cast_heq _ _).trans (HEq.trans ?_ (cast_heq _ _).symm)
      rw [show (⟨m + (j : ℕ) - m, by omega⟩ : Fin n) = j from by ext; simp]

/-- Recompose a full appended transcript directly through `appendRight`: splitting into
`FullTranscript.fst`/`snd` and then rebuilding with `appendRight` recovers the original transcript.
This is the right-block transcript reconciliation corollary used by append-run proofs. -/
theorem appendRight_fst_snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) :
    appendRight (k := Fin.last n) T.fst T.snd = T := by
  rw [appendRight_full]
  exact FullTranscript.fst_append_snd T

/-- **First-half projection of a full `appendRight`.**  Projecting the appended full transcript back
to its `pSpec₁` half recovers `T₁`. The inverse of `appendRight_fst_snd` on the left component. -/
theorem appendRight_full_fst (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (show FullTranscript (pSpec₁ ++ₚ pSpec₂) from appendRight (k := Fin.last n) T₁ T₂).fst = T₁ := by
  rw [show (show FullTranscript (pSpec₁ ++ₚ pSpec₂) from appendRight (k := Fin.last n) T₁ T₂)
        = T₁ ++ₜ T₂ from appendRight_full T₁ T₂]
  exact FullTranscript.append_fst T₁ T₂

/-- **Second-half projection of a full `appendRight`.**  Projecting the appended full transcript back
to its `pSpec₂` half recovers `T₂`. The inverse of `appendRight_fst_snd` on the right component. -/
theorem appendRight_full_snd (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (show FullTranscript (pSpec₁ ++ₚ pSpec₂) from appendRight (k := Fin.last n) T₁ T₂).snd = T₂ := by
  rw [show (show FullTranscript (pSpec₁ ++ₚ pSpec₂) from appendRight (k := Fin.last n) T₁ T₂)
        = T₁ ++ₜ T₂ from appendRight_full T₁ T₂]
  exact FullTranscript.append_snd T₁ T₂

end ProtocolSpec.Transcript

#check @ProtocolSpec.Transcript.appendRight
#print axioms ProtocolSpec.Transcript.appendRight_concat
#print axioms ProtocolSpec.Transcript.appendRight_empty
#print axioms ProtocolSpec.Transcript.appendRight_full
#print axioms ProtocolSpec.Transcript.appendRight_fst_snd
