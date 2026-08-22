/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.ProtocolSpec.TranscriptRecompose

/-!
# Partial `appendRight` transcript projections (phase-2 reconcile bricks)

The phase-1 partial-transcript bricks `transcript_fst_heq` / `concat_fst_heq_phase2` /
`concat_snd_heq_phase2` (in `AppendRbrKnowledgeStateFunction.lean`) project an appended-spec partial
transcript `tr : (pSpec₁ ++ₚ pSpec₂).Transcript k` into its `pSpec₁` / `pSpec₂` halves.  This file
provides the *mirror* bricks that the phase-2 seam reconcile
(`appendRbrKnowledgePhase2SeamReconcile`) needs: the partial-transcript `.fst` / `.snd` projections of
an `appendRight T₁ T₂` transcript, where `T₁ : FullTranscript pSpec₁` is a *full* phase-1 transcript
and `T₂ : pSpec₂.Transcript k` is a *partial* phase-2 transcript.

`TranscriptRecompose.lean` already supplies the **full** variants `appendRight_full_fst` /
`appendRight_full_snd` (both halves complete).  Here we supply the **partial** variants:

* `appendRight_fst` — `(appendRight T₁ T₂).fst ≍ T₁`.  When the appended round index `m + k.val ≥ m`,
  the phase-1 truncation `.fst` recovers the *whole* phase-1 prefix `T₁` (heterogeneously, since the
  truncated index type is `min (m + k.val) m = m`).
* `appendRight_snd` — `(appendRight T₁ T₂).snd ≍ T₂`.  The phase-2 tail `.snd` recovers the partial
  phase-2 transcript `T₂` (heterogeneously, since the tail index type is `(m + k.val) - m = k.val`).
* `appendRight_concat_fst` — at a phase-2 round, `((appendRight T₁ T₂).concat msg).fst ≍ T₁`: a
  phase-2 message leaves the phase-1 prefix untouched.
* `appendRight_concat_snd` — `((appendRight T₁ T₂).concat msg).snd ≍ T₂.concat (recast msg)`: the
  phase-2 tail of a concat'd `appendRight` picks up the new message.

These are exactly the projections consumed by `appendExtractMid_gt` /
`KnowledgeStateFunction.append_toFun_gt` (the `htrf : tr.fst ≍ trf`, `htrs : tr.snd ≍ trs`
hypotheses) under the `appendRight ctx.1` transcript prefix of the phase-2 reconcile.
-/

open ProtocolSpec

namespace ProtocolSpec.Transcript

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **`Transcript.fst` respects heterogeneous transcript equality.**  Two appended-spec partial
transcripts at index-equal rounds that are heterogeneously equal have heterogeneously-equal phase-1
truncations.  The dependent congruence glue for the `appendRight` `.fst` projections. -/
theorem fst_heq_of_heq {k₁ k₂ : Fin (m + n + 1)} (hk : (k₁ : ℕ) = (k₂ : ℕ))
    {T₁ : (pSpec₁ ++ₚ pSpec₂).Transcript k₁} {T₂ : (pSpec₁ ++ₚ pSpec₂).Transcript k₂}
    (hT : HEq T₁ T₂) : HEq (Transcript.fst T₁) (Transcript.fst T₂) := by
  have hkeq : k₁ = k₂ := Fin.ext hk
  subst hkeq
  rw [eq_of_heq hT]

/-- **`Transcript.snd` respects heterogeneous transcript equality.**  The `.snd` analogue of
`fst_heq_of_heq`. -/
theorem snd_heq_of_heq {k₁ k₂ : Fin (m + n + 1)} (hk : (k₁ : ℕ) = (k₂ : ℕ))
    {T₁ : (pSpec₁ ++ₚ pSpec₂).Transcript k₁} {T₂ : (pSpec₁ ++ₚ pSpec₂).Transcript k₂}
    (hT : HEq T₁ T₂) : HEq (Transcript.snd T₁) (Transcript.snd T₂) := by
  have hkeq : k₁ = k₂ := Fin.ext hk
  subst hkeq
  rw [eq_of_heq hT]

/-- **Phase-1 projection of a partial `appendRight`.**  Projecting `appendRight T₁ T₂` (a full
phase-1 transcript `T₁` prefixed onto a *partial* phase-2 transcript `T₂` at round `k`) onto its
phase-1 truncation `.fst` recovers the whole phase-1 prefix `T₁`, heterogeneously: the truncated
index type is `min (m + k.val) m = m`, so `.fst` is a full `pSpec₁` transcript again.  The partial
analogue of `appendRight_full_fst`. -/
theorem appendRight_fst (T₁ : FullTranscript pSpec₁) {k : Fin (n + 1)}
    (T₂ : pSpec₂.Transcript k) :
    HEq (Transcript.fst (appendRight T₁ T₂)) T₁ := by
  refine Function.hfunext ?_ ?_
  · congr 1
    dsimp only [Fin.val_mk]; omega
  · intro i j hij
    have hcard : min (m + k.val) m = m := by omega
    have hv : (i : ℕ) = (j : ℕ) := (Fin.heq_ext_iff (by dsimp only [Fin.val_mk]; omega)).mp hij
    -- `i : Fin (min (m + k.val) m)`, so `i.val < m`.
    have hilt : (i : ℕ) < m := by have := i.isLt; simp only [hcard] at this; exact this
    simp only [Transcript.fst, appendRight]
    rw [dif_pos (show (⟨i.val, by omega⟩ : Fin (m + k.val)).val < m from hilt)]
    refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
    rw [show (⟨i.val, by omega⟩ : Fin m) = j from by ext; exact hv]

/-- **Phase-2 projection of a partial `appendRight`.**  Projecting `appendRight T₁ T₂` onto its
phase-2 tail `.snd` recovers the partial phase-2 transcript `T₂`, heterogeneously: the tail index
type is `(m + k.val) - m = k.val`.  The partial analogue of `appendRight_full_snd`. -/
theorem appendRight_snd (T₁ : FullTranscript pSpec₁) {k : Fin (n + 1)}
    (T₂ : pSpec₂.Transcript k) :
    HEq (Transcript.snd (appendRight T₁ T₂)) T₂ := by
  refine Function.hfunext ?_ ?_
  · congr 1
    dsimp only [Fin.val_mk]; omega
  · intro i j hij
    have hv : (i : ℕ) = (j : ℕ) := (Fin.heq_ext_iff (by dsimp only [Fin.val_mk]; omega)).mp hij
    have hjlt : (j : ℕ) < k.val := j.isLt
    simp only [Transcript.snd]
    -- `.snd` lands in the `else` branch since the appended index `m + k.val > m` (as `k.val ≥ 1`
    -- whenever there is any tail position `j`).
    rw [dif_neg (show ¬ (⟨m + k.val, by omega⟩ : Fin (m + n + 1)) ≤ m from by
      dsimp only []; omega)]
    simp only [appendRight]
    rw [dif_neg (show ¬ (⟨m + i.val, by omega⟩ : Fin (m + k.val)).val < m from by
      dsimp only [Fin.val_mk]; omega)]
    refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
    congr 1
    ext
    dsimp only [Fin.val_mk]
    omega

/-- **Phase-1 prefix is invariant under a phase-2 concat of a partial `appendRight`.**  At a phase-2
round `natAdd m j` (with the partial `appendRight T₁ T₂` at round `j.castSucc`), concatenating a
phase-2 message leaves the phase-1 truncation `.fst` unchanged — it still recovers the whole phase-1
prefix `T₁`.  Combines `appendRight_concat` with `appendRight_fst` (the `concat_fst_heq_phase2`
analogue, prefixed by `appendRight`). -/
theorem appendRight_concat_fst (T₁ : FullTranscript pSpec₁) {j : Fin n}
    (msg : pSpec₂.«Type» j) (T₂ : pSpec₂.Transcript j.castSucc) :
    HEq (Transcript.fst (Transcript.concat (m := Fin.natAdd m j)
          (cast (append_Type_natAdd j).symm msg) (appendRight T₁ T₂))) T₁ := by
  -- The concat'd `appendRight` is (heterogeneously) `appendRight T₁ (T₂.concat msg)` by
  -- `appendRight_concat`; its `.fst` recovers `T₁` by `appendRight_fst`.
  have hrw : HEq
      (Transcript.fst (appendRight T₁ (Transcript.concat msg T₂)))
      (Transcript.fst (Transcript.concat (m := Fin.natAdd m j)
        (cast (append_Type_natAdd j).symm msg) (appendRight T₁ T₂))) := by
    refine fst_heq_of_heq ?_ ?_
    · dsimp only [Fin.val_mk, Fin.val_succ, Fin.val_natAdd]; omega
    · exact appendRight_concat T₁ msg T₂
  exact hrw.symm.trans (appendRight_fst T₁ (Transcript.concat msg T₂))

/-- **Phase-2 tail of a concat'd partial `appendRight`.**  At a phase-2 round `natAdd m j`,
concatenating a phase-2 message onto `appendRight T₁ T₂` and taking the phase-2 tail `.snd` is
heterogeneously equal to first taking the tail (which recovers `T₂`) and then concatenating the
message: `T₂.concat msg`.  The `concat_snd_heq_phase2` analogue prefixed by `appendRight`. -/
theorem appendRight_concat_snd (T₁ : FullTranscript pSpec₁) {j : Fin n}
    (msg : pSpec₂.«Type» j) (T₂ : pSpec₂.Transcript j.castSucc) :
    HEq (Transcript.snd (Transcript.concat (m := Fin.natAdd m j)
          (cast (append_Type_natAdd j).symm msg) (appendRight T₁ T₂)))
        (Transcript.concat msg T₂) := by
  have hrw : HEq
      (Transcript.snd (appendRight T₁ (Transcript.concat msg T₂)))
      (Transcript.snd (Transcript.concat (m := Fin.natAdd m j)
        (cast (append_Type_natAdd j).symm msg) (appendRight T₁ T₂))) := by
    refine snd_heq_of_heq ?_ ?_
    · dsimp only [Fin.val_mk, Fin.val_succ, Fin.val_natAdd]; omega
    · exact appendRight_concat T₁ msg T₂
  exact hrw.symm.trans (appendRight_snd T₁ (Transcript.concat msg T₂))

end ProtocolSpec.Transcript

#print axioms ProtocolSpec.Transcript.appendRight_fst
#print axioms ProtocolSpec.Transcript.appendRight_snd
#print axioms ProtocolSpec.Transcript.appendRight_concat_fst
#print axioms ProtocolSpec.Transcript.appendRight_concat_snd
