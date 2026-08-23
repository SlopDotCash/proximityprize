/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.CheckedVerifier

/-!
# The checked WHIR verifier is input-oblivious: the all-zero fence (#302)

**Finding (formalized here):** every check of `whirCheckingBool` — the initial-phase
anchors/links, the main-round links, and the final zero-sum — reads ONLY prover messages
and challenges; the input oracle is never queried.  Consequently the **all-zero prover
strategy** (every sumcheck/final message the zero vector) passes every check on EVERY
statement and EVERY challenge draw:

* `whirCheckingBool_allZero` — `whirCheckingBool P d (allZeroMsgs P d) chals = true`,
  unconditionally.

**Consequence for the #302 protocol lane (the fence):** genuinely sub-unit per-round rbr
budgets with respect to the δ-far proximity relation are UNACHIEVABLE for
`whirVerifyChecked` as it stands — a malicious prover on ANY δ-far input is accepted with
probability `1` by playing all-zero, so the state function must flip somewhere with total
probability `1` (the budgets must sum to `≥ 1`).  This is the WHIR analogue of the STIR
switch-prover tightness analysis, and it is STRONGER (probability `1`, challenge-free).
The earlier small-field discharges (`whirChecked_rbrKnowledgeSoundness_smallField`) are
consistent with this: their budgets are `≥ 1`.

**The path forward** (mirroring how STIR's #301 milestone was reached): the checked
verifier must be upgraded with **input-binding checks** — oracle queries comparing the
input codeword against the first folded message at challenge-derived points (the analogue
of STIR's round-2 binding check, which is exactly what made `stirEpsStar` sub-unit at
round 2; the wire infrastructure exists in `CheckedFinalBlock`-style landings).  Until
that upgrade lands, any claimed sub-unit rbr discharge for `whirVerifyChecked` against the
proximity relation is FABRICATED — this file is the machine-checked fence.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace Whir302Checked

open WhirIOP WhirIOP.Construction ProtocolSpec

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-- **The all-zero prover messages**: every message slot carries the zero vector. -/
noncomputable def allZeroMsgs (P : Params ιs F) (d : ℕ) :
    ∀ j, ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message j :=
  fun j => Vector.replicate ((whirPaperTranscriptVectorSpec P d).length j.1) (0 : F)

/-- Every oracle answer of the all-zero messages is `0`. -/
theorem msgAns_allZero (P : Params ιs F) (d : ℕ)
    (j : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).MessageIdx)
    (k : Fin ((whirPaperTranscriptVectorSpec P d).length j.1)) :
    msgAns P d (allZeroMsgs P d) j k = 0 := by
  show (Vector.replicate _ (0 : F))[(k : ℕ)] = 0
  rw [Vector.getElem_replicate]

/-- Every full read of the all-zero messages is a constant-zero list. -/
theorem readAns_allZero (P : Params ιs F) (d : ℕ)
    (j : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).MessageIdx) :
    readAns P d (allZeroMsgs P d) j
      = (List.finRange ((whirPaperTranscriptVectorSpec P d).length j.1)).map
          (fun _ => (0 : F)) := by
  unfold readAns
  exact List.map_congr_left (fun k _ => msgAns_allZero P d j k)

/-- **THE FENCE: the all-zero strategy passes every check of the checked WHIR verifier,
on every statement and every challenge draw.**  The verifier never reads the input
oracle, so its decision cannot depend on the proximity statement. -/
theorem whirCheckingBool_allZero (P : Params ιs F) (d : ℕ)
    (chals : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges) :
    whirCheckingBool P d (allZeroMsgs P d) chals = true := by
  unfold whirCheckingBool
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- initial-phase anchors/links
    rintro b ⟨s, -, rfl⟩
    unfold initialStepAns
    rw [readAns_allZero, listEval_map_zero, listEval_map_zero]
    rcases eq_or_ne (s : ℕ) 0 with hs | hs
    · rw [dif_pos hs]
      simp
    · rw [dif_neg hs, readAns_allZero, listEval_map_zero]
      simp
  · -- main-round links
    rintro b ⟨i, -, rfl⟩
    unfold mainRoundAns
    simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq]
    rintro b' ⟨s, -, rfl⟩
    unfold mainStepAns
    rw [readAns_allZero, listEval_map_zero, listEval_map_zero]
    rcases eq_or_ne (s : ℕ) 0 with hs | hs
    · rw [dif_pos hs]
      simp
    · rw [dif_neg hs, readAns_allZero, listEval_map_zero]
      simp
  · -- the final zero-sum check
    rw [readAns_allZero]
    simp [List.sum_map_zero]

end Whir302Checked

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Whir302Checked.whirCheckingBool_allZero
#print axioms Whir302Checked.readAns_allZero
