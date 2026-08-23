/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Sequential composition with an empty trailing protocol

This file discharges the prover-run residual `Prover.appendRunRightResidual` for the case where the
*second* protocol `pSpec₂` is empty (`ProtocolSpec 0`), giving an unconditional run-factoring
theorem `Prover.append_run_empty`. It is the `n = 0` analogue of `Prover.append_run_msg` (which
handles a message-first non-empty second phase).

Unlike the general arbitrary-`n` case, the empty trailing block is genuinely simple: the right-block
continuation `continueFromTo ⟨m⟩ (last m)` collapses to `pure` (`Prover.continueFromTo_self`), the
left block is the proven seam run (`Prover.append_runToRound_seam`, which holds for all `n`), and the
appended prover's `output` reduces to `P₁.output >>= P₂.input >>= P₂.output`
(`Prover.append_output_empty`). The appended run then factors as `P₁.run` followed by `P₂.run` with
the unique empty trailing transcript.

This is the completeness-side keystone (`Prover.append_run`) for any sequential composition whose
trailing phase performs no message/challenge rounds — e.g. a transparent (local-check) opening phase
in the BCS compiler, see `ArkLib.CommitmentScheme.Transparent`.
-/

open OracleSpec OracleComp ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

/-- For an empty trailing protocol, the appended prover's state type at the last round equals `P₁`'s
last-round state type. -/
theorem append_PrvState_last_empty :
    (P₁.append P₂).PrvState (Fin.last (m + 0)) = P₁.PrvState (Fin.last m) := by
  have h := append_PrvState_castLE (P₁ := P₁) (P₂ := P₂) (Fin.last m)
  rwa [show ((Fin.last m).castLE (by omega) : Fin (m + 0 + 1)) = Fin.last (m + 0) from by
    ext; simp] at h

/-- For an empty trailing protocol, the appended-protocol transcript type at the last round equals
`pSpec₁`'s. -/
theorem append_Transcript_last_empty :
    (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + 0)) = pSpec₁.Transcript (Fin.last m) := by
  have h := append_Transcript_castLE (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (Fin.last m)
  rwa [show ((Fin.last m).castLE (by omega) : Fin (m + 0 + 1)) = Fin.last (m + 0) from by
    ext; simp] at h

/-- The appended prover's `output` for an empty trailing protocol: run `P₁`'s output, feed it to
`P₂`'s input, then `P₂`'s output. -/
theorem append_output_empty (state : (P₁.append P₂).PrvState (Fin.last (m + 0))) :
    (P₁.append P₂).output state
      = (do
          let ctx ← P₁.output (cast (append_PrvState_last_empty P₁ P₂) state)
          P₂.output (P₂.input ctx)) := by
  show (P₁.append P₂).output state = _
  unfold Prover.append
  simp only [Nat.add_zero, dif_pos]
  rfl

/-- Running a prover over the empty protocol: with no rounds it just maps input through output,
returning the unique empty transcript. -/
theorem run_empty (s : Stmt₂) (w : Wit₂) :
    P₂.run s w
      = (do
          let ctx ← P₂.output (P₂.input (s, w))
          return ((default : pSpec₂.FullTranscript), ctx)) := by
  rw [run_eq_runToRound_last]
  simp only [Prover.runToRound]
  have h_last_eq_zero : (Fin.last 0) = (0 : Fin 1) := rfl
  rw! (castMode := .all) [h_last_eq_zero]
  simp only [Fin.induction_zero, pure_bind]
  rfl

/-- **The `n = 0` discharge of `Prover.appendRunRightResidual`.** When the trailing protocol is
empty, the right-block continuation collapses (`continueFromTo_self`), the left block is the seam
run (`append_runToRound_seam`), and the output is the empty-append branch (`append_output_empty`); the
appended run then matches `P₁.run >>= P₂.run` with the empty trailing transcript. The analogue of
`Prover.appendRunRightResidual_holds_msg` for `n = 0`. -/
theorem appendRunRightResidual_holds_empty (stmt : Stmt₁) (wit : Wit₁) :
    appendRunRightResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  unfold appendRunRightResidual
  have hcollapse :
      (Prover.runToRound (⟨m, by omega⟩ : Fin (m + 0 + 1)) stmt wit (P₁.append P₂) >>=
        (P₁.append P₂).continueFromTo stmt wit (⟨m, by omega⟩ : Fin (m + 0 + 1)) (Fin.last (m + 0)))
      = Prover.runToRound (⟨m, by omega⟩ : Fin (m + 0 + 1)) stmt wit (P₁.append P₂) := by
    have hcont : (P₁.append P₂).continueFromTo stmt wit (⟨m, by omega⟩ : Fin (m + 0 + 1))
        (Fin.last (m + 0)) = pure := by
      funext rk; exact continueFromTo_self _ _ _ _ rk
    rw [hcont]
    exact bind_pure _
  simp only [hcollapse, run_eq_runToRound_last (prover := P₁), run_empty, append_output_empty,
    liftM_bind, bind_assoc, liftM_pure, pure_bind]
  apply eq_of_heq
  have hseam := append_runToRound_seam (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit)
  refine bind_heq_congr
    (by rw [append_Transcript_last_empty, append_PrvState_last_empty]) rfl hseam
    (fun rSeam x hr => ?_)
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_last_empty (pSpec₂ := pSpec₂))
    (append_PrvState_last_empty P₁ P₂) hr
  have hc2 : cast (append_PrvState_last_empty P₁ P₂) rSeam.2 = x.2 :=
    eq_of_heq ((cast_heq _ _).trans hs)
  rw [hc2]
  apply heq_of_eq
  have htr : rSeam.1 = x.1 ++ₜ (default : pSpec₂.FullTranscript) := by
    have hempty : (x.1 ++ₜ (default : pSpec₂.FullTranscript)) ≍ x.1 := by
      rw [← Transcript.appendRight_full]
      exact Transcript.appendRight_empty x.1
    exact eq_of_heq (ht.trans hempty.symm)
  rw [htr]
  simp only [← OracleComp.liftComp_eq_liftM, Prod.mk.eta]
  rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]
  refine bind_congr fun x_1 => ?_
  rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]
  rfl

/-- **Sequential-composition prover run for an empty trailing protocol (UNCONDITIONAL).** Running
the appended prover `P₁.append P₂` when `pSpec₂` is empty is exactly running `P₁` then `P₂` and
concatenating transcripts (the second being the unique empty transcript) — no residual hypothesis
required. The `n = 0` analogue of `Prover.append_run_msg`. -/
theorem append_run_empty (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂).run stmt wit = (do
      let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
      let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
      return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :=
  append_run stmt wit (appendRunRightResidual_holds_empty P₁ P₂ stmt wit)

end Prover
