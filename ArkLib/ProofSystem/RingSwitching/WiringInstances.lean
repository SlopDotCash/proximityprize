/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness

/-!
# Wiring instances for the RingSwitching rbr knowledge-soundness chain (issue #29)

The rbr knowledge-soundness append keystones
(`OracleVerifier.append_rbrKnowledgeSoundness_subsingleton`,
`OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton`) consume, per seam:

* `Inhabited`/`Nonempty` witnesses for the intermediate statement/witness packs, and
* the message-seam direction facts `hDir`/`hDir₂` (the right phase opens with a `P_to_V` message,
  both in its own indexing and inside the appended protocol's indexing).

This file supplies all of them for the RingSwitching protocol stack. The statement-side
`Inhabited` instances are built from `0` (every carrier is a ring or a function/polynomial over
one); the oracle-statement pack `∀ j, aOStmtIn.OStmtIn j` is *abstract* and stays a hypothesis at
the wiring level. The direction facts are proven by the `Fin.natAdd`/`Fin.castLE` reindexing
pattern already used by the completeness seams (`General.lean`), made public and keystone-shaped
here.
-/

namespace RingSwitching

noncomputable section
open OracleSpec OracleComp ProtocolSpec
open Sumcheck.Structured

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

/-! ## `Inhabited` instances for the intermediate statement/witness packs -/

/-- The MLIOPCS input statement is inhabited (zero evaluation point and claim). -/
instance instInhabitedMLPEvalStatement : Inhabited (MLPEvalStatement L ℓ) :=
  ⟨{ t_eval_point := fun _ => 0, original_claim := 0 }⟩

/-- The batching input statement is inhabited (zero evaluation point and claim). -/
instance instInhabitedBatchingStmtIn : Inhabited (BatchingStmtIn L ℓ) :=
  ⟨{ t_eval_point := fun _ => 0, original_claim := 0 }⟩

/-- The MLIOPCS witness is inhabited (the zero multilinear polynomial). -/
instance instInhabitedWitMLP : Inhabited (WitMLP K ℓ) := ⟨{ t := 0 }⟩

/-- The ring-switching sumcheck context is inhabited (zero context; `P.A` is a `CommRing`). -/
instance instInhabitedRingSwitchingBaseContext :
    Inhabited (RingSwitchingBaseContext κ L K ℓ P) :=
  ⟨{ t_eval_point := fun _ => 0, original_claim := 0, s_hat := 0, r_batching := fun _ => 0 }⟩

/-- The per-round structured-sumcheck statement is inhabited for any inhabited context — the
intermediate-statement `Inhabited` input of the failing-det rbr knowledge-soundness keystone at
every sumcheck-side seam. -/
instance instInhabitedSumcheckStatement {Ctx : Type} [Inhabited Ctx] (i : Fin (ℓ' + 1)) :
    Inhabited (Statement (L := L) (ℓ := ℓ') Ctx i) :=
  ⟨{ sumcheck_target := 0, challenges := fun _ => 0, ctx := default }⟩

/-- The per-round structured-sumcheck witness is inhabited (zero polynomials) — the
`Nonempty Wit₂` input of the keystones at the sumcheck-side seams. -/
instance instInhabitedSumcheckWitness (i : Fin (ℓ' + 1)) (d : ℕ) :
    Inhabited (Sumcheck.Structured.SumcheckWitness L ℓ' i d) :=
  ⟨{ t' := 0, H := 0 }⟩

/-! ## Round-count and seam direction facts

Each binary keystone application needs `0 < n` (the right phase has at least one round) and the
two direction facts `hDir₂ : pSpec₂.dir 0 = .P_to_V` (the right phase opens with a prover
message) and `hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, _⟩ = .P_to_V` (the same fact inside the appended
indexing). -/

/-- The sumcheck loop (over any `NeZero` number of rounds) has positive length. -/
theorem vsum_two_pos : 0 < Fin.vsum (fun _ : Fin ℓ' => 2) := by
  have : (0 : ℕ) < ℓ' := Nat.pos_of_ne_zero (NeZero.ne ℓ')
  rcases ℓ' with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

/-- A single sumcheck round opens with the prover's polynomial message. -/
theorem pSpecSumcheckRound_dir_zero :
    (pSpecSumcheckRound (L := L)).dir ⟨0, by omega⟩ = .P_to_V := rfl

/-- The final sumcheck step opens (and consists of) the prover's constant message. -/
theorem pSpecFinalSumcheck_dir_zero :
    (pSpecFinalSumcheck (L := L)).dir ⟨0, by omega⟩ = .P_to_V := rfl

/-- Round 0 of a `seqCompose` chain of sumcheck rounds (any length) is a prover message. The
generic-length form feeds the per-step seams of the loop induction. -/
theorem pSpecSumcheckLoopGen_dir_zero (k : ℕ) (hpos : 0 < Fin.vsum (fun _ : Fin k => 2)) :
    (ProtocolSpec.seqCompose (fun _ : Fin k => pSpecSumcheckRound (L := L))).dir ⟨0, hpos⟩
      = .P_to_V := by
  rcases seqCompose_appendValid (pSpec := fun _ : Fin k => pSpecSumcheckRound (L := L))
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h, hdir⟩
  · omega
  · exact hdir

/-- Round 0 of the sumcheck loop is a prover message (the `pSpecSumcheckLoop` specialization;
public version of `General.lean`'s private `sumcheckLoop_dir_zero`). -/
theorem pSpecSumcheckLoop_dir_zero (hpos : 0 < Fin.vsum (fun _ : Fin ℓ' => 2)) :
    (pSpecSumcheckLoop L ℓ').dir ⟨0, hpos⟩ = .P_to_V :=
  pSpecSumcheckLoopGen_dir_zero L ℓ' hpos

/-- Seam direction fact for the loop-internal steps (head round `++ₚ` tail chain): the appended
protocol's direction at the head boundary (index `2`) is the tail's opening prover message. -/
theorem pSpecSumcheckRound_seqCompose_seam_dir (k : ℕ)
    (hpos : 0 < Fin.vsum (fun _ : Fin k => 2)) :
    ((pSpecSumcheckRound (L := L)) ++ₚ
        ProtocolSpec.seqCompose (fun _ : Fin k => pSpecSumcheckRound (L := L))).dir
      ⟨2, by omega⟩ = .P_to_V := by
  rw [show (⟨2, by omega⟩ : Fin (2 + Fin.vsum (fun _ : Fin k => 2)))
      = Fin.natAdd 2 (⟨0, hpos⟩ : Fin (Fin.vsum (fun _ : Fin k => 2))) from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact pSpecSumcheckLoopGen_dir_zero L k hpos

/-- Round 0 of the core interaction (loop `++ₚ` final sumcheck) is a prover message — the
`hDir₂` input of the batching-core seam keystone. -/
theorem pSpecCoreInteraction_dir_zero :
    (pSpecCoreInteraction (L := L) (ℓ' := ℓ')).dir ⟨0, by omega⟩ = .P_to_V := by
  have hvsum : 0 < Fin.vsum (fun _ : Fin ℓ' => 2) := vsum_two_pos ℓ'
  rw [show (⟨0, by omega⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2) + 1))
      = Fin.castLE (by omega) (⟨0, hvsum⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact pSpecSumcheckLoopGen_dir_zero L ℓ' hvsum

/-- Seam direction fact for the core-interaction seam (loop `++ₚ` final): the appended protocol's
direction at the loop/final boundary is the final step's prover message — the `hDir` input of the
core-interaction seam keystone. -/
theorem pSpecCoreInteraction_dir_seam :
    (pSpecCoreInteraction (L := L) (ℓ' := ℓ')).dir
      ⟨Fin.vsum (fun _ : Fin ℓ' => 2), by omega⟩ = .P_to_V := by
  rw [show (⟨Fin.vsum (fun _ : Fin ℓ' => 2), by omega⟩ :
        Fin (Fin.vsum (fun _ : Fin ℓ' => 2) + 1))
      = Fin.natAdd (Fin.vsum (fun _ : Fin ℓ' => 2)) (⟨0, Nat.one_pos⟩ : Fin 1) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  rfl

/-- Seam direction fact for the batching-core seam (batching `++ₚ` core interaction): the appended
protocol's direction at the batching/core boundary (index `2`) is the core interaction's opening
prover message — the `hDir` input of the batching-core seam keystone. -/
theorem pSpecLargeFieldReduction_dir_seam :
    (pSpecLargeFieldReduction κ L K P ℓ').dir ⟨2, by omega⟩ = .P_to_V := by
  rw [show (⟨2, by omega⟩ : Fin (2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1)))
      = Fin.natAdd 2 (⟨0, by omega⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2) + 1)) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact pSpecCoreInteraction_dir_zero L ℓ'

/-- Seam direction fact for the full seam (batching-core `++ₚ` MLIOPCS opening): given the
abstract opening's message-seam facts (`hMlnPos`/`hMlnDir`, as in the completeness capstone), the
appended protocol's direction at the boundary is the opening's first prover message — the `hDir`
input of the full seam keystone. -/
theorem fullPspec_dir_seam (mlIOPCS : MLIOPCS L ℓ')
    (hMlnPos : 0 < mlIOPCS.numRounds)
    (hMlnDir : mlIOPCS.pSpec.dir ⟨0, hMlnPos⟩ = .P_to_V) :
    (fullPspec κ L K P ℓ' mlIOPCS).dir
      ⟨2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1), by omega⟩ = .P_to_V := by
  rw [show (⟨2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1), by omega⟩ :
        Fin (2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1) + mlIOPCS.numRounds))
      = Fin.natAdd (2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1))
          (⟨0, hMlnPos⟩ : Fin mlIOPCS.numRounds) from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact hMlnDir

end
end RingSwitching

-- Axiom audit: each must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms RingSwitching.instInhabitedMLPEvalStatement
#print axioms RingSwitching.instInhabitedBatchingStmtIn
#print axioms RingSwitching.instInhabitedWitMLP
#print axioms RingSwitching.instInhabitedRingSwitchingBaseContext
#print axioms RingSwitching.instInhabitedSumcheckStatement
#print axioms RingSwitching.instInhabitedSumcheckWitness
#print axioms RingSwitching.vsum_two_pos
#print axioms RingSwitching.pSpecSumcheckRound_dir_zero
#print axioms RingSwitching.pSpecFinalSumcheck_dir_zero
#print axioms RingSwitching.pSpecSumcheckLoopGen_dir_zero
#print axioms RingSwitching.pSpecSumcheckLoop_dir_zero
#print axioms RingSwitching.pSpecSumcheckRound_seqCompose_seam_dir
#print axioms RingSwitching.pSpecCoreInteraction_dir_zero
#print axioms RingSwitching.pSpecCoreInteraction_dir_seam
#print axioms RingSwitching.pSpecLargeFieldReduction_dir_seam
#print axioms RingSwitching.fullPspec_dir_seam
