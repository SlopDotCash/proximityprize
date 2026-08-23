/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet

/-!
# Failing-determinism witnesses for the RingSwitching sumcheck-side verifiers (issue #29)

The round and final-sumcheck verifiers are *failing*-deterministic: their `verify`, simulated
against the transcript-message oracle, collapses to `if check then pure (accept …) else failure`
(`iteratedSumcheckOracleVerifier_verify_collapse` / `finalSumcheckVerifier_verify_collapse`).
This file reshapes those collapses into the `Option`-valued form and feeds them through
`OracleVerifier.toVerifier_eq_failingDet_of_collapse`, producing the failing-determinism
witnesses consumed by the failing-det rbr knowledge-soundness append keystone
(`append_rbrKnowledgeSoundness_failingDet_subsingleton`).
-/

open OracleSpec OracleComp ProtocolSpec
open Sumcheck.Structured
open scoped NNReal

noncomputable section
namespace RingSwitching.SumcheckPhase

/-- **`if`-`pure`-`failure` reshape.** A conditional between `pure` and `failure` in
`OptionT (OracleComp _)` is the `OptionT.mk` of the corresponding `Option`-valued pure
computation — the bridge between the `*_verify_collapse` shape and the failing-determinism
witness shape. -/
theorem ite_pure_failure_eq_mk {ι : Type} {oSpec : OracleSpec ι} {α : Type}
    (c : Prop) [Decidable c] (a : α) :
    (if c then pure a else failure : OptionT (OracleComp oSpec) α)
      = OptionT.mk (pure (if c then some a else none)) := by
  split <;> rfl

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

/-- The round verifier's deterministic partial verdict: `some` of the advanced round statement if
the sum-check passes, else `none` (the verifier aborts). Matches
`iteratedSumcheckOracleVerifier_verify_collapse` exactly. -/
def roundVerifyFn? (i : Fin ℓ')
    (p : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc
      × ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecSumcheckRound L)) :
    Option (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ) :=
  if (∑ b ∈ (boolDomain L ℓ').points i, (FullTranscript.messages tr ⟨0, rfl⟩).val.eval b)
      = p.1.sumcheck_target then
    some { ctx := p.1.ctx,
           sumcheck_target := (FullTranscript.messages tr ⟨0, rfl⟩).val.eval
             (FullTranscript.challenges tr ⟨1, rfl⟩),
           challenges := Fin.cons (FullTranscript.challenges tr ⟨1, rfl⟩) p.1.challenges }
  else none

/-- **Failing-determinism witness for the round verifier.** -/
theorem iteratedSumcheckOracleVerifier_toVerifier_failingDet (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).toVerifier
      = ⟨fun p tr => OptionT.mk (pure ((roundVerifyFn? κ L K P ℓ ℓ' aOStmtIn i p tr).map (fun s => (s,
          fun j => match h : (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).embed j with
            | Sum.inl j' =>
                ((iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).hEq j ▸ h ▸ p.2 j')
            | Sum.inr j' =>
                ((iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).hEq j ▸ h ▸
                  tr.messages j')))))⟩ :=
  OracleVerifier.toVerifier_eq_failingDet_of_collapse _ _ (fun stmt oStmt tr => by
    rw [iteratedSumcheckOracleVerifier_verify_collapse, ite_pure_failure_eq_mk]
    rfl)

variable [IsDomain L] [IsDomain K]

/-- The final-sumcheck verifier's deterministic partial verdict. Matches
`finalSumcheckVerifier_verify_collapse` exactly. -/
def finalSumcheckVerifyFn?
    (p : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecFinalSumcheck L)) :
    Option (MLPEvalStatement L ℓ') :=
  if p.1.sumcheck_target
      = compute_final_eq_value κ L K P ℓ ℓ' h_l p.1.ctx.t_eval_point p.1.challenges
          p.1.ctx.r_batching * (show L from FullTranscript.messages tr ⟨0, rfl⟩) then
    some { t_eval_point := p.1.challenges,
           original_claim := (FullTranscript.messages tr ⟨0, rfl⟩ : L) }
  else none

/-- **Failing-determinism witness for the final-sumcheck verifier.** -/
theorem finalSumcheckVerifier_toVerifier_failingDet :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier
      = ⟨fun p tr => OptionT.mk (pure
          ((finalSumcheckVerifyFn? κ L K P ℓ ℓ' h_l aOStmtIn p tr).map (fun s => (s,
          fun j => match h : (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).embed j with
            | Sum.inl j' =>
                ((finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).hEq j ▸ h ▸ p.2 j')
            | Sum.inr j' =>
                ((finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).hEq j ▸ h ▸
                  tr.messages j')))))⟩ :=
  OracleVerifier.toVerifier_eq_failingDet_of_collapse _ _ (fun stmt oStmt tr => by
    rw [finalSumcheckVerifier_verify_collapse, ite_pure_failure_eq_mk]
    rfl)

end RingSwitching.SumcheckPhase
end

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_toVerifier_failingDet
#print axioms RingSwitching.SumcheckPhase.finalSumcheckVerifier_toVerifier_failingDet
