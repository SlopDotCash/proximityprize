/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof
import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

/-!
# Perfect completeness of sequential composition (empty trailing seam) — discharged

This file proves `Reduction.append_perfectCompleteness_empty_proof`, the `n = 0` analogue of
`Reduction.append_perfectCompleteness_msg_proof`: perfect completeness of `R₁.append R₂` when the
trailing protocol `pSpec₂` is empty (`ProtocolSpec 0`).

The proof reuses the support-decomposition theorem
`Reduction.append_perfectCompleteness_of_run_factor`, discharging its prover-run factoring
hypothesis with `Prover.append_run_empty`. No seam-direction hypotheses are required.

This is the empty-tail case of the `hAppend` keystone consumed by
`Reduction.seqCompose_perfectCompleteness_of_append_msg` (it fires at the final induction step, where
the trailing `seqCompose` is over zero remaining components). Together with the message-seam keystone
it yields full multi-round sum-check perfect completeness.
-/

open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [∀ t, Fintype ((oSpec).Range t)] [∀ t, Inhabited ((oSpec).Range t)]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 1000000 in
/-- **Perfect completeness of `Reduction.append` at an empty trailing seam (`pSpec₂ : ProtocolSpec 0`).** The `n = 0` analogue of `append_perfectCompleteness_msg_proof`. -/
theorem append_perfectCompleteness_empty_proof
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q : OracleComp oSpec β))
    [∀ t, Fintype (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range t)]
    [∀ t, Inhabited (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range t)]
    [∀ t, Fintype (((oSpec + [pSpec₁.Challenge]ₒ)).Range t)] [∀ t, Inhabited (((oSpec + [pSpec₁.Challenge]ₒ)).Range t)]
    [∀ t, Fintype (((oSpec + [pSpec₂.Challenge]ₒ)).Range t)] [∀ t, Inhabited (((oSpec + [pSpec₂.Challenge]ₒ)).Range t)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  exact append_perfectCompleteness_of_run_factor R₁ R₂ h₁ h₂
    (fun stmt wit => Prover.append_run_empty R₁.prover R₂.prover stmt wit) hInit hImplSupp

end Reduction
