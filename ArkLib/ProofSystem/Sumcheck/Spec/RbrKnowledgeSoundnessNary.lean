/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.RbrKnowledgeSoundnessOracle
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# Generic multi-round sum-check rbr knowledge soundness via the n-ary failing-det fold (#114)

Each round's verifier (`SingleRound.verifier`, the `liftContext` of the `Simple` guard-form
verifier) is failing-deterministic with the explicit verdict `roundVerify?`; every round opens with
a prover message, so the n-ary `seqCompose_rbrKnowledgeSoundness_failingDet` fold applies,
assembling the full sum-check verifier's round-by-round knowledge soundness from the per-round
facts.
-/

open OracleComp OracleSpec ProtocolSpec Sumcheck Sumcheck.Spec Polynomial Finset
open scoped NNReal

namespace Sumcheck.Spec.SingleRound

variable {R : Type} [CommSemiring R] [VCVCompatible R] {n deg : ℕ} (D : Fin (deg + 1) ↪ R)
  {ι : Type} (oSpec : OracleSpec ι)

/-- The failing-deterministic partial verdict of the `i`-th-round sum-check verifier (the
`liftContext` of the `Simple` guard-form verifier): check the claimed sum at the projected inner
statement, emit the lifted next-round statement. -/
noncomputable abbrev roundVerify? (i : Fin n) :
    (StatementRound R n i.castSucc × (∀ j, OracleStatement R n deg j)) →
    (SingleRound.pSpec R deg).FullTranscript →
    Option (StatementRound R n i.succ × (∀ j, OracleStatement R n deg j)) :=
  fun s tr => (simpleOracleVerify? deg D ((oStmtLens R n deg D i).proj s) tr).map
    ((oStmtLens R n deg D i).lift s)

/-- The actual canonical round verifier is failing-deterministic with the shared verdict. -/
theorem verifier_eq_failingDet
    [∀ j, SampleableType ((SingleRound.pSpec R deg).Challenge j)] (i : Fin n) :
    verifier (R := R) (n := n) (deg := deg) D oSpec i
      = ⟨fun s tr => OptionT.mk (pure (roundVerify? D i s tr))⟩ := by
  ext s tr
  simp only [verifier, Verifier.liftContext, Simple.verifier, roundVerify?,
    simpleOracleVerify?, OracleComp.guard_eq]
  split <;> simp_all

end Sumcheck.Spec.SingleRound

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [VCVCompatible R] {n deg : ℕ} (D : Fin (deg + 1) ↪ R)
  {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Generic multi-round sum-check rbr knowledge soundness, parameterized on the per-round
facts.** -/
theorem verifier_rbrKnowledgeSoundness_of_perRound [Subsingleton σ]
    [∀ j, SampleableType ((SingleRound.pSpec R deg).Challenge j)]
    [∀ i : Fin (n+1), Inhabited (StatementRound R n i × (∀ j, OracleStatement R n deg j))]
    (Wit : Fin (n + 1) → Type) (hNEW : ∀ i, Nonempty (Wit i))
    (rel : (i : Fin (n + 1)) →
      Set ((StatementRound R n i × (∀ j, OracleStatement R n deg j)) × Wit i))
    (rbrKnowledgeError : ∀ _ : Fin n, (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0)
    (hInit : ∃ s, s ∈ support init) (hInitNF : prFail init = 0)
    (h : ∀ i : Fin n, (SingleRound.verifier (R := R) (n := n) (deg := deg) D oSpec i).rbrKnowledgeSoundness
      init impl (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i)) :
    (verifier (R := R) (n := n) (deg := deg) (D := D) oSpec).rbrKnowledgeSoundness init impl
      (rel 0) (rel (Fin.last n))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        rbrKnowledgeError ij.1 ij.2) := by
  unfold verifier pSpec
  exact Verifier.seqCompose_rbrKnowledgeSoundness_failingDet
    (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j)) Wit
    (SingleRound.verifier (R := R) (n := n) (deg := deg) D oSpec)
    (SingleRound.roundVerify? D)
    (fun i => SingleRound.verifier_eq_failingDet D oSpec i)
    rel rbrKnowledgeError
    (fun _ => ⟨by omega, rfl⟩)
    hNEW hInit hInitNF h

end Sumcheck.Spec

#print axioms Sumcheck.Spec.SingleRound.verifier_eq_failingDet
#print axioms Sumcheck.Spec.verifier_rbrKnowledgeSoundness_of_perRound
