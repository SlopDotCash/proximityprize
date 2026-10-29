/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Conditional sumcheck facts under canonical message-polynomial semantics

The input-only rejection and transcript-independent concrete knowledge-state claims from the old
verifier are retired. The declarations below retain only mathematical correspondence, outer-phase,
or explicitly conditional knowledge-flip results. No zero-error sumcheck completion follows from
this module. Exact retired commands are in
`scripts/integration/sumcheck-message-semantics-retirements.json`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

noncomputable section

namespace Sumcheck.Spec.SingleRound.KnowFlip

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut WitIn WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **All-prover-witness-type per-round knowledge-flip probability is `0` when the flip event is
pointwise impossible.**

For an arbitrary verifier `verifier`, round-by-round extractor `extractor`, and knowledge state
function `kSF`, suppose the per-round knowledge-flip event is *pointwise impossible*: for every round
`i`, statement `stmtIn`, transcript `transcript`, challenge `challenge`, and intermediate witness
`witMid`,

```
¬ (¬ kSF i.castSucc stmtIn transcript (extractor.extractMid i stmtIn (transcript.concat challenge)
      witMid) ∧ kSF i.succ stmtIn (transcript.concat challenge) witMid).
```

Then, for **every** prover witness type `PWitIn`/`PWitOut`, prover, witness, and round, the per-round
knowledge-flip probability over the with-log run block is `0`.

This abstracts the zero-flip step used by the former input-query verifier's proof. For the
canonical message-polynomial verifier it applies only when the caller supplies a valid knowledge
state function and a flip-impossibility proof. This module does not construct those inputs or
prove the canonical round-knowledge bound. The transfer is uniform in the prover witness type. -/
theorem rbrKnowledgeFlipProb_eq_zero_of_flipImpossible
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (hFlipImp : ∀ (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
        (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i)
        (witMid : WitMid i.1.succ),
      ¬ (¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid))
    (PWitIn PWitOut : Type) (stmtIn : StmtIn) (witIn' : PWitIn)
    (prover : Prover oSpec StmtIn PWitIn StmtOut PWitOut pSpec) (i : pSpec.ChallengeIdx) :
    probEvent (fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid) (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
            return (transcript, challenge, proveQueryLog))).run' (← init)) = 0 := by
  -- The flip event holds for no point of the support: any witness exhibiting the flip would
  -- contradict the pointwise impossibility `hFlipImp`.
  refine _root_.prEvent_eq_zero_of_forall_not _ _ ?_
  rintro ⟨transcript, challenge, _log⟩ ⟨witMid, hNot, hYes⟩
  exact hFlipImp i stmtIn transcript challenge witMid ⟨hNot, hYes⟩

/-- **All-prover-witness-type per-round knowledge-flip bound from pointwise flip-impossibility.**

A trivial consequence of `rbrKnowledgeFlipProb_eq_zero_of_flipImpossible`: since the per-round
knowledge-flip probability is `0`, it is `≤ rbrError i` for *any* error family `rbrError`.  This is
the all-witness-type `hKnowFlip` shape directly. -/
theorem rbrKnowledgeFlipProb_le_of_flipImpossible
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrError : pSpec.ChallengeIdx → ℝ≥0)
    (hFlipImp : ∀ (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
        (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i)
        (witMid : WitMid i.1.succ),
      ¬ (¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid))
    (PWitIn PWitOut : Type) (stmtIn : StmtIn) (witIn' : PWitIn)
    (prover : Prover oSpec StmtIn PWitIn StmtOut PWitOut pSpec) (i : pSpec.ChallengeIdx) :
    probEvent (fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid) (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
            return (transcript, challenge, proveQueryLog))).run' (← init)) ≤ rbrError i := by
  rw [rbrKnowledgeFlipProb_eq_zero_of_flipImpossible kSF hFlipImp PWitIn PWitOut stmtIn witIn'
    prover i]
  exact zero_le

end Sumcheck.Spec.SingleRound.KnowFlip

namespace Sumcheck.Spec.SingleRound.Simple

open Sumcheck.Spec.SingleRound.KnowFlip

variable {R : Type} [CommSemiring R] {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [DecidableEq R] [SampleableType R]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The `H-knowFlip` residual, single-round sum-check oracle verifier.**

For the single-round sum-check oracle verifier `Simple.oracleVerifier R deg D oSpec`, the caller supplies:

* a supplied knowledge state function `kSF` with extractor `extractor`, satisfying the current
  canonical verifier's clauses, and
* an explicit **flip-impossibility** proof `hFlipImp` for that supplied function,

These are genuine assumptions. The former constant-input-relation
`simpleKnowledgeStateFunction` belonged to the historical input-query verifier and is retired;
it does not establish these clauses for the canonical message-polynomial verifier.

The supplied data produce the per-round knowledge-flip bound **for every prover witness type** `PWitIn`/`PWitOut`
and any error family `rbrError` — i.e. exactly the `hKnowFlip` argument consumed by
`Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip`
(`Spec/SingleRoundPlainRbr.lean`).

The conclusion is `≤ rbrError i` (with the flip probability being `0`), uniformly over the prover
witness type, because the supplied proof makes the flip pointwise impossible. This transfers the
stated assumptions; it does not discharge canonical sumcheck knowledge soundness. -/
theorem oracleVerifier_hKnowFlip_of_flipImpossible
    {relIn : Set ((StmtIn R × ∀ i, OStmtIn R deg i) × Unit)}
    {relOut : Set ((StmtOut R × ∀ i, OStmtOut R deg i) × Unit)}
    {WitMid : Fin (2 + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec (StmtIn R × ∀ i, OStmtIn R deg i) Unit Unit
      (SingleRound.pSpec R deg) WitMid}
    (kSF : ((oracleVerifier R deg D oSpec).toVerifier).KnowledgeStateFunction init impl
      relIn relOut extractor)
    (rbrError : (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0)
    (hFlipImp : ∀ (i : (SingleRound.pSpec R deg).ChallengeIdx)
        (stmtIn : StmtIn R × ∀ i, OStmtIn R deg i)
        (transcript : Transcript i.1.castSucc (SingleRound.pSpec R deg))
        (challenge : (SingleRound.pSpec R deg).Challenge i) (witMid : WitMid i.1.succ),
      ¬ (¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid))
    (PWitIn PWitOut : Type) (stmtIn : StmtIn R × ∀ i, OStmtIn R deg i) (witIn' : PWitIn)
    (prover : Prover oSpec (StmtIn R × ∀ i, OStmtIn R deg i) PWitIn
      (StmtOut R × ∀ i, OStmtOut R deg i) PWitOut (SingleRound.pSpec R deg))
    (i : (SingleRound.pSpec R deg).ChallengeIdx) :
    probEvent (fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid) (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp ((SingleRound.pSpec R deg).getChallenge i)
              (oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'(challengeOracleInterface))
            return (transcript, challenge, proveQueryLog))).run' (← init)) ≤ rbrError i :=
  rbrKnowledgeFlipProb_le_of_flipImpossible kSF rbrError hFlipImp PWitIn PWitOut stmtIn witIn'
    prover i

end Sumcheck.Spec.SingleRound.Simple

end

#print axioms Sumcheck.Spec.SingleRound.KnowFlip.rbrKnowledgeFlipProb_eq_zero_of_flipImpossible
#print axioms Sumcheck.Spec.SingleRound.KnowFlip.rbrKnowledgeFlipProb_le_of_flipImpossible
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_of_flipImpossible
