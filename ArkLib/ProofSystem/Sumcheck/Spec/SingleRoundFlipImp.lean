/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundKnowFlip

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

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
  {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}

/-- **Transcript-independence of a knowledge state function.**

`kSF` is *transcript-independent* if its value depends only on the statement: there is a predicate
`P : StmtIn → Prop` such that for every round `m`, statement `stmtIn`, transcript `tr`, and
intermediate witness `witMid`, `kSF m stmtIn tr witMid ↔ P stmtIn`.

This definition is a conditional mathematical property. The old concrete input-query knowledge
state function is retired; a witness for the canonical message-checking verifier must be supplied
independently. -/
def TranscriptIndependent
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor) : Prop :=
  ∃ P : StmtIn → Prop,
    ∀ (m : Fin (n + 1)) (stmtIn : StmtIn) (tr : Transcript m pSpec) (witMid : WitMid m),
      kSF m stmtIn tr witMid ↔ P stmtIn

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **A transcript-independent knowledge state function has pointwise-impossible knowledge flips
(this is `hFlipImp`).**

If `kSF` is `TranscriptIndependent` (with statement-predicate `P`), then for every round `i`,
statement `stmtIn`, transcript `transcript`, challenge `challenge`, and intermediate witness
`witMid`, the per-round knowledge-flip event

```
¬ kSF i.castSucc stmtIn transcript (extractor.extractMid …) ∧ kSF i.succ stmtIn (transcript.concat …) witMid
```

is `False`.  Indeed, by transcript-independence the first conjunct is `¬ P stmtIn` and the second is
`P stmtIn`, whose conjunction is a contradiction.

This is exactly the shape of the `hFlipImp` hypothesis of
`Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_of_flipImpossible` (and of the generic
`rbrKnowledgeFlipProb_*_of_flipImpossible`), and it is the abstract form of the `hn hy` one-liner that
closes the `Unit`-only `oracleVerifier_rbrKnowledgeSoundness`.  No prover, witness, or probability is
involved. -/
theorem flipImpossible_of_transcriptIndep
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (hIndep : TranscriptIndependent kSF)
    (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
    (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i)
    (witMid : WitMid i.1.succ) :
    ¬ (¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
        kSF i.1.succ stmtIn (transcript.concat challenge) witMid) := by
  obtain ⟨P, hP⟩ := hIndep
  rintro ⟨hNot, hYes⟩
  -- Both conjuncts collapse to `P stmtIn` by transcript-independence: contradiction.
  exact hNot ((hP _ stmtIn transcript _).mpr ((hP _ stmtIn (transcript.concat challenge) witMid).mp hYes))

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **The `hFlipImp` family, for every round, from transcript-independence.**

Packaging `flipImpossible_of_transcriptIndep` as the universally-quantified flip-impossibility family
in exactly the shape required by the generic
`rbrKnowledgeFlipProb_eq_zero_of_flipImpossible` / `..._le_of_flipImpossible`. -/
theorem flipImpossible_family_of_transcriptIndep
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (hIndep : TranscriptIndependent kSF) :
    ∀ (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
        (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i)
        (witMid : WitMid i.1.succ),
      ¬ (¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid) :=
  fun i stmtIn transcript challenge witMid =>
    flipImpossible_of_transcriptIndep kSF hIndep i stmtIn transcript challenge witMid

end Sumcheck.Spec.SingleRound.KnowFlip

namespace Sumcheck.Spec.SingleRound.Simple

open Sumcheck.Spec.SingleRound.KnowFlip

variable {R : Type} [CommSemiring R] {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [DecidableEq R] [SampleableType R]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The `H-knowFlip` residual, single-round sum-check oracle verifier, from
transcript-independence.**

For the single-round sum-check oracle verifier `Simple.oracleVerifier R deg D oSpec`, given a
knowledge state function `kSF` (with extractor `extractor`) that is `TranscriptIndependent`, this
produces the per-round knowledge-flip bound **for every prover witness type** `PWitIn`/`PWitOut` and
any error family `rbrError` — exactly the `hKnowFlip` argument consumed by
`Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip`
(`Spec/SingleRoundPlainRbr.lean`).

The flip probability is identically `0` (the flip event is pointwise impossible by
`flipImpossible_of_transcriptIndep`), hence `≤ rbrError i`, uniformly over the prover witness type.
`hIndep` is an explicit property of the supplied knowledge-state function. No such witness is
constructed here for the canonical message-checking verifier; the old input-query instantiation
has been retired and archived. -/
theorem oracleVerifier_hKnowFlip_of_transcriptIndep
    {relIn : Set ((StmtIn R × ∀ i, OStmtIn R deg i) × Unit)}
    {relOut : Set ((StmtOut R × ∀ i, OStmtOut R deg i) × Unit)}
    {WitMid : Fin (2 + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec (StmtIn R × ∀ i, OStmtIn R deg i) Unit Unit
      (SingleRound.pSpec R deg) WitMid}
    (kSF : ((oracleVerifier R deg D oSpec).toVerifier).KnowledgeStateFunction init impl
      relIn relOut extractor)
    (hIndep : TranscriptIndependent kSF)
    (rbrError : (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0)
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
  oracleVerifier_hKnowFlip_of_flipImpossible kSF rbrError
    (flipImpossible_family_of_transcriptIndep kSF hIndep)
    PWitIn PWitOut stmtIn witIn' prover i

/-- **The all-prover-witness-type `hKnowFlip` hypothesis, from transcript-independence.**

Repackages `oracleVerifier_hKnowFlip_of_transcriptIndep` as the exact universally-quantified
`hKnowFlip` argument (`∀ PWitIn PWitOut stmtIn witIn' prover i, … ≤ rbrError i`) consumed by
`Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip`.  Feeding this (together with
`kSF` and `rbrError`) to that weakening yields per-round plain soundness conditional on the
supplied knowledge-state function and its transcript-independence
witness `hIndep`. The retired constant input-query state function supplies neither premise for
the canonical message verifier. -/
theorem oracleVerifier_hKnowFlip_family_of_transcriptIndep
    {relIn : Set ((StmtIn R × ∀ i, OStmtIn R deg i) × Unit)}
    {relOut : Set ((StmtOut R × ∀ i, OStmtOut R deg i) × Unit)}
    {WitMid : Fin (2 + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec (StmtIn R × ∀ i, OStmtIn R deg i) Unit Unit
      (SingleRound.pSpec R deg) WitMid}
    (kSF : ((oracleVerifier R deg D oSpec).toVerifier).KnowledgeStateFunction init impl
      relIn relOut extractor)
    (hIndep : TranscriptIndependent kSF)
    (rbrError : (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0) :
    ∀ (PWitIn PWitOut : Type) (stmtIn : StmtIn R × ∀ i, OStmtIn R deg i) (witIn' : PWitIn)
      (prover : Prover oSpec (StmtIn R × ∀ i, OStmtIn R deg i) PWitIn
        (StmtOut R × ∀ i, OStmtOut R deg i) PWitOut (SingleRound.pSpec R deg))
      (i : (SingleRound.pSpec R deg).ChallengeIdx),
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
  fun PWitIn PWitOut stmtIn witIn' prover i =>
    oracleVerifier_hKnowFlip_of_transcriptIndep kSF hIndep rbrError
      PWitIn PWitOut stmtIn witIn' prover i

end Sumcheck.Spec.SingleRound.Simple

end

#print axioms Sumcheck.Spec.SingleRound.KnowFlip.flipImpossible_of_transcriptIndep
#print axioms Sumcheck.Spec.SingleRound.KnowFlip.flipImpossible_family_of_transcriptIndep
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_of_transcriptIndep
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_family_of_transcriptIndep
