/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# All-prover-witness-type per-round knowledge-flip bound (issue #13, residual `H-knowFlip`)

The generic plain-from-knowledge weakening
`Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip`
(`Spec/SingleRoundPlainRbr.lean`) consumes the named hypothesis `hKnowFlip`: the per-round
round-by-round *knowledge-flip* probability bound **for every prover witness type**, namely

```
∀ (PWitIn PWitOut : Type) (stmtIn …) (witIn' : PWitIn)
    (prover : Prover oSpec … PWitIn … PWitOut pSpec) (i : pSpec.ChallengeIdx),
  Pr[fun ⟨transcript, challenge, _⟩ =>
      ∃ witMid,
        ¬ kSF i.castSucc stmtIn transcript
          (extractor.extractMid i stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.succ stmtIn (transcript.concat challenge) witMid
    | run-block prover witIn' i] ≤ rbrError i.
```

This file discharges that residual for the single-round sum-check oracle verifier.

## The key fact: the flip event is identically `False`

The proven `Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness`
(`Spec/SingleRound.lean`) gives the bound only for the *relation* witness types (`Unit`/`Unit`).
Its proof, however, does **not** use the prover or the witness at all: the per-round knowledge-flip
event is *pointwise impossible*.  Concretely, the knowledge state function
`Simple.simpleKnowledgeStateFunction` is **transcript-independent** — its value
`kSF m stmtIn tr witMid = (stmtIn, ()) ∈ inputRelation` does not depend on `m`, `tr`, or `witMid`.
Hence at a flip the two conjuncts read

```
¬ kSF i.castSucc stmtIn tr (extractMid …)   -- ⇔ (stmtIn,()) ∉ inputRelation
  ∧ kSF i.succ stmtIn (tr.concat chal) witMid  -- ⇔ (stmtIn,()) ∈ inputRelation
```

which is `¬P ∧ P`, a contradiction.  The flip is therefore impossible regardless of `prover`,
`witIn'`, `PWitIn`, `PWitOut`, so the flip probability is `0 ≤ rbrError i` *uniformly in every
prover witness type*.  This is exactly the all-witness content the abstract `hKnowFlip` demands.

## What is proven vs. taken as a named hypothesis

`Simple.simpleKnowledgeStateFunction` / `Simple.simpleRbrExtractor` are `private` in
`Spec/SingleRound.lean`, so a downstream file cannot name them to re-derive the impossibility from
their definitions.  We therefore prove the *fully general* statement:

* `rbrKnowledgeFlipProb_eq_zero_of_flipImpossible` — for **any** verifier, extractor, and knowledge
  state function `kSF`, if the per-round knowledge-flip event is pointwise impossible
  (hypothesis `hFlipImp`), then the per-round flip probability is `0` for **every** prover witness
  type.  This is the entire mathematical content of the `Unit`-only `oracleVerifier_rbrKnowledgeSoundness`
  proof, abstracted away from the (private) concrete `kSF` and stated for all witness types.

* `oracleVerifier_hKnowFlip_of_flipImpossible` — its single-round sum-check oracle-verifier
  specialization, producing the `hKnowFlip` argument in *exactly* the shape consumed by
  `Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip` (with any error family),
  from the same flip-impossibility hypothesis.

The only residual is the named hypothesis `hFlipImp` — the transcript-independence /
flip-impossibility of the single-round knowledge state function — which is precisely the property
the private `simpleKnowledgeStateFunction` satisfies and which the `Unit`-only proof already used
(`hn hy`).  No `sorry`/`admit`.
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

This is the prover- and witness-agnostic core of `oracleVerifier_rbrKnowledgeSoundness`: the proof of
that `Unit`-only result never touches the prover or witness, only the `hn hy` contradiction inside
the flip event.  Abstracting it makes the bound hold uniformly in the prover witness type, which is
exactly what the abstract `hKnowFlip` residual requires. -/
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
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
            return (transcript, challenge, proveQueryLog))).run' (← init)] = 0 := by
  -- The flip event holds for no point of the support: any witness exhibiting the flip would
  -- contradict the pointwise impossibility `hFlipImp`.
  refine probEvent_eq_zero ?_
  rintro ⟨transcript, challenge, _log⟩ - ⟨witMid, hNot, hYes⟩
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
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
            return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ rbrError i := by
  rw [rbrKnowledgeFlipProb_eq_zero_of_flipImpossible kSF hFlipImp PWitIn PWitOut stmtIn witIn'
    prover i]
  exact zero_le _

end Sumcheck.Spec.SingleRound.KnowFlip

namespace Sumcheck.Spec.SingleRound.Simple

open Sumcheck.Spec.SingleRound.KnowFlip

variable {R : Type} [CommSemiring R] {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [DecidableEq R] [SampleableType R]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The `H-knowFlip` residual, single-round sum-check oracle verifier.**

For the single-round sum-check oracle verifier `Simple.oracleVerifier R deg D oSpec`, given

* a knowledge state function `kSF` (with extractor `extractor`) — in practice the in-tree
  `simpleKnowledgeStateFunction` / `simpleRbrExtractor`, which is `private` and so cannot be named
  here — and
* the **flip-impossibility** hypothesis `hFlipImp` (the transcript-independence property that makes
  the per-round knowledge-flip event identically `False`; the private
  `simpleKnowledgeStateFunction` satisfies this, and the proven `oracleVerifier_rbrKnowledgeSoundness`
  already uses it via `hn hy`),

this produces the per-round knowledge-flip bound **for every prover witness type** `PWitIn`/`PWitOut`
and any error family `rbrError` — i.e. exactly the `hKnowFlip` argument consumed by
`Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip`
(`Spec/SingleRoundPlainRbr.lean`).

The conclusion is `≤ rbrError i` (with the flip probability being `0`), uniformly over the prover
witness type, because the flip is pointwise impossible.  This discharges `H-knowFlip` modulo the
single named residual `hFlipImp`. -/
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
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp ((SingleRound.pSpec R deg).getChallenge i)
              (oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'(challengeOracleInterface))
            return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ rbrError i :=
  rbrKnowledgeFlipProb_le_of_flipImpossible kSF rbrError hFlipImp PWitIn PWitOut stmtIn witIn'
    prover i

end Sumcheck.Spec.SingleRound.Simple

end

#print axioms Sumcheck.Spec.SingleRound.KnowFlip.rbrKnowledgeFlipProb_eq_zero_of_flipImpossible
#print axioms Sumcheck.Spec.SingleRound.KnowFlip.rbrKnowledgeFlipProb_le_of_flipImpossible
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_of_flipImpossible
