/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundKnowFlip

/-!
# Discharging `hFlipImp`: the single-round sum-check knowledge-flip event is identically `False`
(issue #13, residual `I-flipImp`)

The all-prover-witness-type per-round knowledge-flip bound assembled in
`Spec/SingleRoundKnowFlip.lean`
(`Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_of_flipImpossible`) consumes one named
residual: the *flip-impossibility* hypothesis `hFlipImp`, asserting that for every round `i`,
statement `stmtIn`, transcript `transcript`, challenge `challenge`, and intermediate witness
`witMid`,

```
¬ (¬ kSF i.castSucc stmtIn transcript (extractMid …) ∧ kSF i.succ stmtIn (transcript.concat …) witMid).
```

This file *discharges* that residual from the only property the in-tree single-round knowledge state
function actually has — and the only property the `Unit`-only
`oracleVerifier_rbrKnowledgeSoundness` proof (`Spec/SingleRound.lean`, lines `intro … ; … ; exact
hn hy`) ever used: **transcript-independence**.

## The mathematical content

The (private, in `Spec/SingleRound.lean`) `Simple.simpleKnowledgeStateFunction` is defined by

```
toFun := fun _ stmtIn _ _ => (stmtIn, ()) ∈ inputRelation R deg D
```

i.e. its value `kSF m stmtIn tr witMid` ignores the round `m`, the transcript `tr`, and the witness
`witMid`, depending only on `stmtIn`.  Call such a `kSF` *transcript-independent*: there is a
predicate `P : StmtIn → Prop` with `kSF m stmtIn tr w ↔ P stmtIn` for all `m, stmtIn, tr, w`.

For a transcript-independent `kSF`, the two conjuncts of the flip event both collapse to `P stmtIn`:

* `¬ kSF i.castSucc stmtIn transcript (extractMid …)`  ⇔  `¬ P stmtIn`;
* `kSF i.succ stmtIn (transcript.concat challenge) witMid`  ⇔  `P stmtIn`.

Their conjunction is `¬ P stmtIn ∧ P stmtIn`, a contradiction.  Hence the flip event is pointwise
impossible — *exactly* `hFlipImp`.  This is `flipImpossible_of_transcriptIndep`, stated and proven
for an **arbitrary** verifier, extractor, knowledge state function, and witness-middle family; it
needs no probability theory, no prover, and no witness, mirroring the `hn hy` one-liner of the
original `Unit`-only proof.

## What is proven vs. taken as a named hypothesis

`Simple.simpleKnowledgeStateFunction` is `private`, so a downstream file cannot name it to *read off*
its transcript-independence from the definitional unfolding.  We therefore expose the *structural*
property `TranscriptIndependent` and prove that it is sufficient for `hFlipImp`:

* `flipImpossible_of_transcriptIndep` — for **any** `kSF` that is `TranscriptIndependent`, the
  per-round knowledge-flip event is pointwise impossible (`hFlipImp`).  No `sorry`/`admit`.

* `oracleVerifier_hKnowFlip_of_transcriptIndep` — its single-round sum-check specialization, chaining
  through `oracleVerifier_hKnowFlip_of_flipImpossible` to produce the `hKnowFlip` argument consumed by
  `Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip`, with the flip probability
  identically `0` and hence `≤ rbrError i`, uniformly over the prover witness type.

The only residual is the named hypothesis `hIndep : TranscriptIndependent kSF` — the
transcript-independence of the single-round knowledge state function.  This is *not* deep
mathematics: it is the syntactic fact that `simpleKnowledgeStateFunction.toFun` ignores its `m`,
`tr`, and `witMid` arguments, witnessed by `P := fun stmtIn => (stmtIn, ()) ∈ inputRelation R deg D`
and `Iff.rfl`.  Because that definition is `private`, the witness cannot be supplied by name here; it
is supplied at the call site that already has `simpleKnowledgeStateFunction` in scope (same file /
namespace).  Every other step of `hFlipImp` is fully discharged below.
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

This is precisely the property of the in-tree single-round sum-check knowledge state function
`Simple.simpleKnowledgeStateFunction`, whose `toFun` is `fun _ stmtIn _ _ => (stmtIn, ()) ∈
inputRelation R deg D` — witnessed by `P := fun stmtIn => (stmtIn, ()) ∈ inputRelation R deg D` with
`Iff.rfl`.  It is the only property the `Unit`-only `oracleVerifier_rbrKnowledgeSoundness` proof
ever uses. -/
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
This is the in-tree `simpleKnowledgeStateFunction` case once its transcript-independence (`hIndep`,
witnessed by `P := fun stmtIn => (stmtIn, ()) ∈ inputRelation R deg D` with `Iff.rfl`) is supplied —
the single remaining residual, which is the syntactic fact that the private `toFun` ignores its `m`,
`tr`, and `witMid` arguments.  Everything else of `H-knowFlip` is discharged. -/
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
  oracleVerifier_hKnowFlip_of_flipImpossible kSF rbrError
    (flipImpossible_family_of_transcriptIndep kSF hIndep)
    PWitIn PWitOut stmtIn witIn' prover i

/-- **The all-prover-witness-type `hKnowFlip` hypothesis, from transcript-independence.**

Repackages `oracleVerifier_hKnowFlip_of_transcriptIndep` as the exact universally-quantified
`hKnowFlip` argument (`∀ PWitIn PWitOut stmtIn witIn' prover i, … ≤ rbrError i`) consumed by
`Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip`.  Feeding this (together with
`kSF` and `rbrError`) to that weakening yields unconditional per-round *plain* round-by-round
soundness for the single-round sum-check oracle verifier — modulo only the transcript-independence
witness `hIndep` of the (private) `simpleKnowledgeStateFunction`. -/
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
  fun PWitIn PWitOut stmtIn witIn' prover i =>
    oracleVerifier_hKnowFlip_of_transcriptIndep kSF hIndep rbrError
      PWitIn PWitOut stmtIn witIn' prover i

end Sumcheck.Spec.SingleRound.Simple

end

#print axioms Sumcheck.Spec.SingleRound.KnowFlip.flipImpossible_of_transcriptIndep
#print axioms Sumcheck.Spec.SingleRound.KnowFlip.flipImpossible_family_of_transcriptIndep
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_of_transcriptIndep
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_hKnowFlip_family_of_transcriptIndep
