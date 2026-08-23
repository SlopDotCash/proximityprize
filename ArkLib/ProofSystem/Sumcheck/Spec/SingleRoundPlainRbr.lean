/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Round-by-round *plain* soundness from round-by-round *knowledge* soundness (issue #13, residual
`G-rbrWeaken` / `hRound`)

This file discharges the per-round **plain** round-by-round (RBR) soundness obligation `hRound`
(consumed by `Sumcheck.Spec.oracleVerifier_rbrSoundness` and the LogUp soundness-lift chain) by
**weakening** the already-proven single-round RBR *knowledge* soundness
`Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness`
(`Spec/SingleRound.lean`).

## The weakening, conceptually

A `Verifier.KnowledgeStateFunction` `kSF` gives rise to a plain `Verifier.StateFunction` via
`KnowledgeStateFunction.toStateFunction`, whose value on `(m, stmtIn, tr)` is
`∃ witMid, kSF m stmtIn tr witMid`.  The two RBR *flip* events compare as follows (at a fixed
realized prefix `(transcript, challenge)`):

* the **plain** soundness flip event is
  `¬ (∃ w, kSF castSucc tr w) ∧ (∃ w, kSF succ (tr.concat chal) w)`;
* the **knowledge** soundness flip event is
  `∃ w, ¬ kSF castSucc tr (extractMid … w) ∧ kSF succ (tr.concat chal) w`.

The plain event **implies** the knowledge event: the witness `w` produced by the second conjunct's
existential simultaneously witnesses the knowledge event (the first conjunct, `∀ w', ¬ kSF castSucc
w'`, in particular kills `extractMid … w`).  Hence the plain flip probability is `≤` the knowledge
flip probability, round by round.  This is the proven core
`plainFlipProb_le_knowledgeFlipProb` (whose pointwise heart is
`toStateFunctionFlip_imp_knowledgeFlip`).

## What is proven vs. taken as a named hypothesis

`rbrSoundness` quantifies over **arbitrary** prover witness types `WitIn'`/`WitOut'`, whereas
`rbrKnowledgeSoundness` fixes the prover witness types to those of the input/output *relations*.  A
`WitIn'`-prover and a `WitIn`-prover induce different transcript distributions in general, so the
plain→knowledge probability bound transfers only for matching witness types.  The faithful generic
weakening therefore takes the per-round knowledge-flip bound **for every prover witness type** as the
named hypothesis `hKnowFlip` (which is exactly what an all-witness-type RBR knowledge soundness
supplies), and the proven content is the event-implication core plus its assembly into
`rbrSoundness`.

No `sorry`/`admit`; the only residual is the named hypothesis `hKnowFlip` (universal-witness-type
per-round knowledge-flip bound).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

noncomputable section

namespace Verifier.RoundByRound

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Plain RBR flip ⟹ knowledge RBR flip (pointwise).**

Let `kSF` be a knowledge state function with extractor `extractor`, and let
`sf := kSF.toStateFunction` be its induced plain state function (`sf m stmtIn tr = ∃ w,
kSF m stmtIn tr w`).  At any fixed prefix `(transcript, challenge)`, the plain soundness flip event

```
¬ sf i.castSucc stmtIn transcript ∧ sf i.succ stmtIn (transcript.concat challenge)
```

implies the knowledge soundness flip event

```
∃ witMid, ¬ kSF i.castSucc stmtIn transcript (extractor.extractMid i stmtIn (transcript.concat
  challenge) witMid) ∧ kSF i.succ stmtIn (transcript.concat challenge) witMid.
```

The witness `witMid` is taken from the plain event's second conjunct; the plain event's first
conjunct `¬ ∃ w, kSF i.castSucc … w` kills *every* witness in the `i.castSucc` slot, in particular
`extractor.extractMid … witMid`. -/
theorem toStateFunctionFlip_imp_knowledgeFlip
    {StmtOut : Type}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
    (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i)
    (h : ¬ (KnowledgeStateFunction.toStateFunction init impl kSF)
          i.1.castSucc stmtIn transcript ∧
        (KnowledgeStateFunction.toStateFunction init impl kSF)
          i.1.succ stmtIn (transcript.concat challenge)) :
    ∃ witMid,
      ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
        kSF i.1.succ stmtIn (transcript.concat challenge) witMid := by
  obtain ⟨hNot, hSucc⟩ := h
  -- `hSucc : ∃ w, kSF i.succ (tr.concat chal) w`; take that witness.
  obtain ⟨witMid, hWit⟩ := hSucc
  refine ⟨witMid, ?_, hWit⟩
  -- `hNot : ¬ ∃ w, kSF i.castSucc tr w`, so no witness lands in the `i.castSucc` slot.
  intro hContra
  exact hNot ⟨_, hContra⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **No-log soundness block = `proj ∘ map` of the with-log knowledge block.**

The `rbrSoundness` flip-probability is computed over the block that runs `runToRound` (no query log)
and returns `(transcript, challenge)`; the `rbrKnowledgeSoundness` flip-probability is computed over
the block that runs `runWithLogToRound` (with query log) and returns `(transcript, challenge, log)`.
Since `Prod.fst <$> runWithLogToRound = runToRound` (`runWithLogToRound_discard_log_eq_runToRound`)
and the returned `(transcript, challenge)` does not depend on the log, the *no-log* block is exactly
the with-log block post-composed with the projection `(t, c, l) ↦ (t, c)`.  This is the
distributional identity that lets `probEvent_map` transport the soundness flip event onto the
knowledge block, where the pointwise implication
`toStateFunctionFlip_imp_knowledgeFlip` then applies. -/
theorem noLogBlock_eq_proj_map_withLogBlock
    {StmtOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : pSpec.ChallengeIdx) (stmtIn : StmtIn) (witIn : WitIn) :
    (do
      let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
      let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
      return (transcript, challenge))
    = (fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ) => (x.1, x.2.1)) <$>
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return (transcript, challenge, proveQueryLog)) := by
  rw [← Prover.runWithLogToRound_discard_log_eq_runToRound]
  simp only [map_bind, map_pure, bind_map_left]

/-- **Per-round plain flip probability ≤ per-round knowledge flip probability.**

For a fixed prover, initial statement/witness, and challenge round `i`, the `rbrSoundness` flip
probability (over the no-log `runToRound` block, with the induced plain state function
`kSF.toStateFunction`) is bounded by the `rbrKnowledgeSoundness` flip probability (over the with-log
`runWithLogToRound` block, with `kSF`).

The proof rewrites the no-log block as `proj <$> (with-log block)`
(`noLogBlock_eq_proj_map_withLogBlock`), hoists the `Functor.map` out through `simulateQ`/`run'`, and
applies `probEvent_map` to land on the with-log distribution; there the pointwise event implication
`toStateFunctionFlip_imp_knowledgeFlip` plus `probEvent_mono` finishes. -/
theorem plainFlipProb_le_knowledgeFlipProb
    {StmtOut PWitIn PWitOut : Type}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (stmtIn : StmtIn) (witIn : PWitIn)
    (prover : Prover oSpec StmtIn PWitIn StmtOut PWitOut pSpec)
    (i : pSpec.ChallengeIdx) :
    Pr[fun ⟨transcript, challenge⟩ =>
        ¬ (KnowledgeStateFunction.toStateFunction init impl kSF)
            i.1.castSucc stmtIn transcript ∧
          (KnowledgeStateFunction.toStateFunction init impl kSF)
            i.1.succ stmtIn (transcript.concat challenge)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
            return (transcript, challenge))).run' (← init)]
    ≤
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
            return (transcript, challenge, proveQueryLog))).run' (← init)] := by
  -- Reduce to a per-initial-state bound, then transport the event onto the with-log distribution.
  simp only [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun s => ?_
  refine mul_le_mul' le_rfl ?_
  -- Rewrite the no-log block as `proj <$> with-log block`, hoist the map through simulateQ/run',
  -- then transport *both* events onto the common with-log distribution `(simulateQ … ).run s`,
  -- where the pointwise implication finishes via `probEvent_mono`.
  rw [noLogBlock_eq_proj_map_withLogBlock prover i stmtIn witIn,
    simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    probEvent_map, probEvent_map]
  refine probEvent_mono fun x _ hx => ?_
  obtain ⟨⟨transcript, challenge, log⟩, st⟩ := x
  exact toStateFunctionFlip_imp_knowledgeFlip kSF i stmtIn transcript challenge hx

/-- **Generic weakening: RBR knowledge soundness ⟹ RBR (plain) soundness.**

`Verifier.rbrSoundness` quantifies over *arbitrary* prover witness types `WitIn'`/`WitOut'`, while a
`KnowledgeStateFunction` `kSF` is tied to the fixed relation witness types.  The honest bridge takes,
as the named hypothesis `hKnowFlip`, the per-round knowledge-flip bound *for every prover witness
type* — exactly the all-witness-type form of the `rbrKnowledgeSoundness` per-round bound (the
knowledge-flip event references only `kSF`/`extractor`, so it is well-typed against any prover witness
type).  Given that, this theorem assembles plain `rbrSoundness` with state function
`kSF.toStateFunction`: for every prover witness type the plain flip probability is `≤` the knowledge
flip probability (`plainFlipProb_le_knowledgeFlipProb`), which `hKnowFlip` bounds by the error.

This is the generic `rbrKnowledgeSoundness → rbrSoundness` weakening, with the only residual being the
universal-witness-type per-round bound `hKnowFlip`. -/
theorem rbrSoundness_of_knowledgeFlip
    {StmtOut : Type}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrError : pSpec.ChallengeIdx → ℝ≥0)
    (hKnowFlip : ∀ (WitIn' WitOut' : Type) (stmtIn : StmtIn) (witIn' : WitIn')
        (prover : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec) (i : pSpec.ChallengeIdx),
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
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ rbrError i) :
    verifier.rbrSoundness init impl relIn.language relOut.language rbrError := by
  refine ⟨KnowledgeStateFunction.toStateFunction init impl kSF, ?_⟩
  intro stmtIn _ WitIn' WitOut' witIn' prover i
  exact le_trans
    (plainFlipProb_le_knowledgeFlipProb kSF stmtIn witIn' prover i)
    (hKnowFlip WitIn' WitOut' stmtIn witIn' prover i)

/-- **Oracle-verifier specialization of the generic weakening.**

`OracleVerifier.rbrSoundness`/`rbrKnowledgeSoundness` are *definitionally* the corresponding
`toVerifier` notions, so the generic plain-from-knowledge weakening applies verbatim to an
oracle verifier `V` once the per-round, all-prover-witness-type knowledge-flip bound `hKnowFlip` is
supplied for a chosen knowledge state function `kSF`. -/
theorem oracleVerifier_rbrSoundness_of_knowledgeFlip
    {StmtOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
    {V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec WitMid}
    (kSF : V.toVerifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrError : pSpec.ChallengeIdx → ℝ≥0)
    (hKnowFlip : ∀ (PWitIn PWitOut : Type) (stmtIn : StmtIn × ∀ i, OStmtIn i) (witIn' : PWitIn)
        (prover : Prover oSpec (StmtIn × ∀ i, OStmtIn i) PWitIn
          (StmtOut × ∀ i, OStmtOut i) PWitOut pSpec) (i : pSpec.ChallengeIdx),
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
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ rbrError i) :
    V.rbrSoundness init impl relIn.language relOut.language rbrError :=
  rbrSoundness_of_knowledgeFlip kSF rbrError hKnowFlip

end Verifier.RoundByRound

end

#print axioms Verifier.RoundByRound.rbrSoundness_of_knowledgeFlip
#print axioms Verifier.RoundByRound.plainFlipProb_le_knowledgeFlipProb
#print axioms Verifier.RoundByRound.toStateFunctionFlip_imp_knowledgeFlip
#print axioms Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip
