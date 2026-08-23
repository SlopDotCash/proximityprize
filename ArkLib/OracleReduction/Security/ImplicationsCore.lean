/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Implications between security notions (core implications)

This file proves the implications between the security notions defined in
`Security/Basic.lean` and `Security/RoundByRound.lean` (the "Implications Between Security
Notions" lattice from the blueprint):

* round-by-round knowledge soundness ⟹ (straightline) knowledge soundness
  (`Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` — but see the ⚠ VACUITY NOTE
  below — and the *genuine*, extractor-exhibiting version
  `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal`);
* round-by-round knowledge soundness ⟹ round-by-round soundness
  (`Verifier.rbrKnowledgeSoundness_implies_rbrSoundness`);
* round-by-round soundness ⟹ soundness, conditional on the marginal-domination residual
  (`Verifier.rbrSoundness_implies_soundness_of_marginal`);
* knowledge soundness ⟹ soundness: **documented as open**; the literal statement is *false*
  under the current definitions (see the final section of this file for the three obstructions
  and the proposed honest variant).

## ⚠ VACUITY NOTE: the scalar `knowledgeSoundness` definition is trivially satisfiable

`Extractor.Straightline` (`Security/Basic.lean`, around line 271) returns an
`OptionT (OracleComp oSpec) WitIn`, so the always-failing extractor
`fun _ _ _ _ _ => failure` is a legal straightline extractor.  The knowledge game in
`Verifier.knowledgeSoundness` (`Security/Basic.lean`, around line 357) *binds* the extractor's
output inside the measured `OptionT` computation, and `probEvent` over an `OptionT` computation
does **not** count failures toward the event (see
`Verifier.StateFunction.probEvent_optionT_mk_eq_elim` in `Security/RoundByRound.lean`: the
event is `o.elim False p`, which is `False` on `none`).  Consequently **every** verifier
satisfies `knowledgeSoundness` with error `0`, witnessed by the failing extractor
(`Verifier.knowledgeSoundness_vacuous` below makes this explicit).

In the literature, an extraction *failure* makes the knowledge game's bad event *true* (the
extractor must succeed whenever the verifier accepts); the current Lean definition instead
silently drops failing runs.  This is a definitional porting bug that should eventually be
repaired (e.g. by scoring `(stmtOut, witOut) ∈ relOut ∧ (extraction failed ∨ extracted ∉ relIn)`
as the bad event).  Until then:

* `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` (the statement consumed by
  `ProofSystem/Binius/FRIBinius/General.lean`) is proven *honestly but vacuously* via the
  failing extractor — the proof does not use the round-by-round hypothesis at all;
* the *genuine* mathematical content (the bound for the real, fold-of-`extractMid` extractor)
  is `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal`, stated
  so that the exhibited extractor is `Extractor.RoundByRound.toStraightline` and the bound is
  proved for *that* extractor, conditional on two named measure-theoretic residuals (see below).

## The two named residuals of the genuine implication

The genuine `rbrKnowledgeSoundness → knowledgeSoundness` proof has the same structure as the
`rbrSoundness → soundness` bridge in
`ProofSystem/Logup/Security/{RbrToSoundBridge,MarginalBridgeProof}.lean` (generic theorems
which are misfiled under `Logup` and should be re-homed next to this file; they could not be
imported in this change because their compiled artifacts are not part of the core `Security`
build):

1. `Verifier.KnowledgeAcceptLast` — the *fresh-init seam*: on the support of the (logged) full
   run, a prover output accepted by the output relation forces the knowledge state function at
   the last round.  This is the knowledge twin of the `toFun_full` seam in
   `Verifier.marginalBridge_holds`: `KnowledgeStateFunction.toFun_full` only constrains
   verifier runs started from a *fresh* `init` sample, while the full run threads the
   post-prover implementation state into the verifier, so this residual is genuinely
   conditional (for state-mutating `impl` the unconditional statement is **false**; see the
   counterexample documented at `ProofSystem/Logup/Security/MarginalBridgeProof.lean`, lines
   20–31).  It is dischargeable for honest implementations (state-preserving / value-blind
   `impl`, via `OptionTStateT.addLift_state_preserving` and the state-independence of
   `evalDist`), exactly as in `Verifier.marginalBridge_holds`.

2. `Verifier.KnowledgeFlipTransport` — the *per-round marginal transport*: the probability of
   the round-`i` flip event along the realized full-run transcript is dominated by the
   round-by-round game's flip probability (the game that runs the prover only up to round `i`
   and samples a fresh challenge).  This is the knowledge twin of
   `Verifier.fullRun_flip_marginal_le_rbrGameFlipProb`
   (`ProofSystem/Logup/Security/MarginalBridgeProof.lean`), whose proof is unconditional but
   relies on the `continueFromTo` trailing-drop machinery for the *unlogged* run; the logged
   (`runWithLog`) analogue needed here is left as this named residual.

Everything else — the extractor fold, the first-crossing pigeonhole on the realized transcript
(`false` at round `0` via `toFun_empty`, `true` at the last round via the seam, no flip at
prover rounds via `toFun_next`), the union bound over challenge rounds, and the error
summation — is proven below, axiom-clean.

## Technique summary

Per-round bounds are consumed/produced against the *literal* round-by-round games by event
implication (`probEvent_mono`) and program-level `map` transport (`simulateQ_map`,
`StateT.run'`/`map` commutation, `probEvent_map`), never by unfolding the run; the
combinatorial core is `Verifier.StateFunction.exists_challenge_flip_of_false_zero_true_last`
plus the union bound `Verifier.StateFunction.probEvent_le_sum_of_imp_exists`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

section Plumbing

variable {ι' : Type} {spec : OracleSpec ι'}

/-- **`map` transport for the standard game shape.**  Mapping the measured oracle computation by
a pure post-processing function `f` commutes with `simulateQ`, `StateT.run'`, and the
initial-state bind.  This is the reusable plumbing step for the game-alignment arguments in this
file (log elimination, extractor inlining). -/
private theorem run'_init_map {α β : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (ma : OracleComp spec α) (f : α → β) :
    (do (simulateQ so (f <$> ma)).run' (← init))
      = f <$> (do (simulateQ so ma).run' (← init)) := by
  rw [map_bind]
  refine bind_congr fun s => ?_
  rw [simulateQ_map]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]

/-- Event-probability form of `run'_init_map`. -/
private theorem probEvent_run'_init_map {α β : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (ma : OracleComp spec α) (f : α → β)
    (p : β → Prop) :
    Pr[p | do (simulateQ so (f <$> ma)).run' (← init)]
      = Pr[p ∘ f | do (simulateQ so ma).run' (← init)] := by
  rw [run'_init_map, probEvent_map]

/-- Generic first-projection/bind commutation: consuming only the first component of a
mapped first stage equals consuming the first component of the unmapped stage.  (Stated over a
generic lawful monad; the higher-order pattern `f` lets `exact` instantiate the tuple shape.) -/
private lemma bind_fst_map_eq {m' : Type → Type} [Monad m'] [LawfulMonad m']
    {A B C D : Type} (w : m' (A × B)) (kc : m' C) (f : A → C → D) :
    ((Prod.fst <$> w) >>= fun p => kc >>= fun c => pure (f p c))
      = w >>= fun a => kc >>= fun c => pure (f a.1 c) := by
  simp only [bind_map_left]

end Plumbing

namespace Verifier

/-! ## Error monotonicity (consumed by `ProofSystem/Binius/FRIBinius/General.lean`) -/

/-- **Knowledge-soundness error monotonicity** (hypothesis-first restatement of
`Verifier.knowledgeSoundness.mono_error`, in the argument order consumed by
`ProofSystem/Binius/FRIBinius/General.lean`). -/
theorem knowledgeSoundness_error_mono
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (hε : knowledgeError₁ ≤ knowledgeError₂)
    (h : verifier.knowledgeSoundness init impl relIn relOut knowledgeError₁) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError₂ :=
  knowledgeSoundness.mono_error init impl h hε

/-! ## The vacuity of `knowledgeSoundness`, made explicit -/

/-- ⚠ VACUITY NOTE.  **Every verifier satisfies `knowledgeSoundness` at error `0`**, witnessed
by the always-failing straightline extractor.  This is *not* a meaningful security statement: it
exposes the definitional weakness documented in the module docstring (`Extractor.Straightline`
is `OptionT`-valued and `probEvent` does not count failures, so an extractor that always fails
makes the knowledge game's bad event have probability `0`).  It is recorded here (a) to make the
definitional bug impossible to overlook and (b) as the honest engine behind the literal
statement `rbrKnowledgeSoundness_implies_knowledgeSoundness` below. -/
theorem knowledgeSoundness_vacuous
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.knowledgeSoundness init impl relIn relOut 0 := by
  refine ⟨fun _ _ _ _ _ => failure, fun stmtIn witIn prover => ?_⟩
  show Pr[fun (y : StmtIn × WitIn × StmtOut × WitOut) =>
      (y.1, y.2.1) ∉ relIn ∧ (y.2.2.1, y.2.2.2) ∈ relOut |
    OptionT.mk do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (OptionT.run (do
          let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
            ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
          let extractedWitIn ← (failure : OptionT (OracleComp oSpec) WitIn)
          return (stmtIn, extractedWitIn, stmtOut, witOut)))).run' (← init)] ≤ _
  refine le_of_eq ?_
  rw [ENNReal.coe_zero, StateFunction.probEvent_optionT_mk_eq_elim]
  -- The second stage of the `OptionT` bind is the failing extractor, so every run returns
  -- `none`: the game is the constant-`none` post-processing of the logged run.
  have hrun : OptionT.run (do
        let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
          ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
        let extractedWitIn ← (failure : OptionT (OracleComp oSpec) WitIn)
        return (stmtIn, extractedWitIn, stmtOut, witOut))
      = (fun _ => (none : Option (StmtIn × WitIn × StmtOut × WitOut))) <$>
        OptionT.run ((Reduction.mk prover verifier).runWithLog stmtIn witIn) := by
    rw [map_eq_bind_pure_comp, OptionT.run_bind]
    simp only [Option.elimM]
    refine bind_congr fun o => ?_
    cases o with
    | none => simp
    | some x =>
      obtain ⟨⟨⟨tr, _pOut, wOut⟩, sOut⟩, pLog, vLog⟩ := x
      simp only [OracleComp.failure_def, OptionT.fail, OptionT.run, OptionT.mk]
      rfl
  rw [hrun, probEvent_run'_init_map init (impl.addLift challengeQueryImpl),
    probEvent_eq_zero_iff]
  intro o _
  exact fun h => h

/-! ## I4 (literal statement): `rbrKnowledgeSoundness → knowledgeSoundness` -/

/-- **Round-by-round knowledge soundness implies (straightline) knowledge soundness** with the
union-bound error `∑ i, rbrKnowledgeError i` — *as literally stated*.

⚠ VACUITY NOTE.  Under the current definition of `Verifier.knowledgeSoundness` this statement
is true for a degenerate reason: the conclusion is *always* satisfiable via the always-failing
`OptionT` extractor (see `knowledgeSoundness_vacuous` and the module docstring), so this proof
does **not** use the round-by-round hypothesis.  The statement is kept in this exact shape
because it is the one consumed by `ProofSystem/Binius/FRIBinius/General.lean`; the *genuine*
implication — where the exhibited extractor is the real fold of the round-by-round extractor
and the bound is proven for it — is
`rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal` below. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError →
      verifier.knowledgeSoundness init impl relIn relOut (∑ i, rbrKnowledgeError i) :=
  fun _ => knowledgeSoundness_error_mono init impl (zero_le _)
    (knowledgeSoundness_vacuous init impl relIn relOut verifier)

end Verifier

/-! ## The genuine straightline extractor from a round-by-round extractor -/

namespace Extractor.RoundByRound

variable {WitMid : Fin (n + 1) → Type}

/-- **The chain of intermediate witnesses along a fixed full transcript.**  Starting from a
last-round intermediate witness `wLast` and folding `extractMid` downwards along the prefixes of
the full transcript `tr`, this produces the intermediate witness at every round `m`. -/
def chainWit (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmtIn : StmtIn) (tr : FullTranscript pSpec) (wLast : WitMid (.last n)) :
    (m : Fin (n + 1)) → WitMid m :=
  Fin.reverseInduction wLast
    (fun j w => E.extractMid j stmtIn (tr.take j.succ.val j.succ.is_le) w)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp]
lemma chainWit_last (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmtIn : StmtIn) (tr : FullTranscript pSpec) (wLast : WitMid (.last n)) :
    E.chainWit stmtIn tr wLast (.last n) = wLast :=
  Fin.reverseInduction_last ..

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp]
lemma chainWit_castSucc (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmtIn : StmtIn) (tr : FullTranscript pSpec) (wLast : WitMid (.last n)) (j : Fin n) :
    E.chainWit stmtIn tr wLast j.castSucc
      = E.extractMid j stmtIn (tr.take j.succ.val j.succ.is_le)
          (E.chainWit stmtIn tr wLast j.succ) :=
  Fin.reverseInduction_castSucc ..

/-- **The genuine straightline extractor obtained from a round-by-round extractor**: seed the
last-round intermediate witness with `extractOut`, fold `extractMid` down to round `0` along the
realized transcript (`chainWit`), and transport along `eqIn`.  It is deterministic, never fails,
and ignores the query logs. -/
def toStraightline (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) :
    Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  fun stmtIn witOut tr _ _ =>
    pure (cast E.eqIn (E.chainWit stmtIn tr (E.extractOut stmtIn tr witOut) 0))

end Extractor.RoundByRound

namespace Verifier

/-! ## I4 (genuine form): the real extractor, conditional on the two transport residuals -/

section GenuineKnowledge

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {WitMid : Fin (n + 1) → Type}

/-- **The raw (logged) knowledge run**: the full reduction execution with query logging,
simulated against the shared-oracle implementation and averaged over the initial state.  This is
the base random variable of the knowledge game: the literal `knowledgeSoundness` game is a pure
post-processing (`Option.map`) of it once the extractor is deterministic. -/
@[reducible]
def knowledgeBaseRun
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    ProbComp (Option (((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) ×
      QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec)) :=
  do (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (OptionT.run ((Reduction.mk prover verifier).runWithLog stmtIn witIn))).run' (← init)

/-- **The round-`i` knowledge-state-function flip event along a realized full-run output** (the
event whose probability the round-by-round game bounds, transported to the full run): there is
an intermediate witness for which the knowledge state function is *true* at round `i.succ` on
the realized prefix-plus-challenge, yet *false* at round `i` on the realized prefix after
applying `extractMid`. -/
def kSFFlip (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (stmtIn : StmtIn) (i : pSpec.ChallengeIdx)
    (x : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) ×
      QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) : Prop :=
  ∃ witMid,
    ¬ kSF.toFun i.1.castSucc stmtIn (x.1.1.1.take i.1.castSucc.val i.1.castSucc.is_le)
        (E.extractMid i.1 stmtIn
          (Transcript.concat (x.1.1.1 i.1)
            (x.1.1.1.take i.1.castSucc.val i.1.castSucc.is_le)) witMid) ∧
      kSF.toFun i.1.succ stmtIn
        (Transcript.concat (x.1.1.1 i.1)
          (x.1.1.1.take i.1.castSucc.val i.1.castSucc.is_le)) witMid

/-- **Residual 1 (fresh-init seam).**  On the support of the logged full run, an output accepted
by the output relation (with the prover's output witness) forces the knowledge state function at
the last round on the realized transcript, with the `extractOut`-seeded witness.

This is the knowledge twin of the `toFun_full` seam discharged (for the plain-soundness bridge)
in `Verifier.marginalBridge_holds` (`ProofSystem/Logup/Security/MarginalBridgeProof.lean`): it
follows from `KnowledgeStateFunction.toFun_full` whenever the implementation is state-preserving
and value-blind (the post-prover state is then interchangeable with a fresh `init` sample), and
it is **false** for general state-mutating implementations (same counterexample as documented in
that file, lines 20–31). -/
def KnowledgeAcceptLast (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut E) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) x,
    some x ∈ support (knowledgeBaseRun init impl verifier prover stmtIn witIn) →
    (x.1.2, x.1.1.2.2) ∈ relOut →
    kSF.toFun (.last n) stmtIn x.1.1.1 (E.extractOut stmtIn x.1.1.1 x.1.1.2.2)

/-- **Residual 2 (per-round marginal transport).**  The probability of the round-`i` flip event
along the realized full run is dominated by the round-by-round game's flip probability (prover
run only up to round `i`, fresh challenge).  This is the knowledge twin of the unconditional
trailing-drop core `Verifier.fullRun_flip_marginal_le_rbrGameFlipProb`
(`ProofSystem/Logup/Security/MarginalBridgeProof.lean`); the proof there is for the *unlogged*
run, and the `runWithLog` analogue required here is precisely this statement. -/
def KnowledgeFlipTransport (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut E) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (i : pSpec.ChallengeIdx),
    Pr[fun o => o.elim False (kSFFlip init impl E kSF stmtIn i) |
        knowledgeBaseRun init impl verifier prover stmtIn witIn] ≤
      Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (E.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **First-crossing along a realized transcript** (the combinatorial core of the genuine
implication, with no probabilistic content): if the round-`0` chain witness is bad for the input
relation while the knowledge state function holds at the last round (with the seed witness),
then the knowledge state function flips at some challenge round, in the exact shape of the
round-by-round flip event. -/
private lemma chainWit_crossing
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (stmtIn : StmtIn) (tr : FullTranscript pSpec) (wLast : WitMid (.last n))
    (hNotIn : (stmtIn, cast E.eqIn (E.chainWit stmtIn tr wLast 0)) ∉ relIn)
    (hlast : kSF.toFun (.last n) stmtIn tr wLast) :
    ∃ i : pSpec.ChallengeIdx, ∃ witMid,
      ¬ kSF.toFun i.1.castSucc stmtIn (tr.take i.1.castSucc.val i.1.castSucc.is_le)
          (E.extractMid i.1 stmtIn
            (Transcript.concat (tr i.1)
              (tr.take i.1.castSucc.val i.1.castSucc.is_le)) witMid) ∧
        kSF.toFun i.1.succ stmtIn
          (Transcript.concat (tr i.1)
            (tr.take i.1.castSucc.val i.1.castSucc.is_le)) witMid := by
  classical
  -- The crossing sequence: the knowledge state function on the realized prefixes, with the
  -- chained witnesses.
  have h0 : ¬ kSF.toFun 0 stmtIn (tr.take (0 : Fin (n + 1)).val (0 : Fin (n + 1)).is_le)
      (E.chainWit stmtIn tr wLast 0) := by
    intro hP0
    refine hNotIn ((kSF.toFun_empty stmtIn (E.chainWit stmtIn tr wLast 0)).mpr ?_)
    have hdef : ((tr.take (0 : Fin (n + 1)).val (0 : Fin (n + 1)).is_le) :
        Transcript 0 pSpec) = default := Subsingleton.elim _ _
    rw [← hdef]
    exact hP0
  have hlast' : kSF.toFun (.last n) stmtIn
      (tr.take (Fin.last n).val (Fin.last n).is_le)
      (E.chainWit stmtIn tr wLast (.last n)) := by
    have htake : ((tr.take (Fin.last n).val (Fin.last n).is_le) :
        Transcript (Fin.last n) pSpec) = tr := by
      simp only [FullTranscript.take, Fin.val_last]
      exact Fin.take_eq_self _
    rw [htake, Extractor.RoundByRound.chainWit_last]
    exact hlast
  have hPtoV : ∀ j : Fin n, pSpec.dir j = .P_to_V →
      ¬ kSF.toFun j.castSucc stmtIn (tr.take j.castSucc.val j.castSucc.is_le)
          (E.chainWit stmtIn tr wLast j.castSucc) →
      ¬ kSF.toFun j.succ stmtIn (tr.take j.succ.val j.succ.is_le)
          (E.chainWit stmtIn tr wLast j.succ) := by
    intro j hdir hnc hs
    refine hnc ?_
    rw [Extractor.RoundByRound.chainWit_castSucc, StateFunction.take_succ_eq_concat]
    refine kSF.toFun_next j hdir stmtIn (tr.take j.castSucc.val j.castSucc.is_le) (tr j)
      (E.chainWit stmtIn tr wLast j.succ) ?_
    rw [← StateFunction.take_succ_eq_concat]
    exact hs
  obtain ⟨i, hci, hsi⟩ := StateFunction.exists_challenge_flip_of_false_zero_true_last
    (fun m => kSF.toFun m stmtIn (tr.take m.val m.is_le) (E.chainWit stmtIn tr wLast m))
    h0 hlast' hPtoV
  rw [Extractor.RoundByRound.chainWit_castSucc, StateFunction.take_succ_eq_concat] at hci
  rw [StateFunction.take_succ_eq_concat] at hsi
  exact ⟨i, E.chainWit stmtIn tr wLast i.1.succ, hci, hsi⟩

/-- **The genuine `rbrKnowledgeSoundness → knowledgeSoundness` implication** (data-level form),
conditional on the two named transport residuals.

Given a round-by-round extractor `E` and knowledge state function `kSF` whose per-round flip
probabilities are bounded by `ε` (`hBound` — this is exactly the inner content of
`Verifier.rbrKnowledgeSoundness` for the data `(WitMid, E, kSF)`), the verifier satisfies
straightline knowledge soundness at the union-bound error `∑ i, ε i`, **witnessed by the
genuine extractor** `E.toStraightline` (the fold of `extractMid` along the realized transcript,
seeded by `extractOut`).

The proof is real (not vacuous): the literal knowledge game is rewritten as a pure
post-processing of the logged run (`knowledgeBaseRun`); on any accepting run whose extracted
input witness is bad, the knowledge state function is false at round `0` (by `toFun_empty`,
since the extracted witness is the round-`0` chain witness), true at the last round (by the
fresh-init seam residual `hAccept`), and cannot flip at prover rounds (by `toFun_next` and
`chainWit_castSucc`), so it must flip at some challenge round (`chainWit_crossing`); the union
bound (`probEvent_le_sum_of_imp_exists`) and the per-round transport residual `hTransport` then
bound the bad-event probability by `∑ i, ε i`. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (hAccept : KnowledgeAcceptLast init impl E kSF)
    (hTransport : KnowledgeFlipTransport init impl E kSF)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hBound : ∀ (stmtIn : StmtIn) (witIn : WitIn)
      (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (i : pSpec.ChallengeIdx),
      Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (E.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ ε i) :
    verifier.knowledgeSoundness init impl relIn relOut (∑ i, ε i) := by
  classical
  refine ⟨E.toStraightline, fun stmtIn witIn prover => ?_⟩
  show Pr[fun (y : StmtIn × WitIn × StmtOut × WitOut) =>
      (y.1, y.2.1) ∉ relIn ∧ (y.2.2.1, y.2.2.2) ∈ relOut |
    OptionT.mk do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (OptionT.run (do
          let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
            ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
          let extractedWitIn ← E.toStraightline stmtIn witOut transcript
            proveQueryLog.fst verifyQueryLog
          return (stmtIn, extractedWitIn, stmtOut, witOut)))).run' (← init)] ≤ _
  rw [StateFunction.probEvent_optionT_mk_eq_elim]
  -- Step 1: the literal knowledge game is the deterministic extraction post-processing of the
  -- logged base run.
  have hexec : (do
        let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
          ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
        let extractedWitIn ← E.toStraightline stmtIn witOut transcript
          proveQueryLog.fst verifyQueryLog
        return (stmtIn, extractedWitIn, stmtOut, witOut))
      = (fun x : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) ×
            QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec =>
          (stmtIn,
            cast E.eqIn (E.chainWit stmtIn x.1.1.1 (E.extractOut stmtIn x.1.1.1 x.1.1.2.2) 0),
            x.1.2, x.1.1.2.2)) <$>
        (Reduction.mk prover verifier).runWithLog stmtIn witIn := by
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun x => ?_
    obtain ⟨⟨⟨tr, _pOut, wOut⟩, sOut⟩, pLog, vLog⟩ := x
    simp only [Extractor.RoundByRound.toStraightline]
    rfl
  rw [hexec, OptionT.run_map, probEvent_run'_init_map init (impl.addLift challengeQueryImpl)]
  -- Step 2: union bound over challenge rounds via the first-crossing pigeonhole.
  refine le_trans (StateFunction.probEvent_le_sum_of_imp_exists _ _
    (fun (i : pSpec.ChallengeIdx) o => o.elim False (kSFFlip init impl E kSF stmtIn i))
    ?_) ?_
  · -- the bad event forces a flip at some challenge round, on the support
    intro o ho hq
    cases o with
    | none => exact hq.elim
    | some x =>
      obtain ⟨hNotIn, hRelOut⟩ := hq
      have hlast := hAccept stmtIn witIn prover x ho hRelOut
      obtain ⟨i, witMid, h1, h2⟩ := chainWit_crossing init impl E kSF stmtIn x.1.1.1
        (E.extractOut stmtIn x.1.1.1 x.1.1.2.2) hNotIn hlast
      exact ⟨i, witMid, h1, h2⟩
  · -- per-round: transport to the round-by-round game, then apply the per-round bound
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact le_trans (hTransport stmtIn witIn prover i) (hBound stmtIn witIn prover i)

/-- **The genuine implication, packaged**: from `rbrKnowledgeSoundness` (whose data satisfies
the two transport residuals), conclude `knowledgeSoundness` at the union-bound error, with the
exhibited extractor being `E.toStraightline` for the round-by-round extractor `E` supplied by
the hypothesis.  See `rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal` for
the data-level statement (which makes the genuine extractor visible in the conclusion). -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hRbr : verifier.rbrKnowledgeSoundness init impl relIn relOut ε)
    (hAccept : ∀ (WitMid : Fin (n + 1) → Type)
      (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
      (kSF : verifier.KnowledgeStateFunction init impl relIn relOut E),
      KnowledgeAcceptLast init impl E kSF)
    (hTransport : ∀ (WitMid : Fin (n + 1) → Type)
      (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
      (kSF : verifier.KnowledgeStateFunction init impl relIn relOut E),
      KnowledgeFlipTransport init impl E kSF) :
    verifier.knowledgeSoundness init impl relIn relOut (∑ i, ε i) := by
  obtain ⟨WitMid, E, kSF, hBound⟩ := hRbr
  exact rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal init impl E kSF
    (hAccept WitMid E kSF) (hTransport WitMid E kSF) hBound

end GenuineKnowledge

end Verifier

/-! ## I3: `rbrKnowledgeSoundness → rbrSoundness` -/

namespace Prover

/-- **Witness-type adapter for provers** (interaction-only).  Re-types a prover with arbitrary
witness types `WitIn'`/`WitOut'` into one with the given witness types `WitIn`/`WitOut`, by
baking the original input witness `witIn'` into the input function and substituting an arbitrary
output witness (`OracleComp` is a bare free monad with no `failure`, so `[Nonempty WitOut]` is
needed to produce *some* output witness; the output is never consulted by the round games this
adapter serves).  The interaction behaviour (`sendMessage`, `receiveChallenge`, hence every
`runToRound` / `runWithLogToRound`) is unchanged.

This is the adapter needed because `Verifier.rbrSoundness` quantifies over provers with
*arbitrary* witness types inside the definition, while `Verifier.rbrKnowledgeSoundness` fixes
the witness types to those of the relations. -/
def deWitness {WitIn' WitOut' : Type}
    (P : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec) (witIn' : WitIn')
    (WitIn WitOut : Type) [Nonempty WitOut] :
    Prover oSpec StmtIn WitIn StmtOut WitOut pSpec where
  PrvState := P.PrvState
  input := fun x => P.input (x.1, witIn')
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge
  output := fun s => (fun out => (out.1, Classical.arbitrary WitOut)) <$> P.output s

/-- The adapter does not change the prover's partial runs: `runToRound` of the adapted prover
(on any witness of the new type) equals `runToRound` of the original prover on the baked-in
witness. -/
lemma deWitness_runToRound {WitIn' WitOut' : Type}
    (P : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec) (witIn' : WitIn')
    (WitIn WitOut : Type) [Nonempty WitOut] (i : Fin (n + 1)) (stmt : StmtIn) (w : WitIn) :
    (P.deWitness witIn' WitIn WitOut).runToRound i stmt w = P.runToRound i stmt witIn' := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih =>
    rw [runToRound_succ, runToRound_succ, ih]
    rfl

/-- `runWithLogToRound` version of `deWitness_runToRound`. -/
lemma deWitness_runWithLogToRound {WitIn' WitOut' : Type}
    (P : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec) (witIn' : WitIn')
    (WitIn WitOut : Type) [Nonempty WitOut] (i : Fin (n + 1)) (stmt : StmtIn) (w : WitIn) :
    (P.deWitness witIn' WitIn WitOut).runWithLogToRound i stmt w
      = P.runWithLogToRound i stmt witIn' := by
  unfold runWithLogToRound
  rw [deWitness_runToRound]
  rfl

end Prover

namespace Verifier

/-- **Round-by-round knowledge soundness implies round-by-round soundness** (same per-round
error, languages of the relations).

The state function is `KnowledgeStateFunction.toStateFunction` (existence of an intermediate
witness).  The per-round bound for an *arbitrary-witness-typed* prover is obtained by (a) the
pointwise event implication from the existential state-function flip to the knowledge
state-function flip (`probEvent_mono`), (b) re-typing the prover through `Prover.deWitness`
(which leaves all partial runs unchanged), and (c) re-introducing the (ignored) query log to
match the round-by-round knowledge game (`runWithLogToRound_discard_log_eq_runToRound` + `map`
transport).

The `[Nonempty WitIn]` hypothesis is genuinely required: `rbrSoundness` demands bounds for
provers over *all* witness types, while the `rbrKnowledgeSoundness` hypothesis only bounds
games that thread *some* witness of the relation's input witness type `WitIn`; if `WitIn` were
empty the hypothesis would be silent while the conclusion is not. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness [Nonempty WitIn] [Nonempty WitOut]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hRbr : verifier.rbrKnowledgeSoundness init impl relIn relOut ε) :
    verifier.rbrSoundness init impl relIn.language relOut.language ε := by
  classical
  obtain ⟨WitMid, E, kSF, hBound⟩ := hRbr
  refine ⟨kSF.toStateFunction init impl, ?_⟩
  intro stmtIn _hStmtIn WitIn' WitOut' witIn' prover i
  have w₀ : WitIn := Classical.arbitrary WitIn
  -- The per-round bound for the knowledge flip event, on this round game.
  have hMain : Pr[fun (p : pSpec.Transcript i.1.castSucc × pSpec.Challenge i) =>
      ∃ witMid,
        ¬ kSF.toFun i.1.castSucc stmtIn p.1
            (E.extractMid i.1 stmtIn (p.1.concat p.2) witMid) ∧
          kSF.toFun i.1.succ stmtIn (p.1.concat p.2) witMid |
      do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' (← init)] ≤ (ε i : ℝ≥0∞) := by
    -- Swap in the adapter prover (identical partial runs), then re-introduce the query log.
    have hinner : (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))
        = (fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
            QueryLog (oSpec + [pSpec.Challenge]ₒ) => (x.1, x.2.1)) <$> (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            (prover.deWitness witIn' WitIn WitOut).runWithLogToRound i.1.castSucc stmtIn w₀
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog)) := by
      rw [← Prover.deWitness_runToRound prover witIn' WitIn WitOut i.1.castSucc stmtIn w₀,
        ← Prover.runWithLogToRound_discard_log_eq_runToRound]
      simp only [map_bind, map_pure]
      exact bind_fst_map_eq _ _ _
    rw [hinner, probEvent_run'_init_map init (impl.addLift challengeQueryImpl)]
    exact hBound stmtIn w₀ (prover.deWitness witIn' WitIn WitOut) i
  refine le_trans (probEvent_mono ?_) hMain
  -- Pointwise event implication: an existential-state-function flip yields a knowledge flip
  -- witness (take the round-`i.succ` witness; the round-`i` negation is universal).
  rintro ⟨transcript, challenge⟩ _ ⟨hno, hyes⟩
  obtain ⟨wm, hwm⟩ := hyes
  exact ⟨wm, fun h => hno ⟨_, h⟩, hwm⟩

/-! ## I2: `rbrSoundness → soundness`, conditional on the marginal-domination residual -/

/-- **Round-by-round soundness implies plain soundness** with the union-bound error
`∑ i, rbrSoundnessError i`, **conditional** on the per-round marginal-domination residual
`hMarginal`.

⚠ The *unconditional* blueprint statement is **false** under the current definitions: a
state-mutating shared-oracle implementation can make every `StateFunction` field hold (they
only constrain *fresh-`init`* verifier runs, via `toFun_full`) while the full run accepts with
probability `1`.  See the concrete counterexample documented at
`ProofSystem/Logup/Security/MarginalBridgeProof.lean`, lines 20–31.

`hMarginal` is exactly the `Verifier.MarginalBridge` residual of
`ProofSystem/Logup/Security/RbrToSoundBridge.lean` (with the unused per-round-bound premise
dropped): for every state function, every prover and bad input statement, the full-run accept
probability is dominated by the sum over challenge rounds of the round-by-round game's flip
probabilities.  It is discharged *generically* by `Verifier.marginalBridge_holds`
(`ProofSystem/Logup/Security/MarginalBridgeProof.lean`) under the three standard honest-`impl`
side conditions (state-preserving on support / never-failing / value-blind `impl`,
dischargeable e.g. via `OptionTStateT.addLift_state_preserving`); those two generic theorems
are misfiled under `ProofSystem/Logup` and should be re-homed next to this file (they could not
be imported here because their compiled artifacts are not part of the core `Security` build).

This theorem is the thin union-bound composition: chain `hMarginal` with the per-round bounds
from `hRbr` and sum. -/
theorem rbrSoundness_implies_soundness_of_marginal
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (hRbr : verifier.rbrSoundness init impl langIn langOut rbrSoundnessError)
    (hMarginal : ∀ sf : verifier.StateFunction init impl langIn langOut,
      ∀ (WitIn WitOut : Type) (witIn : WitIn)
        (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec),
        ∀ stmtIn ∉ langIn,
        Pr[fun (x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut) => x.2 ∈ langOut |
            OptionT.mk do
              (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
                (OptionT.run ((Reduction.mk prover verifier).run stmtIn witIn))).run'
                (← init)] ≤
          ∑ i : pSpec.ChallengeIdx,
            Pr[fun (p : pSpec.Transcript i.1.castSucc × pSpec.Challenge i) =>
              ¬ sf i.1.castSucc stmtIn p.1 ∧ sf i.1.succ stmtIn (p.1.concat p.2) |
            do
              (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
                (do
                  let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
                  let challenge ← liftComp (pSpec.getChallenge i) _
                  return (transcript, challenge))).run' (← init)]) :
    verifier.soundness init impl langIn langOut
      (∑ i : pSpec.ChallengeIdx, rbrSoundnessError i) := by
  classical
  obtain ⟨sf, hPerRound⟩ := hRbr
  intro WitIn WitOut witIn prover stmtIn hStmtIn
  refine le_trans (hMarginal sf WitIn WitOut witIn prover stmtIn hStmtIn) ?_
  rw [ENNReal.coe_finset_sum]
  exact Finset.sum_le_sum fun i _ => hPerRound stmtIn hStmtIn WitIn WitOut witIn prover i

/-! ## I1: `knowledgeSoundness → soundness` — DOCUMENTED OPEN (the literal statement is false)

The blueprint implication "knowledge soundness (with error `κ < 1`) implies soundness (with
error `κ`, for the languages of the relations)" is **not provable** — indeed *false as
literally stated* — under the current definitions, for three independent reasons:

1. **Vacuity of the hypothesis** (see the ⚠ VACUITY NOTE in the module docstring and
   `knowledgeSoundness_vacuous`): every verifier satisfies `knowledgeSoundness` at error `0`
   via the always-failing `OptionT` extractor, while `soundness` is a real constraint (e.g.
   the verifier that always accepts is not sound for a non-full output language).  Hence
   `knowledgeSoundness relIn relOut V κ → soundness relIn.language relOut.language V κ'` is
   false for every `κ' < 1` at, say, the always-accepting verifier.

2. **`witOut`-vs-language mismatch**: the knowledge game's bad event tests the *prover's own*
   output witness against `relOut` (`(stmtOut, witOut) ∈ relOut`), while the soundness event
   only tests `stmtOut ∈ relOut.language = {s | ∃ w, (s, w) ∈ relOut}`.  An accepting
   soundness run need not carry a `relOut`-valid `witOut`, so the soundness event does not
   imply the knowledge event.  The honest repair is the side condition
   `∀ stmtOut witOut, stmtOut ∈ relOut.language → (stmtOut, witOut) ∈ relOut`
   (satisfied e.g. by `acceptRejectRel`-style output relations, where the witness is trivial).

3. **Witness-type rigidity** (documented at `Security/Basic.lean`, around lines 421–433):
   `soundness` quantifies over provers with arbitrary witness types inside the definition,
   while `knowledgeSoundness` fixes them to the relation's types; transporting a prover across
   witness types requires the `Prover.deWitness`-style adapter *with a non-failing output*
   (`output := fun s => (fun out => (out.1, default)) <$> P.output s`, needing
   `[Inhabited WitOut]`), since a failing output would *lower* the adapted prover's accept
   probability — the wrong direction for this implication (unlike I3, where only partial runs
   matter).

**Proposed honest variant** (statement written out; not proven here — the remaining work is
the run/`runWithLog` game alignment with the inserted extractor stage and the output-adapter
transport):

```
theorem knowledgeSoundness_implies_soundness_of_neverFails [Nonempty WitIn] [Inhabited WitOut]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {κ : ℝ≥0}
    (hRelOut : ∀ stmtOut witOut, stmtOut ∈ relOut.language → (stmtOut, witOut) ∈ relOut)
    (hKS : ∃ extr : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
      (∀ stmtIn witOut tr pLog vLog, ∃ w, extr stmtIn witOut tr pLog vLog = pure w) ∧
      <the knowledgeSoundness bound of Security/Basic.lean for extr, at error κ>) :
    verifier.soundness init impl relIn.language relOut.language κ
```

The never-failing hypothesis on the extractor closes obstruction 1 (for *this* extractor the
knowledge game does not silently drop runs), `hRelOut` closes obstruction 2, and the
`[Inhabited WitOut]` output adapter closes obstruction 3.  A definitional repair of
`knowledgeSoundness` (counting extraction failure toward the bad event) would make the
never-failing hypothesis unnecessary and is the recommended long-term fix. -/

end Verifier

/-! ## Axiom audit -/

#print axioms Verifier.knowledgeSoundness_error_mono
#print axioms Verifier.knowledgeSoundness_vacuous
#print axioms Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness
#print axioms Extractor.RoundByRound.chainWit
#print axioms Extractor.RoundByRound.toStraightline
#print axioms Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal
#print axioms Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine
#print axioms Prover.deWitness_runToRound
#print axioms Prover.deWitness_runWithLogToRound
#print axioms Verifier.rbrKnowledgeSoundness_implies_rbrSoundness
#print axioms Verifier.rbrSoundness_implies_soundness_of_marginal

end
