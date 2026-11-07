/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.Implications
import ArkLib.OracleReduction.Security.GuardedBridges

/-!
# Conditional downstream security bridges

The canonical security definitions count extractor failure as a bad event and allow arbitrary
private prover inputs. The former `knowledgeSoundness_vacuous` claim and its unconditional
round-by-round corollary relied on the retired convention that discarded extraction failure;
they are intentionally retired. `Security.Implications` owns the round-by-round knowledge to
plain soundness implication, and `Security.GuardedBridges` owns the guarded worst-case bridge.

The additional full-run seam and marginal transport predicates below remain explicit hypotheses.
They quantify over arbitrary private prover inputs, matching canonical knowledge soundness. Their
conditional bridge certifies the specified pure backward-fold extractor. No fresh-state seam or
marginal transport is assumed implicitly.
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
    probEvent (p) (do (simulateQ so (f <$> ma)).run' (← init))
      = probEvent (p ∘ f) (do (simulateQ so ma).run' (← init)) := by
  rw [run'_init_map]
  exact prEvent_map _ _ _

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
realized transcript (`chainWit`), and apply `extractIn`.  It is deterministic, never fails,
and ignores the query logs. -/
def toStraightline (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) :
    Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  fun stmtIn witOut tr _ _ =>
    pure (E.extractIn stmtIn (E.chainWit stmtIn tr (E.extractOut stmtIn tr witOut) 0))

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
def knowledgeBaseRun {Aux : Type}
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (prover : Prover oSpec StmtIn Aux StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : Aux) :
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
  ∀ (Aux : Type) (stmtIn : StmtIn) (witIn : Aux)
    (prover : Prover oSpec StmtIn Aux StmtOut WitOut pSpec) x,
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
  ∀ (Aux : Type) (stmtIn : StmtIn) (witIn : Aux)
    (prover : Prover oSpec StmtIn Aux StmtOut WitOut pSpec) (i : pSpec.ChallengeIdx),
    probEvent (fun o => o.elim False (kSFFlip init impl E kSF stmtIn i)) (knowledgeBaseRun init impl verifier prover stmtIn witIn) ≤
      probEvent (fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (E.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid) (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init))

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
    (hNotIn : (stmtIn, E.extractIn stmtIn (E.chainWit stmtIn tr wLast 0)) ∉ relIn)
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
    refine hNotIn (kSF.toFun_empty stmtIn (E.chainWit stmtIn tr wLast 0) ?_)
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
    (hBound : ∀ (Aux : Type) (stmtIn : StmtIn) (witIn : Aux)
      (prover : Prover oSpec StmtIn Aux StmtOut WitOut pSpec) (i : pSpec.ChallengeIdx),
      probEvent (fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (E.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid) (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)) ≤ ε i) :
    verifier.knowledgeSoundnessWith init impl relIn relOut E.toStraightline (∑ i, ε i) := by
  classical
  intro Aux stmtIn witIn prover
  show probEvent (fun (y : StmtIn × Option WitIn × StmtOut × WitOut) =>
      (∀ w ∈ y.2.1, (y.1, w) ∉ relIn) ∧ (y.2.2.1, y.2.2.2) ∈ relOut) (OptionT.mk do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (OptionT.run (do
          let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
            ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
          let extractedWitIn ← liftM
            (E.toStraightline stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
          return (stmtIn, extractedWitIn, stmtOut, witOut)))).run' (← init)) ≤ _
  rw [StateFunction.probEvent_optionT_mk_eq_elim]
  -- Step 1: the literal knowledge game is the deterministic extraction post-processing of the
  -- logged base run.
  have hexec : (do
        let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
          ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
        let extractedWitIn ← liftM
          (E.toStraightline stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
        return (stmtIn, extractedWitIn, stmtOut, witOut))
      = (fun x : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) ×
            QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec =>
          (stmtIn,
            some (E.extractIn stmtIn (E.chainWit stmtIn x.1.1.1 (E.extractOut stmtIn x.1.1.1 x.1.1.2.2) 0)),
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
      have hlast := hAccept Aux stmtIn witIn prover x ho hRelOut
      obtain ⟨i, witMid, h1, h2⟩ := chainWit_crossing init impl E kSF stmtIn x.1.1.1
        (E.extractOut stmtIn x.1.1.1 x.1.1.2.2) (hNotIn _ rfl) hlast
      exact ⟨i, witMid, h1, h2⟩
  · -- per-round: transport to the round-by-round game, then apply the per-round bound
    rw [ENNReal.ofNNReal_finsetSum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact le_trans (hTransport Aux stmtIn witIn prover i) (hBound Aux stmtIn witIn prover i)

/-- The canonical guarded worst-case bridge supplies ordinary knowledge soundness with the
sum of the round budgets. Unlike the retired fixed-private-input formulation, this exposes the
execution guard and fixed-prefix bound required by the canonical security game. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine
    (G : verifier.GuardedForm) {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundnessWorstCase init impl relIn relOut ε) :
    verifier.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  G.knowledgeSoundness_of_rbrKnowledgeSoundnessWorstCase h

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

/-! The round-by-round knowledge-to-soundness theorem is imported from the canonical
`Security.Implications` owner; the prover adapters above remain available to downstream callers. -/

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
        probEvent (fun (x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut) => x.2 ∈ langOut) (OptionT.mk do
              (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
                (OptionT.run ((Reduction.mk prover verifier).run stmtIn witIn))).run'
                (← init)) ≤
          ∑ i : pSpec.ChallengeIdx,
            probEvent (fun (p : pSpec.Transcript i.1.castSucc × pSpec.Challenge i) =>
              ¬ sf i.1.castSucc stmtIn p.1 ∧ sf i.1.succ stmtIn (p.1.concat p.2)) (do
              (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
                (do
                  let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
                  let challenge ← liftComp (pSpec.getChallenge i) _
                  return (transcript, challenge))).run' (← init))) :
    verifier.soundness init impl langIn langOut
      (∑ i : pSpec.ChallengeIdx, rbrSoundnessError i) := by
  classical
  obtain ⟨sf, hPerRound⟩ := hRbr
  intro WitIn WitOut witIn prover stmtIn hStmtIn
  refine le_trans (hMarginal sf WitIn WitOut witIn prover stmtIn hStmtIn) ?_
  rw [ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_le_sum fun i _ => hPerRound stmtIn hStmtIn WitIn WitOut witIn prover i


end Verifier

/-! ## Axiom audit -/

#print axioms Verifier.knowledgeSoundness_error_mono
#print axioms Extractor.RoundByRound.chainWit
#print axioms Extractor.RoundByRound.toStraightline
#print axioms Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine_of_marginal
#print axioms Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_genuine
#print axioms Prover.deWitness_runToRound
#print axioms Prover.deWitness_runWithLogToRound
#print axioms Verifier.rbrKnowledgeSoundness_implies_rbrSoundness
#print axioms Verifier.rbrSoundness_implies_soundness_of_marginal

end
