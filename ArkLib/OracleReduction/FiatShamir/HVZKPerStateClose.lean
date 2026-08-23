/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKKernelInfra
import ArkLib.OracleReduction.FiatShamir.HVZKLazyVerifier

/-!
# Per-state lazy coupling: assembly of the verifier leg (G3 + G4) (#116)

This file reduces the open per-`oSpec`-state coupling residual
`Reduction.canonicalFSPerStateCoupling` to a SINGLE distributional hypothesis: the
**full-transcript joint coupling** `fullTranscriptCoupling` between

* the lazy Fiat-Shamir prover run (`runToRoundFS` under `ambientProd impl + fsLazyProd`,
  from the empty cache), projected to the *reconstructed* transcript
  (`reconstruct stmt messages cache`), the prover state, and the ambient `σ`; and
* the interactive prover run (`runToRound` under `impl.addLift challengeQueryImpl`),
  projected to its full transcript, the prover state, and the ambient `σ`.

Everything else is PROVEN here:

* the canonical combined implementation `impl.addLift canonicalFSChallengeImpl` is
  *definitionally* the product implementation `ambientProd impl + fsLazyProd`
  (`addLift_canonicalFSChallengeImpl_eq_prod`, by `rfl`);
* the Fiat-Shamir verifier's transcript re-derivation collapses, on every support point of the
  lazy prover run, to `pure` of the reconstructed transcript
  (`deriveTranscriptFS_lazy_run_of_runOutput`, the ported replay lemma);
* the reconstructed transcript's message bundle is the prover's message bundle
  (`reconstruct_messages`, the G4 shape reconciliation), so the Fiat-Shamir proof
  `fun | ⟨0, _⟩ => messages` is `msgProjFS` of the reconstructed transcript;
* both residual executions (prover output + verifier verify + `OptionT` verdict plumbing) are
  *the same function* of the coupled triple `(transcript, prover state, σ)`, so the per-state
  coupling follows from the joint coupling by a support-restricted bind congruence.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]

/-! ## G1: the canonical combined implementation is the product implementation, definitionally -/

/-- The canonical lazy random-oracle challenge implementation (`OracleSpec.randomOracle`) is
*definitionally* the ported lazy caching implementation (`srChallengeQueryImpl.withCaching`). -/
theorem canonicalFSChallengeImpl_eq_lazy :
    (canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec))
      = fsChallengeLazyImpl (StmtIn := StmtIn) (pSpec := pSpec) := rfl

/-- **The canonical combined Fiat-Shamir implementation is the product implementation.** The
`addLift` of the ambient `impl` with the canonical lazy random oracle, over the product state
`σ × QueryCache`, is definitionally `ambientProd impl + fsLazyProd`: the `MonadLift` instances
lifting `StateT σ` and `StateT QueryCache` into `StateT (σ × QueryCache)` act exactly as
`extendState`/`extendStateLeft`. This lets every ported lazy-product brick apply verbatim to the
canonical implementation of `canonicalFSPerStateCoupling`. -/
theorem addLift_canonicalFSChallengeImpl_eq_prod (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (impl.addLift (canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec)) :
      QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec)
        (StateT (σ × (fsChallengeOracle StmtIn pSpec).QueryCache) ProbComp))
    = ambientProd (StmtIn := StmtIn) pSpec impl
        + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec := rfl

/-! ## G4: the reconstructed transcript's messages are the prover's messages -/

/-- Pointwise form: at every message (`P_to_V`) round below `j`, the partially reconstructed
transcript `reconstructAux` carries exactly the prover's message. -/
theorem reconstructAux_message_apply (stmt : StmtIn) (k : Fin (n + 1))
    (M : pSpec.MessagesUpTo k) (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) :
    ∀ (j : Fin (k + 1)) (a : ℕ) (ha : a < (j : ℕ)) (ha' : a < k.val)
      (hdir : pSpec.dir ⟨a, by omega⟩ = Direction.P_to_V),
      reconstructAux (StmtIn := StmtIn) stmt k M cache j ⟨a, ha⟩
        = M ⟨⟨a, ha'⟩, hdir⟩ := by
  intro j
  induction j using Fin.induction with
  | zero => exact fun a ha _ _ => absurd ha (by simp)
  | succ i ih =>
    intro a ha ha' hdir
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using ha) with hlt | heq
    · -- strict prefix index: both `concat` branches restrict to the previous round
      rcases hD : pSpec.dir (i.castLE (by omega)) with _ | _
      · rw [reconstructAux_succ_ptov (StmtIn := StmtIn) stmt k M cache i hD]
        exact (Fin.snoc_castSucc _ _ ⟨a, hlt⟩).trans (ih a hlt ha' hdir)
      · rw [reconstructAux_succ_vtop (StmtIn := StmtIn) stmt k M cache i hD]
        exact (Fin.snoc_castSucc _ _ ⟨a, hlt⟩).trans (ih a hlt ha' hdir)
    · -- the just-appended index: must be a P_to_V round, and the appended value is the message
      subst heq
      rcases hD : pSpec.dir (i.castLE (by omega)) with _ | _
      · rw [reconstructAux_succ_ptov (StmtIn := StmtIn) stmt k M cache i hD]
        exact Fin.snoc_last _ _
      · exact absurd (hdir.symm.trans hD) (by decide)

/-- **G4 shape reconciliation.** The full reconstructed transcript's message bundle is exactly
the input message bundle: `reconstruct` only reads the cache at challenge rounds and splices the
given messages at message rounds. -/
theorem reconstruct_messages (stmt : StmtIn) (M : pSpec.Messages)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) :
    FullTranscript.messages (reconstruct (StmtIn := StmtIn) (pSpec := pSpec) stmt M cache)
      = M := by
  funext i
  exact reconstructAux_message_apply stmt (Fin.last n) M cache (Fin.last (Fin.last n).val)
    i.1.val i.1.isLt i.1.isLt i.2

/-- The Fiat-Shamir one-message proof built from the prover's messages is `msgProjFS` of the
reconstructed transcript. -/
theorem msgProjFS_reconstruct (stmt : StmtIn) (M : pSpec.Messages)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) :
    msgProjFS (pSpec := pSpec)
        (reconstruct (StmtIn := StmtIn) (pSpec := pSpec) stmt M cache)
      = (fun | ⟨0, _⟩ => M : FiatShamirProofTranscript (pSpec := pSpec)) := by
  funext i
  match i with
  | ⟨0, _⟩ => exact reconstruct_messages stmt M cache

/-! ## OptionT plumbing helpers -/

/-- `Option.getM` at the `OptionT` run level is `pure` of the option itself. -/
theorem optionT_run_getM {m : Type → Type} [Monad m] {α : Type} (o : Option α) :
    (o.getM : OptionT m α).run = pure o := by
  cases o <;> rfl

/-- Collapse an `Option.elim` whose branches are both `pure` into a `pure` of an `Option.map`. -/
theorem option_elim_pure_pure_some {m : Type → Type} [Monad m] {α β : Type}
    (o : Option α) (f : α → β) :
    (o.elim (pure none) (fun a => pure (some (f a))) : m (Option β)) = pure (o.map f) := by
  cases o <;> rfl

/-! ## Peeled run forms (the `OptionT` plumbing of both honest executions, discharged) -/

set_option maxHeartbeats 1000000 in
-- the `OptionT`/`liftM` normalization of the full honest-execution do-chain is large
/-- **FS-side peel.** The raw run of the explicit Fiat-Shamir honest execution is the bind-chain:
prover `runToRoundFS`, prover output (ambient), verifier transcript re-derivation
(`deriveTranscriptFS`), interactive verifier `verify` (ambient), and the final `Option` verdict
threading. All `OptionT` plumbing is gone. -/
theorem fiatShamirHonestExecution_run_peeled
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    (R.fiatShamirHonestExecution stmt wit).run
      = (R.prover.runToRoundFS (Fin.last n) stmt (R.prover.input (stmt, wit)) >>= fun z =>
          (R.prover.output z.2.2).liftComp (oSpec + fsChallengeOracle StmtIn pSpec) >>= fun c =>
          Messages.deriveTranscriptFS (oSpec := oSpec) stmt z.1 >>= fun T =>
          (R.verifier.verify stmt T).run.liftComp (oSpec + fsChallengeOracle StmtIn pSpec) >>=
            fun v =>
          pure (v.map fun s =>
            ((((fun | ⟨0, _⟩ => z.1) :
              FiatShamirProofTranscript (pSpec := pSpec)), c), s))) := by
  unfold Reduction.fiatShamirHonestExecution
  simp only [Verifier.run, Verifier.fiatShamir, OptionT.run_bind, OptionT.run_monadLift,
    monadLift_self, Option.elimM, OptionT.run_pure, bind_assoc, pure_bind, Option.elim_some,
    OptionT.run_liftM_run, optionT_run_getM, option_elim_pure_pure_some, bind_map_left]
  simp only [← OracleComp.liftComp_def]
  rfl

set_option maxHeartbeats 1000000 in
-- the `OptionT`/`liftM` normalization of the full reduction-run do-chain is large
/-- **Interactive-side peel.** The raw run of the interactive reduction execution is the
bind-chain: prover `runToRound`, prover output (ambient), interactive verifier `verify`
(ambient), and the final `Option` verdict threading. -/
theorem reduction_run_peeled
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    (R.run stmt wit).run
      = (R.prover.runToRound (Fin.last n) stmt wit >>= fun rt =>
          (R.prover.output rt.2).liftComp (oSpec + [pSpec.Challenge]ₒ) >>= fun c =>
          (R.verifier.verify stmt rt.1).run.liftComp (oSpec + [pSpec.Challenge]ₒ) >>= fun v =>
          pure (v.map fun s => ((rt.1, c), s))) := by
  unfold Reduction.run Prover.run
  simp only [Verifier.run, OptionT.run_bind, OptionT.run_monadLift, monadLift_self, Option.elimM,
    OptionT.run_pure, bind_assoc, pure_bind, Option.elim_some, OptionT.run_liftM_run,
    optionT_run_getM, option_elim_pure_pure_some, map_bind, bind_map_left]
  simp only [← OracleComp.liftComp_def, ← OracleComp.liftComp_eq_liftM]
  rfl

/-! ## The common residual continuation and the (G2) full-transcript coupling -/

/-- **The common verifier-leg continuation.** Given the coupled triple
`(transcript, prover state, ambient σ-state)`, both honest executions continue identically: run
the prover's output computation (ambient), run the interactive verifier's `verify` on the
transcript (ambient), and return the message-bundle marginal (`msgProjFS` of the transcript when
the verifier accepts, `none` otherwise). -/
noncomputable def verifierLegK (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) :
    pSpec.FullTranscript × R.prover.PrvState (Fin.last n) × σ →
      SPMF (Option (FiatShamirProofTranscript (pSpec := pSpec))) :=
  fun x =>
    evalDist ((simulateQ impl (R.prover.output x.2.1)).run x.2.2) >>= fun p =>
    evalDist ((simulateQ impl ((R.verifier.verify stmt x.1).run)).run p.2) >>= fun q =>
    pure (q.1.map fun _ => msgProjFS (pSpec := pSpec) x.1)

/-- **(G2) The full-transcript joint coupling** — the single remaining hypothesis.

The lazy Fiat-Shamir prover run (`runToRoundFS` under the product implementation
`ambientProd impl + fsLazyProd`, from the empty cache), projected to the *reconstructed*
transcript (prover messages + cached challenges), the prover state, and the ambient `σ`-state,
has the same joint law as the interactive prover run (`runToRound` under
`impl.addLift challengeQueryImpl`), projected to its full transcript, prover state, and
`σ`-state.

This strengthens the proven message coupling `coupling_run_lazy` from the message marginal to
the joint `(transcript, prover state, σ)` law: per round, the lazy cache stores exactly the
drawn challenge at the round key (`withCaching` stores the answer), so the reconstructed
transcript replays the prover's actual challenges — which are coupled to the interactive
verifier's fresh draws by `processRound_step_coupling`. -/
def fullTranscriptCoupling (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) : Prop :=
  ∀ a : σ,
    ((fun z => (reconstruct (StmtIn := StmtIn) (pSpec := pSpec) stmt z.1.1 z.2.2,
        z.1.2.2, z.2.1)) <$>
      evalDist (StateT.run (simulateQ
          (ambientProd (StmtIn := StmtIn) pSpec impl
            + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (R.prover.runToRoundFS (Fin.last n) stmt (R.prover.input (stmt, wit)))) (a, ∅)))
    = ((fun r => ((r.1.1 : pSpec.FullTranscript), r.1.2, r.2)) <$>
      evalDist (StateT.run (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec)) :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (R.prover.runToRound (Fin.last n) stmt wit)) a))

/-! ## The two collapse lemmas -/

set_option maxHeartbeats 1000000 in
-- large `simulateQ`/`evalDist` bind-chain normalization
/-- **Interactive-side collapse.** The marginal of the interactive honest run appearing in
`canonicalFSPerStateCoupling` is the interactive prover-run law, projected to
`(transcript, prover state, σ)`, continued by the common verifier leg `verifierLegK`.

(The marginal projection is stated at the partial-transcript type
`pSpec.Transcript (Fin.last n)` — definitionally `pSpec.FullTranscript` — so that it matches the
prover-run bind spine syntactically; the main theorem absorbs the definitional seam.) -/
theorem intSide_collapse (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (a : σ) :
    evalDist
        (Option.map (msgProjFS (pSpec := pSpec)) <$>
          StateT.run'
            (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec)) :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              ((Option.map
                  (fun result : (pSpec.Transcript (Fin.last n) × StmtOut × WitOut) × StmtOut =>
                  result.1.1)) <$> (R.run stmt wit).run)) a)
      = ((fun r => ((r.1.1 : pSpec.FullTranscript), r.1.2, r.2)) <$>
          evalDist (StateT.run (simulateQ
              (impl.addLift (challengeQueryImpl (pSpec := pSpec)) :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
            (R.prover.runToRound (Fin.last n) stmt wit)) a))
          >>= verifierLegK impl R stmt := by
  rw [reduction_run_peeled]
  rw [bind_map_left]
  simp only [simulateQ_map, simulateQ_bind, StateT.run'_eq, StateT.run_map, StateT.run_bind,
    Functor.map_map, evalDist_map, evalDist_bind, map_bind]
  refine bind_congr fun x => ?_
  simp only [verifierLegK, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    QueryImpl.simulateQ_add_liftComp_left, simulateQ_pure, StateT.run_pure, evalDist_pure]
  refine bind_congr fun p => bind_congr fun q => ?_
  simp only [LawfulApplicative.map_pure, Option.map_map]
  rfl

set_option maxHeartbeats 1000000 in
-- (large `simulateQ`/`evalDist` normalization)
/-- **Fiat-Shamir-side collapse.** The message-bundle marginal of the lazily-simulated honest
Fiat-Shamir execution is the lazy prover-run law, projected to the *reconstructed* transcript,
prover state, and ambient `σ`-state, continued by the SAME common verifier leg `verifierLegK`.
The verifier's transcript re-derivation has been collapsed by the cache-replay lemma
(`deriveTranscriptFS_lazy_run_of_runOutput`), and the FS proof bundle has been rewritten as
`msgProjFS` of the reconstructed transcript (`msgProjFS_reconstruct`). -/
theorem fsSide_collapse (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (a : σ) :
    evalDist
        (StateT.run'
          ((Option.map (fun r : (FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
              StmtOut => r.1.1)) <$>
            simulateQ (ambientProd (StmtIn := StmtIn) pSpec impl
                + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
              (R.fiatShamirHonestExecution stmt wit).run)
          (a, ∅))
      = ((fun z => (reconstruct (StmtIn := StmtIn) (pSpec := pSpec) stmt z.1.1 z.2.2,
            z.1.2.2, z.2.1)) <$>
          evalDist (StateT.run (simulateQ
              (ambientProd (StmtIn := StmtIn) pSpec impl
                + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
            (R.prover.runToRoundFS (Fin.last n) stmt (R.prover.input (stmt, wit)))) (a, ∅)))
          >>= verifierLegK impl R stmt := by
  rw [fiatShamirHonestExecution_run_peeled]
  rw [bind_map_left]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_map, StateT.run_bind,
    Functor.map_map, evalDist_map, evalDist_bind, map_bind]
  refine SPMF.bind_congr_of_support _ _ _ (fun z hz => ?_)
  have hzoc : z ∈ support (StateT.run (simulateQ
      (ambientProd (StmtIn := StmtIn) pSpec impl
        + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
      (R.prover.runToRoundFS (Fin.last n) stmt (R.prover.input (stmt, wit)))) (a, ∅)) := by
    rw [← mem_support_evalDist_iff]; simpa using hz
  simp only [verifierLegK, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_ambientProd_run impl, evalDist_map, bind_map_left,
    deriveTranscriptFS_lazy_run_of_runOutput R.prover impl stmt wit a z hzoc,
    simulateQ_pure, StateT.run_pure, evalDist_pure, pure_bind, msgProjFS_reconstruct]
  refine bind_congr fun p => bind_congr fun q => ?_
  simp only [LawfulApplicative.map_pure, Option.map_map]
  rfl

/-! ## The main reduction: per-state coupling from the full-transcript coupling -/

set_option maxHeartbeats 1000000 in
-- (definitional-seam absorption between `FullTranscript`/`Transcript (Fin.last n)` and between
-- `impl.addLift canonicalFSChallengeImpl`/`ambientProd impl + fsLazyProd` forms)
/-- **The per-state coupling residual, reduced to the full-transcript coupling (G3 + G4).**

Given only the (G2) full-transcript joint coupling `fullTranscriptCoupling`, the open per-state
residual `canonicalFSPerStateCoupling` of the basic Fiat-Shamir HVZK transfer holds: both honest
executions decompose into their prover-run laws followed by the *same* verifier-leg continuation
(`fsSide_collapse` / `intSide_collapse`), and the prover-run laws agree on the coupled
projection by hypothesis. Composing with
`fiatShamir_hvzkTransferResidual_canonical_of_perStateCoupling` closes the whole #116 HVZK
transfer from `fullTranscriptCoupling` alone. -/
theorem canonicalFSPerStateCoupling_of_fullTranscriptCoupling
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (hG2 : fullTranscriptCoupling impl R stmt wit) :
    canonicalFSPerStateCoupling impl R stmt wit := by
  intro a
  exact (fsSide_collapse impl R stmt wit a).trans
    ((congrArg (· >>= verifierLegK impl R stmt) (hG2 a)).trans
      (intSide_collapse impl R stmt wit a).symm)

-- Axiom audit of the deliverables.
#print axioms addLift_canonicalFSChallengeImpl_eq_prod
#print axioms reconstruct_messages
#print axioms msgProjFS_reconstruct
#print axioms fiatShamirHonestExecution_run_peeled
#print axioms reduction_run_peeled
#print axioms fsSide_collapse
#print axioms intSide_collapse
#print axioms canonicalFSPerStateCoupling_of_fullTranscriptCoupling

end Reduction
