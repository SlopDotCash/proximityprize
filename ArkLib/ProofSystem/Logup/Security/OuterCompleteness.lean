import ArkLib.ProofSystem.Logup.Security.Completeness
import ArkLib.OracleReduction.Completeness
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.Logup.Security.OuterRun
import ArkLib.ProofSystem.Logup.Security.OuterAcceptance
import ArkLib.OracleReduction.RunUnroll

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Logup

/-- **Completeness from a complement-zero predicate and a failure bound (general, axiom-clean).**

If the event's complement has probability `0` (i.e. the predicate `p` holds on *every successful*
outcome of `mx`) and the failure probability `Pr[⊥ | mx]` is at most `err`, then the event
probability is at least `1 - err`.  Proof: `probEvent_compl` gives
`Pr[p] + Pr[¬p] = 1 - Pr[⊥]`; with `Pr[¬p] = 0` this is `Pr[p] = 1 - Pr[⊥] ≥ 1 - err`.

This is the *probability core* of the outer LogUp completeness obligation
(`OuterCompletenessRunResidual`): the honest prover/verifier agree on every accepting transcript
and the honest after-outer statement satisfies the claim-true `midRelation` (the grand-sum
identity), so the completeness predicate holds on every successful run (its complement has
probability `0`), and the run's failure event is exactly
the table-pole event bounded by `probEvent_pole_le` / `probEvent_outerVerify_reject_le`.  With this
lemma, the remaining content of `OuterCompletenessRunResidual` is exactly those two run-level
facts (`Pr[¬p] = 0` and `probFailure ≤ logupCompletenessError`), with all probability arithmetic
discharged. -/
theorem probEvent_ge_one_sub_of_compl_zero {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    (mx : m α) (p : α → Prop) (err : ℝ≥0∞)
    (hA : probEvent (fun x => ¬ p x) (mx) = 0) (hB : prFail (mx) ≤ err) :
    probEvent (p) (mx) ≥ 1 - err := by
  simp only [probEvent] at hA ⊢
  have hmass := prEvent_add_prEvent_not_eq_prEvent_true mx p
  rw [hA, add_zero] at hmass
  rw [prFail_def, ← hmass] at hB
  exact tsub_le_iff_tsub_le.mp hB

/-- Completeness from the two concrete run-level facts exposed by `probEvent_ge_one_sub_of_compl_zero`.

For each valid input, it is enough to show that the complement of the completeness predicate has
probability `0` on the simulated run and that the run's failure probability is bounded by the claimed
error. This is the generic adapter that lets the outer LogUp proof name those two obligations
directly instead of restating the whole `Reduction.completenessFromRun` event. -/
theorem completenessFromRun_of_compl_zero_failure_bound
    {StmtIn WitIn StmtOut WitOut : Type}
    {ιᵣ : Type} {runSpec : OracleSpec ιᵣ} {σᵣ : Type} {Trace : Type}
    (runInit : ProbComp σᵣ)
    (runImpl : QueryImpl runSpec (StateT σᵣ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (run : (stmtIn : StmtIn) → (witIn : WitIn) →
      OptionT (OracleComp runSpec) ((Trace × StmtOut × WitOut) × StmtOut))
    (completenessError : ℝ≥0)
    (hComplZero :
      ∀ stmtIn witIn,
        (stmtIn, witIn) ∈ relIn →
          probEvent (fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
              ¬ ((stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut)) (OptionT.mk do
              (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit)) = 0)
    (hFailure :
      ∀ stmtIn witIn,
        (stmtIn, witIn) ∈ relIn →
          prFail (OptionT.mk do
              (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit))
            ≤ (completenessError : ℝ≥0∞)) :
    Reduction.completenessFromRun runInit runImpl relIn relOut run completenessError := by
  intro stmtIn witIn hRel
  exact probEvent_ge_one_sub_of_compl_zero
    (OptionT.mk do
      (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit))
    (fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
      (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut)
    (completenessError : ℝ≥0∞)
    (hComplZero stmtIn witIn hRel)
    (hFailure stmtIn witIn hRel)

section OuterCompleteness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`). Explicitly named (rather than anonymous) so it does not collide with
the identically-typed anonymous `local instance` in `Security/Soundness.lean` when a downstream
module (e.g. `Security/SubPhaseSplit.lean`) imports both files. -/
local instance instInhabitedFieldOuterCompleteness : Inhabited F := ⟨0⟩

/-- Result type of the standard outer-completeness run experiment. -/
abbrev OuterCompletenessRunResult :=
  (((outerPSpec F n params).FullTranscript ×
      (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) ×
    StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))

/-- The standard outer-completeness run experiment after simulating verifier challenges. -/
noncomputable def outerCompletenessRunComp
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    OptionT ProbComp (OuterCompletenessRunResult F n M params) :=
  OptionT.mk do
    (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
      (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
        StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' (← init)

-- OptionT-level collapse (no outer .run): applies directly inside Reduction.run's bind.
example {ι : Type} {oSpec : OracleSpec ι} {α β γ : Type} (pr : α) (sv : β) (e : γ) (P : Prop) [Decidable P] :
    (do
      let stmtOut ← (liftM (((fun a => (a, e)) <$> (if P then pure sv else (failure : OptionT (OracleComp oSpec) β))).run)
          : OptionT (OracleComp oSpec) (Option (β × γ)))
      Prod.mk pr <$> stmtOut.getM)
      = (if P then pure (pr, (sv, e)) else failure) := by
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; rfl

lemma optionT_liftM_run_getM_collapse {ι : Type} {oSpec : OracleSpec ι} {α β γ : Type} (pr : α) (sv : β) (e : γ) (P : Prop) [Decidable P] :
    (do
      let stmtOut ← (liftM (((fun a => (a, e)) <$> (if P then pure sv else (failure : OptionT (OracleComp oSpec) β))).run)
          : OptionT (OracleComp oSpec) (Option (β × γ)))
      Prod.mk pr <$> stmtOut.getM)
      = (if P then pure (pr, (sv, e)) else failure) := by
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; rfl

/-- The outer LogUp completeness run-unfolding statement — **proven**, see
`outerCompletenessRunResidual_proved` below (issue #337 closeout).

Historical note: this was originally an honest residual for the then-unfinished prover-run
marginal calculation; the verifier-side pole bound was proved first in `OuterAcceptance.lean`
and the run-level facts (`outer_completenessRunFactsResidual` below) completed the calculation.
The `Prop` name is retained for downstream statement stability. -/
def OuterCompletenessRunResidual : Prop :=
  NeverFail init →
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)

/-- Two explicit run-level facts that imply the outer completeness residual — **proven**, see
`outer_completenessRunFactsResidual` below (issue #337 closeout).

The first says every successful standard outer run satisfies the completeness predicate. The second
says the only failed runs have probability bounded by `logupCompletenessError`. -/
def OuterCompletenessRunFactsResidual : Prop :=
  NeverFail init →
    (∀ stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i),
      ∀ witIn : WitIn F n M params,
        (stmtIn, witIn) ∈ inputRelation F n M →
          probEvent (fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
              ¬ ((stmtOut, witOut) ∈ midRelation F n M params ∧ prvStmtOut = stmtOut)) (outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn) = 0) ∧
    (∀ stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i),
      ∀ witIn : WitIn F n M params,
        (stmtIn, witIn) ∈ inputRelation F n M →
          prFail (outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn)
            ≤ (logupCompletenessError F n : ℝ≥0∞))

/-- **Run-unfold brick for the 4-round outer prover (foundational, axiom-clean).**

The honest outer LogUp prover runs the fixed 4-round protocol (P→V multiplicity, V→P `x`, P→V
helpers, V→P batching).  This lemma peels its full `runToRound (Fin.last 4)` into the first
prover step (`processRound 0` on the seeded input state — the round-0 multiplicity message)
followed by the continuation `continueFromTo 1 → last` that folds the remaining three rounds.

It is the structural front door for the still-open prover-run marginal calculation inside
`OuterCompletenessRunFactsResidual`: with the run in this `bind` form, the round-1 `x` challenge
is exposed at the seam so its uniform marginal can be transported to the table-pole event.

Proof: the symmetric form of the generic `processRound_zero_continueFromTo_eq_runToRound_last`
(`OracleReduction/Execution.lean`), instantiated at this protocol.  Note this is the *only*
sound way to unfold the run here: a naive `rw` peel of `runToRound (Fin.last 4)` round-by-round
hits a non-type-correct motive (the `Transcript`/`PrvState` types depend on the `Fin` round
index), exactly the `Fin.succ`/`Fin.castSucc` mismatch the `continueFromTo` machinery exists to
route around. -/
theorem outerProver_runToRound_last_peel
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerProver oSpec F n M params).runToRound (Fin.last 4) stmtIn witIn
      = (outerProver oSpec F n M params).processRound (⟨0, by omega⟩ : Fin 4)
            (pure ((default : (outerPSpec F n params).Transcript (⟨0, by omega⟩ : Fin 5)),
                   (outerProver oSpec F n M params).input (stmtIn, witIn)))
          >>= (outerProver oSpec F n M params).continueFromTo stmtIn witIn
                (⟨0, by omega⟩ : Fin 4).succ (Fin.last 4) :=
  (Prover.processRound_zero_continueFromTo_eq_runToRound_last (by omega)
    (outerProver oSpec F n M params) stmtIn witIn).symm

/-- The explicit complement-zero/failure-bound run facts discharge the existing outer completeness
run residual. -/
theorem outer_completeness_of_runFacts
    (h : OuterCompletenessRunFactsResidual (oSpec := oSpec) F n M params init impl)
    (hInit : NeverFail init) :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) := by
  obtain ⟨hComplZero, hFailure⟩ := h hInit
  unfold OracleReduction.completeness Reduction.completeness
  exact completenessFromRun_of_compl_zero_failure_bound init
    (QueryImpl.addLift impl challengeQueryImpl)
    (inputRelation F n M) (midRelation F n M params)
    ((outerOracleReduction oSpec F n M params).toReduction.run)
    (logupCompletenessError F n)
    hComplZero hFailure

/-- Consumer for the honest outer LogUp completeness run-unfolding residual. -/
theorem outer_completeness_of_runResidual
    (h : OuterCompletenessRunResidual oSpec F n M params init impl) (hInit : NeverFail init) :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) :=
  h hInit

set_option linter.unusedSimpArgs false in
/-- **Closed form of the outer honest prover's full run (`runToRound (Fin.last 4)`).**

The outer LogUp prover has four rounds (`P→V` multiplicity, `V→P` challenge `x`, `P→V` helpers,
`V→P` batch). Unfolding `runToRound` round-by-round (peeling with the message/challenge round
lemmas of `Execution.lean`, chained bottom-up with `simp only` to tolerate the dependent `Fin`
motive) reduces the entire run to a `do`-block containing **exactly two** `getChallenge` samples —
the `x` challenge at round 1 and the `batch` challenge at round 3 — with every prover step pure.
The final prover state is the record `(oStmt, x, batch)` carried into `outerProver.output`.

This is the load-bearing prover-side structural fact for outer-phase completeness: composed with
the verifier's pole-scan collapse (`OuterRun.lean`), it exposes that the only randomness in the
outer phase is the two uniform challenge samples. -/
theorem outerProver_runToRound_closed_form
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerProver oSpec F n M params).runToRound (Fin.last 4) stmtIn witIn = (do
      let m₀ ← (outerProver oSpec F n M params).sendMessage ⟨0, rfl⟩
                  ((outerProver oSpec F n M params).input (stmtIn, witIn))
      let x ← (outerPSpec F n params).getChallenge ⟨1, rfl⟩
      let r₁ ← (outerProver oSpec F n M params).receiveChallenge ⟨1, rfl⟩ m₀.2
      let m₂ ← (outerProver oSpec F n M params).sendMessage ⟨2, rfl⟩ (r₁ x)
      let batch ← (outerPSpec F n params).getChallenge ⟨3, rfl⟩
      let r₃ ← (outerProver oSpec F n M params).receiveChallenge ⟨3, rfl⟩ m₂.2
      return ⟨((default : (outerPSpec F n params).Transcript 0).concat m₀.1).concat x
                |>.concat m₂.1 |>.concat batch, r₃ batch⟩) := by
  -- Direction facts (all `rfl` on this fixed protocol spec).
  have d0 : (outerPSpec F n params).dir (0 : Fin 4) = Direction.P_to_V := rfl
  have d1 : (outerPSpec F n params).dir (1 : Fin 4) = Direction.V_to_P := rfl
  have d2 : (outerPSpec F n params).dir (2 : Fin 4) = Direction.P_to_V := rfl
  have d3 : (outerPSpec F n params).dir (3 : Fin 4) = Direction.V_to_P := rfl
  -- Round 0 (message): runToRound 1 from the prover-first base.
  have h0 := Prover.runToRound_succ_message (n := 4) (0 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d0
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd,
    Prover.runToRound_zero_of_prover_first, bind_assoc, pure_bind] at h0
  -- Round 1 (challenge x).
  have h1 := Prover.runToRound_succ_challenge (n := 4) (1 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d1
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd, h0, bind_assoc] at h1
  -- Round 2 (message helpers).
  have h2 := Prover.runToRound_succ_message (n := 4) (2 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d2
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd, h1, bind_assoc] at h2
  -- Round 3 (challenge batch).
  have h3 := Prover.runToRound_succ_challenge (n := 4) (3 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d3
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd, h2, bind_assoc] at h3
  -- `Fin.last 4 = (3 : Fin 4).succ`, so `h3` is the run to `Fin.last 4`.
  exact h3

/-- **Closed form of the outer honest prover's *full* run (`Prover.run`).**

`Prover.run` is `runToRound (Fin.last 4)` followed by `output` (`run_eq_runToRound_last`). Plugging in
the banked `outerProver_runToRound_closed_form` exposes the entire prover run as a `do`-block with
**exactly two** `getChallenge` samples (the `x` challenge at round 1 and the `batch` challenge at
round 3), every other prover step pure, ending in the prover's `output` step applied to the final
state `r₃ batch`. This is the prover-side half of the simulated outer-reduction run. -/
theorem outerProver_run_closed_form
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerProver oSpec F n M params).run stmtIn witIn = (do
      let m₀ ← (outerProver oSpec F n M params).sendMessage ⟨0, rfl⟩
                  ((outerProver oSpec F n M params).input (stmtIn, witIn))
      let x ← (outerPSpec F n params).getChallenge ⟨1, rfl⟩
      let r₁ ← (outerProver oSpec F n M params).receiveChallenge ⟨1, rfl⟩ m₀.2
      let m₂ ← (outerProver oSpec F n M params).sendMessage ⟨2, rfl⟩ (r₁ x)
      let batch ← (outerPSpec F n params).getChallenge ⟨3, rfl⟩
      let r₃ ← (outerProver oSpec F n M params).receiveChallenge ⟨3, rfl⟩ m₂.2
      let out ← (outerProver oSpec F n M params).output (r₃ batch)
      return ⟨((default : (outerPSpec F n params).Transcript 0).concat m₀.1).concat x
                |>.concat m₂.1 |>.concat batch, out⟩) := by
  rw [Prover.run_eq_runToRound_last, outerProver_runToRound_closed_form]
  simp only [bind_assoc, pure_bind]

/-- **Closed form of the full outer oracle-reduction run (`toReduction.run`).**

`Reduction.run` first runs the prover, then lifts the verifier over the produced transcript. The outer
oracle reduction's prover/verifier are *definitionally* `outerProver`/`outerVerifier`, so its
`toReduction.run` is the explicit `Reduction.run` do-block over those two: run the prover, lift the
verifier over the produced transcript, and project the verdict. Composed with the banked
`outerProver_run_closed_form`, the prover head reduces to the two-challenge closed form (the `x`
sample at round 1, the `batch` sample at round 3, every other prover step pure), so the only
randomness in the run is the two uniform challenge samples — exactly what the simulated experiment
(`outerCompletenessRunComp`) resolves through `challengeQueryImpl`. -/
theorem outerReduction_run_closed_form
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn = (do
      let proverResult ← liftM ((outerProver oSpec F n M params).run stmtIn witIn)
      let stmtOut ← liftM
        ((outerVerifier oSpec F n M params).toVerifier.run stmtIn proverResult.1).run
      return ⟨proverResult, ← stmtOut.getM⟩) := by
  rfl


/-- **Challenge-sample collapse for the simulated outer run (foundational, axiom-clean).**

Simulating an outer-phase challenge query (`getChallenge i`) through the lifted challenge oracle
implementation (`challengeQueryImpl`, the right summand of `addLift impl challengeQueryImpl`) resolves
to a single uniform sample `$ᵗ (Challenge i)`. This is the load-bearing brick that turns each of the
honest outer prover's two `getChallenge` calls (the round-1 `x` and round-3 `batch`) — exposed by
`outerProver_run_closed_form` — into a plain uniform draw once the run is pushed through
`simulateQ (addLift impl challengeQueryImpl)`, leaving the two challenge samples as the *only*
randomness of the simulated outer experiment. It is the challenge-side counterpart of the
verifier-side `simulateQ_outerVerify_eq` collapse, and feeds the round-1 marginal calculation that
transports `x` to the table-pole event bounded by `probEvent_outerVerify_reject_le`. -/
theorem getChallenge_simulateQ_eq (i : (outerPSpec F n params).ChallengeIdx) :
    simulateQ (QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := outerPSpec F n params)))
      ((outerPSpec F n params).getChallenge i)
      = (liftM ($ᵗ ((outerPSpec F n params).Challenge i)) :
          StateT σ ProbComp ((outerPSpec F n params).Challenge i)) := by
  unfold ProtocolSpec.getChallenge
  erw [simulateQ_spec_query]
  rfl

/-- **Transcript challenge readback for the closed-form outer run (foundational, axiom-clean).**

The closed-form prover transcript is the 4-fold `Transcript.concat` (`Fin.snoc`) chain
`((((default).concat m₀).concat x).concat m₂).concat batch`.  The outer verifier reads its two
challenges off this transcript via `chalX`/`chalBatch` (`= transcript ⟨1,rfl⟩` / `transcript ⟨3,rfl⟩`),
while the honest prover's output record uses the received challenges `x`/`batch` directly.  This
lemma settles that they coincide: each `getChallenge` sample is read back unchanged at its own
round index.  Pure finite `Fin.snoc` computation (the last `snoc` for `batch` at index `3 = last`,
and `x` at `1 = castSucc²` peeled through the inner `snoc`s). -/
theorem outerProver_transcript_challenge_readback
    (m₀ : (outerPSpec F n params).Message ⟨0, rfl⟩)
    (x : (outerPSpec F n params).Challenge ⟨1, rfl⟩)
    (m₂ : (outerPSpec F n params).Message ⟨2, rfl⟩)
    (batch : (outerPSpec F n params).Challenge ⟨3, rfl⟩) :
    chalX F n M params
        (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).challenges = x ∧
    chalBatch F n M params
        (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).challenges = batch := by
  constructor
  · simp only [chalX, FullTranscript.challenges, Transcript.concat, Fin.isValue]
    rfl
  · simp only [chalBatch, FullTranscript.challenges, Transcript.concat, Fin.isValue]
    rfl

/-- **Transcript message readback for the closed-form outer run (foundational, axiom-clean).**

Sibling of `outerProver_transcript_challenge_readback` on the message side. The closed-form prover
transcript is the 4-fold `Transcript.concat` (`Fin.snoc`) chain
`((((default).concat m₀).concat x).concat m₂).concat batch`. The outer verifier reads the two prover
messages off this transcript to build its output oracle statement via `embed`
(`.multiplicity → messages ⟨0⟩`, `.helpers → messages ⟨2⟩`), while the honest prover's output oracle
statement uses the sent messages `m₀`/`m₂` directly. This lemma settles that they coincide: each sent
message is read back unchanged at its own round index — the message-side structural fact for the
prover/verifier output-statement agreement (`prvStmtOut = stmtOut`) inside
`OuterCompletenessRunFactsResidual`. Pure finite `Fin.snoc` computation (`m₂` at index `2`, and `m₀`
at index `0` peeled through the inner `snoc`s). -/
theorem outerProver_transcript_message_readback
    (m₀ : (outerPSpec F n params).Message ⟨0, rfl⟩)
    (x : (outerPSpec F n params).Challenge ⟨1, rfl⟩)
    (m₂ : (outerPSpec F n params).Message ⟨2, rfl⟩)
    (batch : (outerPSpec F n params).Challenge ⟨3, rfl⟩) :
    (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).messages (⟨0, rfl⟩ : (outerPSpec F n params).MessageIdx) = m₀ ∧
    (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).messages (⟨2, rfl⟩ : (outerPSpec F n params).MessageIdx) = m₂ := by
  constructor
  · simp only [FullTranscript.messages, Transcript.concat, Fin.isValue]
    rfl
  · simp only [FullTranscript.messages, Transcript.concat, Fin.isValue]
    rfl

/-- **Outer verifier output oracle-statement agreement (foundational, axiom-clean).**

The outer verifier recomputes its output oracle statements off the transcript via `embed`
(`.input i → .inl i` passthrough, `.multiplicity → .inr ⟨0⟩`, `.helpers → .inr ⟨2⟩`) through the
dependent `hEq`/`embed` transport of `OracleVerifier.run`.  Given the transcript carries the honest
prover's round-0/round-2 messages (`honestMultiplicity oStmt` / `honestHelpers params oStmt x` — as
exposed by `outerProver_transcript_message_readback` on the closed-form run), the verifier's output
oracle-statement function coincides *exactly* with the honest prover's output oracle-statement
function (`outerProver.output`).  This is the oracle-statement half of the prover/verifier
output-statement agreement (`prvStmtOut = stmtOut`), the complement-zero content of
`OuterCompletenessRunFactsResidual`; the statement-record half is `outerProver_transcript_challenge_readback`.

The outerVerifier's `embed`/`hEq` are concrete `rfl` on each `OuterOracleIdx` constructor, so the
`hEq i ▸ h ▸` transports compute away under `cases i`. -/
theorem outerVerifier_oStmtOut_eq
    (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : (outerPSpec F n params).FullTranscript)
    (x : F)
    (hm : transcript.messages (⟨0, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestMultiplicity oStmt)
    (hh : transcript.messages (⟨2, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestHelpers params oStmt x) :
    ((outerVerifier oSpec F n M params).materializeOutput transcript.challenges oStmt transcript.messages)
      = (fun
          | .input i => oStmt i
          | .multiplicity => honestMultiplicity oStmt
          | .helpers => honestHelpers params oStmt x) := by
  funext i
  cases i with
  | input j => rfl
  | multiplicity => exact hm
  | helpers => exact hh

/-- **Honest outer prover/verifier output-pair agreement (foundational, axiom-clean).**

The single `prvStmtOut = stmtOut` value-fact, gluing the two banked agreement halves: given the
closed-form transcript carries the honest challenges (`x`/`batch`, via
`outerProver_transcript_challenge_readback`) and the honest messages
(`honestMultiplicity`/`honestHelpers`, via `outerProver_transcript_message_readback`), the honest
prover's output statement pair (`outerProver.output` on the final state `(oStmt, x, batch)`) equals
the pair the verifier recomputes from the same transcript — the statement record read off the
challenges (`chalX`/`chalBatch`) and the oracle statements read via `embed`. This is exactly the
pointwise per-state agreement consumed by
`probEvent_outerCompletenessRunComp_compl_eq_zero_of_perState` (the complement-zero / Fact 1
obligation of `OuterCompletenessRunFactsResidual`). -/
theorem outerProver_output_pair_eq_verifier_recompute
    (oStmt : ∀ i, OStmtIn F n M i)
    (x : F)
    (batch : BatchingChallenge F n params.numGroups)
    (transcript : (outerPSpec F n params).FullTranscript)
    (hx : chalX F n M params transcript.challenges = x)
    (hb : chalBatch F n M params transcript.challenges = batch)
    (hm : transcript.messages (⟨0, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestMultiplicity oStmt)
    (hh : transcript.messages (⟨2, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestHelpers params oStmt x) :
    (show StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i) from
      ({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
       fun
        | .input i => oStmt i
        | .multiplicity => honestMultiplicity oStmt
        | .helpers => honestHelpers params oStmt x))
      = ({ xChallenge := chalX F n M params transcript.challenges,
           zChallenge := (chalBatch F n M params transcript.challenges).1,
           batchingScalars := (chalBatch F n M params transcript.challenges).2 },
         (outerVerifier oSpec F n M params).materializeOutput transcript.challenges oStmt transcript.messages) := by
  rw [hx, hb]
  refine Prod.ext rfl ?_
  exact (outerVerifier_oStmtOut_eq oSpec F n M params oStmt transcript x hm hh).symm

set_option maxHeartbeats 3200000 in
/-- **Outer-completeness failure bound reduced to the per-(initial-state) pole event (axiom-clean).**

The standard outer-run failure probability is bounded by `logupCompletenessError` *given* the
per-initial-state fact that the simulated reduction run returns `none` (its only failure mode, the
verifier rejecting the sampled `x`-challenge) with probability at most that error.

This discharges all of the run-level probability plumbing — the `OptionT.mk` failure split
(`OptionT.probFailure_mk`: bare `⊥` is `0` in `ProbComp`, so failure surfaces only as `none`) and the
average over the never-failing `init` state (`probEvent_bind_le_of_forall_le`) — leaving exactly the
per-state pole obligation.  That remaining obligation is the simulated-verifier-run collapse to
`¬ outerVerifyAccepts` marginalised over the uniform `x`, bounded by `probEvent_outerVerify_reject_le`. -/
theorem probFailure_outerCompletenessRunComp_le_of_perStateNone
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params)
    (hPole : ∀ s : σ,
      probEvent (fun value => value = none) (((simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
            StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' s))
        ≤ (logupCompletenessError F n : ℝ≥0∞)) :
    prFail (outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn)
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  unfold outerCompletenessRunComp
  rw [OptionT.probFailure_mk]
  simp only [OracleComp.prFail_eq_zero, zero_add]
  exact prEvent_bind_le_of_forall_le_of_support init _ _ (fun s _ => hPole s)

set_option maxHeartbeats 3200000 in
/-- **Outer-completeness complement-zero reduced to the per-(initial-state) agreement (axiom-clean).**

The completeness predicate `(stmtOut, witOut) ∈ midRelation ∧ prvStmtOut = stmtOut` (with the
corrected claim-true `midRelation`) has complement probability `0` on the
standard outer run, *given* the per-initial-state fact that its complement is `0` on the simulated
reduction run.

This discharges the run-level plumbing sorry-free: the `OptionT.mk` event collapse
(`probEvent_optionT_mk_eq_elim`) and the split over the `init` state (`probEvent_bind_eq_tsum` +
`ENNReal.tsum_eq_zero`).  The remaining per-state obligation is that on every successful simulated run
the honest prover's output statement equals the verifier's recomputed one — exactly the
`outerProver_transcript_challenge_readback` / `..._message_readback` agreement. -/
theorem probEvent_outerCompletenessRunComp_compl_eq_zero_of_perState
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params)
    (hAgree : ∀ s : σ,
      probEvent (fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
          ¬ ((stmtOut, witOut) ∈ midRelation F n M params ∧ prvStmtOut = stmtOut)) ((OptionT.mk ((simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
              StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' s)
          : OptionT ProbComp (OuterCompletenessRunResult F n M params))) = 0) :
    probEvent (fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
        ¬ ((stmtOut, witOut) ∈ midRelation F n M params ∧ prvStmtOut = stmtOut)) (outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn) = 0 := by
  unfold outerCompletenessRunComp
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim]
  refine le_antisymm (prEvent_bind_le_of_forall_le_of_support init _ _ ?_) (by positivity)
  intro s _
  have h := hAgree s
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim] at h
  exact le_of_eq h

/-- **`OptionT`-over-`OracleComp` run-of-lift law.** Running the `OptionT`-lift of a never-failing
`OracleComp` maps every output to `some`. (`OptionT.lift a = OptionT.mk (some <$> a)`.) -/
theorem optionT_run_lift {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (a : OracleComp spec α) :
    (liftM a : OptionT (OracleComp spec) α).run = Option.some <$> a := by
  change (a >>= fun value => pure (some value)) = some <$> a
  rw [map_eq_bind_pure_comp]
  rfl

/-- **`OptionT`-over-`OracleComp` run-of-bind law.** The base computation of an `OptionT` bind runs
the first stage, then on `some` runs the second stage (threaded) and on `none` short-circuits. -/
theorem optionT_run_bind {ι' : Type} {spec : OracleSpec ι'} {α β : Type}
    (x : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    (x >>= f).run = x.run >>= fun o =>
      match o with | some a => (f a).run | none => pure none := by
  rw [OptionT.run_bind]
  apply bind_congr
  intro value
  cases value <;> rfl

/-- **`OptionT` lift-bind-run collapse.** Since the lifted stage never fails, binding it then running
collapses to running the base then the (run of the) continuation — the structural primitive for
peeling a never-failing head off an `OptionT (OracleComp _)` run. -/
theorem optionT_lift_bind_run {ι' : Type} {spec : OracleSpec ι'} {α β : Type}
    (a : OracleComp spec α) (b : α → OptionT (OracleComp spec) β) :
    ((liftM a >>= b : OptionT (OracleComp spec) β)).run = a >>= fun x => (b x).run := by
  rw [optionT_run_bind, optionT_run_lift, ← bind_pure_comp, bind_assoc]
  simp only [pure_bind]

/-- **Outer verifier rejection bound over the protocol's own challenge measure.**

`probEvent_outerVerify_reject_le` bounds the rejection probability when `x` is drawn from
`uniformSample F`.  The marginal produced by `ChallengeCoherence.probEvent_run'_…_getChallenge_bind`
instead measures against `$ᵗ ((outerPSpec …).Challenge ⟨1, rfl⟩)` — uniform sampling over the
protocol's *own* challenge type at round `⟨1⟩`.  Those two measures coincide: `Challenge ⟨1, rfl⟩` is
definitionally `F`, and `probEvent_uniformSample` evaluates either measure to the same
`Fintype.card`-based ratio, which is independent of the (non-defeq) `SampleableType` instance carried
along.  This is the bridge that lets the per-state pole obligation cite the verifier-side bound. -/
theorem probEvent_outerVerify_reject_challenge_le (oStmt : ∀ i, OStmtIn F n M i)
    [hChallenge : SampleableType ((outerPSpec F n params).Challenge ⟨1, rfl⟩)] :
    probEvent (fun c => ¬ outerVerifyAccepts F n M oStmt c)
      ($ᵗ ((outerPSpec F n params).Challenge ⟨1, rfl⟩))
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  classical
  let : SampleableType F := hChallenge
  exact probEvent_outerVerify_reject_le (oStmt := oStmt)

/-- **Embedded-verifier accept collapse.** On a transcript whose `x`-challenge is accepted
(`outerVerifyAccepts`), the outer reduction's embedded (plain) verifier run is a pure successful
output: its `OptionT.run` is `pure (some …)`, so it never fails (`none`). This is the verifier-side
half of the per-state accept-zero step in `outer_perState_none_le` — a direct repackaging of the
pole-scan collapse `simulateQ_outerVerify_eq` under the named acceptance predicate. -/
theorem outerVerifier_run_accept_eq_pure
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : FullTranscript (outerPSpec F n params))
    (hacc : outerVerifyAccepts F n M stmtIn.2 (chalX F n M params tr.challenges)) :
    (Verifier.run stmtIn tr (outerVerifier oSpec F n M params).toVerifier).run
      = (pure (some (show StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i) from
          ({ xChallenge := chalX F n M params tr.challenges,
             zChallenge := (chalBatch F n M params tr.challenges).1,
             batchingScalars := (chalBatch F n M params tr.challenges).2 },
           (outerVerifier oSpec F n M params).materializeOutput tr.challenges stmtIn.2 tr.messages))) : OracleComp oSpec
          (Option (StmtAfterOuter F n M params
            × (∀ i, OStmtAfterOuter F n M params i)))) := by
  classical
  have hVerify := simulateQ_outerVerify_eq_accepts (oSpec := oSpec) (F := F)
    (n := n) (M := M) (params := params) stmtIn.1 stmtIn.2 tr.challenges tr.messages
  rw [ite_eq_left hacc] at hVerify
  have hRun := congrArg OptionT.run hVerify
  change simulateQ (OracleInterface.simOracle2 oSpec stmtIn.2 tr.messages)
    ((outerVerifier oSpec F n M params).verify stmtIn.1 tr.challenges).run = _ at hRun
  unfold Verifier.run OracleVerifier.toVerifier
  simp only [OptionT.run_mk, hRun, OptionT.run_pure,
    LawfulApplicative.map_pure, Option.map_some]

/-- **Embedded-verifier reject collapse.** On a transcript whose `x`-challenge hits a table pole
(`¬ outerVerifyAccepts`), the embedded verifier run fails: its `OptionT.run` is `pure none`.  The
counterpart of `outerVerifier_run_accept_eq_pure`, used to rule out successful runs on the reject
side of the per-state agreement step. -/
theorem outerVerifier_run_reject_eq_none
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : FullTranscript (outerPSpec F n params))
    (hrej : ¬ outerVerifyAccepts F n M stmtIn.2 (chalX F n M params tr.challenges)) :
    (Verifier.run stmtIn tr (outerVerifier oSpec F n M params).toVerifier).run
      = (pure none : OracleComp oSpec
          (Option (StmtAfterOuter F n M params
            × (∀ i, OStmtAfterOuter F n M params i)))) := by
  classical
  have hVerify := simulateQ_outerVerify_eq_accepts (oSpec := oSpec) (F := F)
    (n := n) (M := M) (params := params) stmtIn.1 stmtIn.2 tr.challenges tr.messages
  rw [ite_eq_right hrej] at hVerify
  have hRun := congrArg OptionT.run hVerify
  change simulateQ (OracleInterface.simOracle2 oSpec stmtIn.2 tr.messages)
    ((outerVerifier oSpec F n M params).verify stmtIn.1 tr.challenges).run = _ at hRun
  unfold Verifier.run OracleVerifier.toVerifier
  simp only [OptionT.run_mk, hRun, OptionT.run_failure,
    LawfulApplicative.map_pure, Option.map_none]

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Per-state pole bound for the simulated outer run.**

Discharges the `hPole` obligation of `probFailure_outerCompletenessRunComp_le_of_perStateNone`: the
simulated reduction run returns `none` with probability at most `logupCompletenessError`.  Peels the
never-failing prover head (`optionT_lift_bind_run` + `outerProver_run_closed_form`), marginalises the
round-1 `x`-challenge (`probEvent_run'_simulateQ_addLift_getChallenge_bind`), and bounds the resulting
weighted sum by the verifier rejection event via `probEvent_outerVerify_reject_challenge_le`.  The
per-`c` split: on accept the run never fails; on reject the failure probability
is trivially `≤ 1`. -/
theorem outer_perState_none_le
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params)
    (s : σ) :
    probEvent (fun value => value = none) (((simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
          StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' s))
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  classical
  rw [outerReduction_run_closed_form, optionT_lift_bind_run, outerProver_run_closed_form]
  simp only [outerProver, bind_pure_comp, pure_bind, map_pure, bind_assoc,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure]
  simp only [OracleComp.liftComp_eq_liftM]
  erw [ChallengeCoherence.run'_simulateQ_addLift_getChallenge_bind]
  refine le_trans (prEvent_bind_le_prEvent_of_forall_eq_zero _ _
    (fun c => ¬ outerVerifyAccepts F n M stmtIn.2 c) (fun value => value = none) ?_)
    (by simpa only [probEvent] using
      (probEvent_outerVerify_reject_challenge_le (params := params) (oStmt := stmtIn.2)
        (hChallenge := instOuterPSpecChallengeSampleable ⟨1, rfl⟩)))
  intro c hnot
  have hacc : outerVerifyAccepts F n M stmtIn.2 c := Classical.not_not.mp hnot
  apply (OracleComp.prEvent_eq_zero_iff _ _).2
  intro y hy hynone
  subst hynone
  -- `none` survives the simulated run only if it is already in the (un-simulated) run's support.
  have hsub := _root_.support_simulateQ_run'_subset (impl.addLift challengeQueryImpl) _ s hy
  rw [support_bind] at hsub
  simp only [Set.mem_iUnion, exists_prop] at hsub
  obtain ⟨x, hx, hxnone⟩ := hsub
  rw [support_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  -- The transcript built here carries `c` as its round-1 challenge (`readback`), so the embedded
  -- verifier accepts and its run is a pure `some` — leaving no `none` in the support.
  have hV := outerVerifier_run_accept_eq_pure oSpec F n M params stmtIn _
    ((outerProver_transcript_challenge_readback
        (m₀ := honestMultiplicity stmtIn.2) (x := c)
        (m₂ := honestHelpers params stmtIn.2 c) (batch := a)).1.symm ▸ hacc)
  rw [optionT_run_bind, OptionT.run_liftM_run, hV] at hxnone
  simp only [simulateQ_pure, _root_.map_pure, pure_bind, Option.getM,
    OptionT.run_map, OptionT.run_pure, Option.map_some, support_pure,
    Set.mem_singleton_iff, reduceCtorEq] at hxnone
/-- **The honest after-outer statement is in the (corrected, claim-true) `midRelation`.**

The intermediate statement produced by the honest outer phase — the input oracles retained, the
honest multiplicity and helper oracles attached, and any challenges `x`/`batch` — satisfies the
zero LogUp outer sumcheck claim `logupOuterSumcheckClaim … = 0`, *given* the input relation (the
lookup is valid) and pole-freeness of `x` (exactly the verifier's acceptance predicate
`outerVerifyAccepts`, the event whose complement is the `logupCompletenessError` pole bound).

This is the grand-sum identity content (`honest_helper_sum_zero_of_inputRelation_all` /
`grandSum_identity`) threaded through `LogupSumcheckBridge.of_honest`; it is the new membership
obligation of the completeness predicate after `midRelation` was corrected from `Set.univ` to the
claim-true relation (issue #13). -/
theorem honest_after_outer_mem_midRelation
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (hRel : ((stmtIn, ()) ∈ inputRelation F n M))
    (x : F) (batch : BatchingChallenge F n params.numGroups)
    (hacc : outerVerifyAccepts F n M stmtIn.2 x) (wit : Unit) :
    ((show StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i) from
      ({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
       fun
        | .input i => stmtIn.2 i
        | .multiplicity => honestMultiplicity stmtIn.2
        | .helpers => honestHelpers params stmtIn.2 x)), wit) ∈ midRelation F n M params :=
  (LogupSumcheckBridge.of_honest F n M params
    stmtIn.1 stmtIn.2
    { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
    hRel hacc).claimZero

set_option maxHeartbeats 3200000 in
/-- **Per-(initial-state) agreement for the simulated outer run.** On every *successful* simulated
outer run the honest prover's output statement equals the verifier's recomputed one **and**
satisfies the claim-true `midRelation` (via the grand-sum identity, from the input relation and
the acceptance predicate), so the completeness predicate's complement has probability `0`.
Discharges the `hAgree` obligation of
`probEvent_outerCompletenessRunComp_compl_eq_zero_of_perState`. -/
theorem outer_perState_agree
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params)
    (hRel : (stmtIn, witIn) ∈ inputRelation F n M)
    (s : σ) :
    probEvent (fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
        ¬ ((stmtOut, witOut) ∈ midRelation F n M params ∧ prvStmtOut = stmtOut)) ((OptionT.mk ((simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
            StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' s)
        : OptionT ProbComp (OuterCompletenessRunResult F n M params))) = 0 := by
  classical
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim, ProximityPrize.Compatibility.DiscreteSupportSemantics.prEvent_eq_zero_iff]
  intro o ho hbad
  have hsub := _root_.support_simulateQ_run'_subset (impl.addLift challengeQueryImpl) _ s ho
  cases o with
  | none => exact hbad
  | some result =>
    rw [outerReduction_run_closed_form, optionT_lift_bind_run, outerProver_run_closed_form] at hsub
    simp only [outerProver, bind_pure_comp, map_pure, bind_assoc, pure_bind, liftM_pure,
      support_bind, Set.mem_iUnion,
      exists_prop] at hsub
    dsimp only [outerProverState] at hsub
    simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
      map_pure, support_pure,
      Set.mem_singleton_iff] at hsub
    obtain ⟨i, _, i_1, hi_1, hverif⟩ := hsub
    have hiEq : i_1 = fun x => (stmtIn.2, x) := Set.mem_singleton_iff.mp hi_1
    subst i_1
    obtain ⟨batch, _, x, rfl, hverif⟩ := hverif
    by_cases hacc : outerVerifyAccepts F n M stmtIn.2 i
    · -- Accept: the verifier collapses to its recomputed output, which the readback agreement
      -- (`outerProver_output_pair_eq_verifier_recompute`) shows equals the prover's output
      -- statement; that honest statement satisfies the claim-true `midRelation` by the grand-sum
      -- identity (`honest_after_outer_mem_midRelation`, from `hRel` + the acceptance `hacc`).
      have hx := (outerProver_transcript_challenge_readback
          (m₀ := honestMultiplicity stmtIn.2) (x := i)
          (m₂ := honestHelpers params stmtIn.2 i) (batch := batch)).1
      have hb := (outerProver_transcript_challenge_readback
          (m₀ := honestMultiplicity stmtIn.2) (x := i)
          (m₂ := honestHelpers params stmtIn.2 i) (batch := batch)).2
      rw [optionT_run_bind, outerVerifier_run_accept_eq_pure oSpec F n M params stmtIn _
          (hx.symm ▸ hacc)] at hverif
      simp only [liftM_pure, OptionT.run_pure, pure_bind, Option.getM] at hverif
      rw [← bind_pure_comp, optionT_run_bind, OptionT.run_pure, pure_bind] at hverif
      simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hverif
      obtain rfl := Option.some.inj hverif
      have hm := (outerProver_transcript_message_readback
          (m₀ := honestMultiplicity stmtIn.2) (x := i)
          (m₂ := honestHelpers params stmtIn.2 i) (batch := batch)).1
      have hh := (outerProver_transcript_message_readback
          (m₀ := honestMultiplicity stmtIn.2) (x := i)
          (m₂ := honestHelpers params stmtIn.2 i) (batch := batch)).2
      have hpair := outerProver_output_pair_eq_verifier_recompute (oSpec := oSpec)
        (oStmt := stmtIn.2) (x := i) (batch := batch)
        (hx := hx) (hb := hb) (hm := hm) (hh := hh)
      refine hbad ⟨?_, hpair⟩
      exact hpair ▸ honest_after_outer_mem_midRelation F n M params stmtIn hRel i batch hacc _
    · -- Reject: the verifier fails, so the run has no successful (`some`) output — `hverif` is absurd.
      have hx := (outerProver_transcript_challenge_readback
          (m₀ := honestMultiplicity stmtIn.2) (x := i)
          (m₂ := honestHelpers params stmtIn.2 i) (batch := batch)).1
      rw [optionT_run_bind, outerVerifier_run_reject_eq_none oSpec F n M params stmtIn _
          (hx.symm ▸ hacc)] at hverif
      simp only [liftM_pure, OptionT.run_pure, pure_bind, Option.getM] at hverif
      rw [← bind_pure_comp, failure_bind, OptionT.run_failure, support_pure] at hverif
      simp only [Set.mem_singleton_iff, reduceCtorEq] at hverif

/-- **Outer-phase completeness failure bound (now fully proved).** The standard outer-completeness
run fails (returns `⊥`) with probability at most `logupCompletenessError`.  This discharges the
`hFailure` half of `OuterCompletenessRunFactsResidual` end-to-end: the run-level plumbing of
`probFailure_outerCompletenessRunComp_le_of_perStateNone` is fed the per-(initial-state) pole bound
`outer_perState_none_le` (whose accept-zero step is now closed). The remaining content of the outer
completeness residual is purely the complement-zero (`hComplZero`) per-state agreement fact. -/
theorem outer_completenessRun_failure_le
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    prFail (outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn)
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  refine probFailure_outerCompletenessRunComp_le_of_perStateNone oSpec F n M params init impl
    stmtIn witIn (fun s => ?_)
  exact outer_perState_none_le oSpec F n M params impl stmtIn witIn s

/-- **Outer LogUp run-facts residual — fully discharged.** Both run-level facts are now proved:
complement-zero via `outer_perState_agree` (every successful run agrees) and the failure bound via
`outer_completenessRun_failure_le` (pole event). No `sorry`, no residual hypothesis. -/
theorem outer_completenessRunFactsResidual :
    OuterCompletenessRunFactsResidual oSpec F n M params init impl := by
  intro _
  refine ⟨fun stmtIn witIn hRel => ?_, fun stmtIn witIn _ => ?_⟩
  · exact probEvent_outerCompletenessRunComp_compl_eq_zero_of_perState oSpec F n M params init impl
      stmtIn witIn (fun s => outer_perState_agree oSpec F n M params impl stmtIn witIn hRel s)
  · exact outer_completenessRun_failure_le oSpec F n M params init impl stmtIn witIn

/-- **Outer LogUp completeness — fully proved (no residual).** The honest outer LogUp oracle
reduction is complete with error `logupCompletenessError F n`, for every `NeverFail` init state.
This closes the outer-phase completeness obligation of LogUp Protocol 2 (#13) end-to-end. -/
theorem outerOracleReduction_completeness (hInit : NeverFail init) :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) :=
  outer_completeness_of_runFacts oSpec F n M params init impl
    (outer_completenessRunFactsResidual oSpec F n M params init impl) hInit

/-- The outer completeness residual `OuterCompletenessRunResidual` itself is now provable. -/
theorem outerCompletenessRunResidual_proved :
    OuterCompletenessRunResidual oSpec F n M params init impl :=
  fun hInit => outerOracleReduction_completeness oSpec F n M params init impl hInit

/-- **LogUp completeness residual shrunk to the embedded sumcheck alone.** The `SubPhaseCompletenessResidual`
of LogUp Protocol 2 (#13) is a conjunction `outer-completeness ∧ sumcheck-completeness`.  The first
conjunct is now a *theorem* (`outerOracleReduction_completeness`), so under `NeverFail init` the whole
residual reduces to just the embedded sumcheck completeness — the only remaining (upstream) blocker on
the completeness side. -/
theorem subPhaseCompletenessResidual_of_sumcheck (hInit : NeverFail init)
    (hSum : (sumcheckOracleReduction oSpec F n M params).completeness init impl
      (midRelation F n M params) outputRelation 0) :
    SubPhaseCompletenessResidual oSpec F n M params init impl :=
  ⟨outerOracleReduction_completeness oSpec F n M params init impl hInit, hSum⟩

/-- The residual is definitionally the outer completeness theorem under `NeverFail init`. -/
theorem outerCompletenessRunResidual_iff :
    OuterCompletenessRunResidual oSpec F n M params init impl ↔
      (NeverFail init →
        (outerOracleReduction oSpec F n M params).completeness init impl
          (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)) :=
  Iff.rfl

end OuterCompleteness

end Logup

/- Axiom audit for the honest outer completeness frontier. -/
#print axioms Logup.optionT_liftM_run_getM_collapse
#print axioms Logup.OuterCompletenessRunResidual
#print axioms Logup.OuterCompletenessRunFactsResidual
#print axioms Logup.completenessFromRun_of_compl_zero_failure_bound
#print axioms Logup.outer_completeness_of_runFacts
#print axioms Logup.outer_completeness_of_runResidual
#print axioms Logup.outerCompletenessRunResidual_iff
#print axioms Logup.outerProver_runToRound_closed_form
#print axioms Logup.outerProver_run_closed_form
#print axioms Logup.outerReduction_run_closed_form
#print axioms Logup.getChallenge_simulateQ_eq
#print axioms Logup.probEvent_outerVerify_reject_challenge_le
#print axioms Logup.outerVerifier_run_accept_eq_pure
#print axioms Logup.outer_perState_none_le
#print axioms Logup.honest_after_outer_mem_midRelation
#print axioms Logup.outer_perState_agree
#print axioms Logup.outer_completenessRun_failure_le
#print axioms Logup.outer_completenessRunFactsResidual
#print axioms Logup.outerOracleReduction_completeness
#print axioms Logup.outerCompletenessRunResidual_proved
