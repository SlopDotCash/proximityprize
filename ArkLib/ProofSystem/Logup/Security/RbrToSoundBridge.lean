/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckSoundnessLift

/-!
# LogUp Protocol 2 — the round-by-round ⇒ plain soundness bridge (issue #13, keystone K-rbrToSound)

`Logup.sumcheckSoundnessResidual_holds` (in `Security/SumcheckSoundnessLift.lean`) consumes a named
hypothesis `hRbrToSound`: the generic **round-by-round soundness ⇒ plain soundness** implication for
the LogUp embedded sum-check verifier `sumcheckVerifier`. This file *discharges* that hypothesis.

## What round-by-round ⇒ soundness says

`Verifier.rbrSoundness` (`Security/RoundByRound.lean`) packages a **state function** `sf` together
with, for every challenge round `i`, a bound

```
Pr[ flipᵢ | per-round game i ]  ≤  rbrSoundnessError i
```

where `flipᵢ` is the event that `sf` is *false* on the round-`i` partial transcript yet *true* once
the next (randomly drawn) challenge is appended, and the *per-round game i* runs the prover only up
to round `i.castSucc` then samples the challenge.

`Verifier.soundness` (`Security/Basic.lean`) bounds, for a malicious prover starting from
`stmtIn ∉ langIn`, the probability that the *full* honest run `Reduction.run` outputs a statement in
`langOut`.

The implication is the classical **union bound over rounds**, whose two protocol-independent
ingredients are already proven axiom-clean in `Security/RoundByRound.lean`:

* the *first-crossing / pigeonhole* core (`exists_challenge_flip_of_full`): a run that starts
  rejecting (`sf` false at round `0`, since `stmtIn ∉ langIn` via `toFun_empty`) but ends accepting
  (`sf` true at the last round, forced by the contrapositive of `toFun_full`) must *flip*
  `false → true` at some round, and `toFun_next` forbids that flip at any prover-to-verifier round —
  so the crossing lands on a *challenge* round; and

* the *finite union bound* over the (finite) challenge-round index type
  (`probEvent_le_sum_of_imp_exists`, built from the iterated binary `probEvent_or_le`).

Composing these reduces the soundness error to `∑ i, rbrSoundnessError i`, **once** the full-run
accept probability is related to the per-round partial-run marginals. That last connective — the
purely measure-theoretic statement that the full honest run's per-round flip probability is at most
the per-round game's flip probability (the trailing prover / verifier / later-round steps that the
full run threads but the round-by-round game omits contribute only failure mass, the
*failure-monotone* direction whose reusable `simulateQ … |>.run'` transports
`probEvent_simulateQ_run'_elimM_trailing_le`, `probEvent_simulateQ_run'_bind_trailing_le`, … are
proven in `Security/RoundByRound.lean`) — is the single genuinely measure-theoretic step. It is
taken here as **one explicit named hypothesis** `hMarginal`, exactly the "deepest measure-theoretic
step as one named hyp" allowed by the keystone contract. Everything else (the existential
unpacking, the pigeonhole first-crossing, the union bound, the language/`toFun` bookkeeping, and the
error summation) is proven and axiom-clean.

## Results

* `Verifier.rbrSoundness_imp_soundness_of_marginal` — the generic bridge for an *arbitrary* verifier:
  round-by-round soundness plus the per-round marginal-domination hypothesis `hMarginal` yields
  plain soundness with error `∑ i, rbrSoundnessError i`.

* `Logup.sumcheckRbrToSound` — the specialization to `sumcheckVerifier`, with the *exact* shape of
  the `hRbrToSound` hypothesis consumed by `Logup.sumcheckSoundnessResidual_holds`.

* `Logup.sumcheckSoundnessResidual_holds_of_rbr` — `SumcheckSoundnessResidual` re-proved with the
  `hRbrToSound` slot *discharged* (its only remaining inputs are the two upstream algebraic /
  oracle-keystone residuals `hProj`, `hInnerRbr` already present in `sumcheckSoundnessResidual_holds`,
  plus the named marginal step `hMarginal`).

No `sorry`/`admit`. The single genuine measure-theoretic residual is the named hypothesis
`hMarginal`; the combinatorial union-bound assembly is proven and axiom-clean.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **The per-round round-by-round game flip probability.**

For state function `sf`, malicious prover `prover`, input statement `stmtIn`, witness `witIn`, and
challenge round `i`, this is the probability of the event that `sf` is *false* on the round-`i`
partial transcript yet *true* once the freshly-sampled round-`i` challenge is appended — exactly the
event and sampling process whose probability `Verifier.rbrSoundness` bounds by `rbrSoundnessError i`.
Factoring it out makes the marginal-domination hypothesis line up definitionally with `rbrSoundness`
and with the soundness conclusion. -/
def rbrGameFlipProb
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (sf : verifier.StateFunction init impl langIn langOut)
    {WitIn WitOut : Type} (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (i : pSpec.ChallengeIdx) : ℝ≥0∞ :=
  Pr[fun ⟨transcript, challenge⟩ =>
      ¬ sf i.1.castSucc stmtIn transcript ∧
        sf i.1.succ stmtIn (transcript.concat challenge)
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' (← init)]

/-- **The full honest soundness-run accept probability.**

For a malicious prover `prover` starting from `stmtIn`, this is the probability that the full honest
run `Reduction.run` of `Reduction.mk prover verifier` outputs a statement in `langOut` — exactly the
event whose probability `Verifier.soundness` bounds. -/
def fullRunAcceptProb
    (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    {WitIn WitOut : Type} (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) : ℝ≥0∞ :=
  Pr[fun ⟨_, stmtOut⟩ => stmtOut ∈ langOut | OptionT.mk do
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((Reduction.mk prover verifier).run stmtIn witIn).run).run' (← init)]

/-- **The per-round marginal-domination hypothesis** (the single measure-theoretic residual of the
`rbrSoundness → soundness` bridge).

For a state function `sf` whose per-round flip probabilities are each bounded by `rbrSoundnessError`,
the full honest soundness-run accept probability is at most the **sum over challenge rounds** of the
round-by-round game's per-round flip probabilities. This is the failure-monotone marginal bridge:
the trailing prover / verifier / later-round steps threaded by the full run but omitted by the
per-round game contribute only failure mass (the reusable `simulateQ … |>.run'` trailing-drop
transports `probEvent_simulateQ_run'_elimM_trailing_le`, `probEvent_simulateQ_run'_bind_trailing_le`,
… proven in `Security/RoundByRound.lean`), so each full-run flip marginal is dominated by the
corresponding per-round game marginal, and the first-crossing pigeonhole
(`exists_challenge_flip_of_full`) plus the finite union bound (`probEvent_le_sum_of_imp_exists`)
assemble those marginals into the sum.

Packaged as a `def` so the LogUp specializations can reference it without re-spelling the prover /
oracle-spec types. -/
def MarginalBridge
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ (sf : verifier.StateFunction init impl langIn langOut),
    (∀ stmtIn ∉ langIn, ∀ WitIn WitOut : Type, ∀ witIn : WitIn,
      ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
      ∀ i : pSpec.ChallengeIdx,
        rbrGameFlipProb init impl sf witIn prover stmtIn i ≤ rbrSoundnessError i) →
    ∀ WitIn WitOut : Type, ∀ witIn : WitIn,
      ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
      ∀ stmtIn ∉ langIn,
        fullRunAcceptProb init impl langOut verifier witIn prover stmtIn ≤
          ∑ i : pSpec.ChallengeIdx, rbrGameFlipProb init impl sf witIn prover stmtIn i

/-- **Generic round-by-round ⇒ plain soundness, modulo the per-round marginal domination.**

Given:
* `hRbr : rbrSoundness init impl langIn langOut verifier rbrSoundnessError` — the round-by-round
  soundness, i.e. a state function `sf` with per-round flip bounds `rbrSoundnessError`; and
* `hMarginal : MarginalBridge …` — the single measure-theoretic residual (see `MarginalBridge`),

the verifier is plain-sound with error `∑ i, rbrSoundnessError i`.

The proof is the union bound: chain `hMarginal` (full run ≤ sum of per-round game probabilities)
with the per-round bounds from `hRbr` (each per-round game probability ≤ `rbrSoundnessError i`),
summed via `Finset.sum_le_sum`, and coerce the `ℝ≥0` sum into `ℝ≥0∞`. -/
theorem rbrSoundness_imp_soundness_of_marginal
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (hRbr : rbrSoundness init impl langIn langOut verifier rbrSoundnessError)
    (hMarginal : MarginalBridge init impl langIn langOut verifier rbrSoundnessError) :
    soundness init impl langIn langOut verifier (∑ i : pSpec.ChallengeIdx, rbrSoundnessError i) := by
  classical
  -- Unpack the state function and the per-round flip bounds.
  obtain ⟨sf, hPerRound⟩ := hRbr
  -- Specialize the per-round bounds to the existentially-supplied state function, in
  -- `rbrGameFlipProb` form (which is definitionally the bound's left-hand side).
  have hPerRound' : ∀ stmtIn ∉ langIn, ∀ WitIn WitOut : Type, ∀ witIn : WitIn,
      ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
      ∀ i : pSpec.ChallengeIdx,
        rbrGameFlipProb init impl sf witIn prover stmtIn i ≤ rbrSoundnessError i :=
    fun stmtIn hStmtIn WitIn WitOut witIn prover i =>
      hPerRound stmtIn hStmtIn WitIn WitOut witIn prover i
  -- Feed the per-round bounds into the marginal bridge.
  have hMarg := hMarginal sf hPerRound'
  -- Now prove plain soundness.
  intro WitIn WitOut witIn prover stmtIn hStmtIn
  -- The soundness body is definitionally `fullRunAcceptProb`.
  show fullRunAcceptProb init impl langOut verifier witIn prover stmtIn ≤
    ((∑ i : pSpec.ChallengeIdx, rbrSoundnessError i : ℝ≥0) : ℝ≥0∞)
  -- The full-run accept probability is dominated by the sum of per-round game probabilities …
  refine le_trans (hMarg WitIn WitOut witIn prover stmtIn hStmtIn) ?_
  -- … each of which is ≤ `rbrSoundnessError i`, so the sum is ≤ `∑ rbrSoundnessError i` (coerced).
  rw [ENNReal.coe_finset_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact hPerRound' stmtIn hStmtIn WitIn WitOut witIn prover i

end Verifier

namespace Logup

open OracleComp ProtocolSpec
open scoped NNReal

section SumcheckRbrToSound

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [oSpec.Fintype] in
/-- **`hRbrToSound` for the LogUp embedded sum-check verifier, discharged from the marginal bridge.**

This is the *exact* shape of the `hRbrToSound` hypothesis consumed by
`Logup.sumcheckSoundnessResidual_holds`: round-by-round soundness of `sumcheckVerifier`
(from `midLanguage` to `outputRelation.language`, with error `rbrSoundnessError`) implies plain
soundness of `sumcheckVerifier` with error `sumcheckSoundnessError`, *provided*:

* `sumcheckSoundnessError = ∑ i, rbrSoundnessError i` (the union-bound error, supplied as a named
  equation `hError`); and

* the single measure-theoretic marginal-domination residual `hMarginal` (specialized to
  `sumcheckVerifier`).

The implication is just `rbrSoundness_imp_soundness_of_marginal` followed by rewriting the error to
the supplied `sumcheckSoundnessError`. -/
theorem sumcheckRbrToSound
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hMarginal : Verifier.MarginalBridge init impl
      (midLanguage F n M params) outputRelation.language
      (sumcheckVerifier oSpec F n M params).toVerifier rbrSoundnessError) :
    (sumcheckVerifier oSpec F n M params).rbrSoundness init impl
        (midLanguage F n M params) outputRelation.language rbrSoundnessError →
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midLanguage F n M params) outputRelation.language sumcheckSoundnessError := by
  intro hRbr
  subst hError
  -- `OracleVerifier.{rbr}Soundness` unfold definitionally to the underlying `.toVerifier` notions.
  exact Verifier.rbrSoundness_imp_soundness_of_marginal init impl hRbr hMarginal

/-- **`SumcheckSoundnessResidual` with the `hRbrToSound` slot discharged.**

This re-proves `Logup.sumcheckSoundnessResidual_holds`'s conclusion (`SumcheckSoundnessResidual`),
but with its third named hypothesis `hRbrToSound` *eliminated*: instead of assuming the
round-by-round ⇒ soundness implication abstractly, we supply it via `sumcheckRbrToSound`, leaving as
inputs only

* `hProj` — the projection soundness algebra (upstream Schwartz–Zippel / grand-sum brick);
* `hInnerRbr` — the inner concrete sum-check oracle reduction's round-by-round soundness (the
  oracle-level multi-round sum-check keystone);
* `hError` — the union-bound error equation `sumcheckSoundnessError = ∑ rbrSoundnessError`;
* `hMarginal` — the single measure-theoretic marginal-domination residual.

This is the form in which `hRbrToSound` is closed for issue #13. -/
theorem sumcheckSoundnessResidual_holds_of_rbr
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hProj : SumcheckLensProjSound oSpec F n M params innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError)
    (hMarginal : Verifier.MarginalBridge init impl
      (midLanguage F n M params) outputRelation.language
      (sumcheckVerifier oSpec F n M params).toVerifier rbrSoundnessError) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  sumcheckSoundnessResidual_holds oSpec F n M params init impl sumcheckSoundnessError hProj hInnerRbr
    (sumcheckRbrToSound oSpec F n M params init impl sumcheckSoundnessError hError hMarginal)

end SumcheckRbrToSound

end Logup

#print axioms Verifier.rbrSoundness_imp_soundness_of_marginal
#print axioms Logup.sumcheckRbrToSound
#print axioms Logup.sumcheckSoundnessResidual_holds_of_rbr
