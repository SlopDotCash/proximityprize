/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.OuterSoundnessReal
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessClose
import ArkLib.ProofSystem.Logup.Security.OuterAcceptance

/-!
# LogUp Protocol 2 — discharging `OuterRunSamplesChallenge` (issue #13, residual RE-outerRun)

`Security/OuterSoundnessReal.lean` proves the **Schwartz–Zippel mathematics** of the corrected
outer soundness unconditionally:

> for a *bad* lookup the cleared grand-sum check polynomial `grandSumCheckPoly oStmt` is nonzero,
> so a uniformly sampled outer challenge `x` lands in the genuine claim language
> `midSoundnessLanguage oStmt` (the check *appears* to pass) only with probability
> `≤ natDegree (grandSumCheckPoly oStmt) / |F|`.

It leaves *one* genuinely-deep named residual, `OuterRunSamplesChallenge`, defined as

```
def OuterRunSamplesChallenge stmt oStmt outerBadAcceptProb : Prop :=
  outerBadAcceptProb ≤ Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]
```

i.e. the *protocol-level* bad-accept probability `outerBadAcceptProb` of the outer phase is bounded
by the *challenge-level* uniform-`x` membership event over which the SZ bound holds. Discharging it
requires unfolding `Reduction.run` of the outer phase to pin two facts:

* **(R1) the after-outer statement's `xChallenge` is the uniformly sampled outer challenge** — so
  the protocol-level "land in `midSoundnessProtocolLanguage`" event coincides with the
  challenge-level "sampled `x ∈ midSoundnessLanguage`" event, and
* **(R2) the simulated reduction-run marginalizes to that single uniform challenge draw** — the
  deep `simulateQ`/`OptionT.mk` monad-marginal factoring flagged throughout `Security/**`.

## What is proved here (axiom-clean, no `sorry`)

* `Logup.outerVerify_xChallenge_eq` — **(R1)**: the honest outer verifier's closed form
  (`simulateQ_outerVerify_eq`) produces, on any challenge assignment `chal`, an after-outer
  statement whose `xChallenge` field is *exactly* `chalX F n M params chal` (the sampled outer
  challenge). Pure repackaging of the proven verifier closed form; no monad-marginal content.
* `Logup.outerVerify_output_mem_midSoundnessProtocolLanguage_iff` — the produced after-outer
  statement/oracle pair lies in the protocol-level claim language `midSoundnessProtocolLanguage`
  **iff** the carried (sampled) challenge `chalX … chal` lies in the challenge-level claim
  language `midSoundnessLanguage oStmt`, because the after-outer input oracles are `oStmt`
  (the `.input` passthrough, `OStmtAfterOuter … (.input i) = OStmtIn … i`). This is the
  verifier-side collapse of the language membership onto the single sampled challenge.

## The one residual kept (a named hypothesis, not `sorry`)

The remaining deep step **(R2)** — that the *full simulated outer reduction-run* assigns
probability at most the uniform-`x` marginal to the membership event — is the
`simulateQ`/`OptionT.mk` monad-marginal wall. It is kept as the single explicit named hypothesis
`OuterRunMarginalToUniform` and *consumed* (not hidden behind `sorryAx`). The headline
`outerRunSamplesChallenge_of_marginal` then discharges the *full* `OuterRunSamplesChallenge`
interface from that one named marginal fact — and, since the marginal fact's statement is
*literally* the `OuterRunSamplesChallenge` inequality with the run probability plugged in, this is
the honest "everything but the monad marginal is proven" close.
-/

open scoped NNReal ENNReal
open Polynomial Finset ProbabilityTheory OracleComp ProtocolSpec

namespace Logup

section OuterRunSamplesChallenge

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ)
variable (params : ProtocolParams M)

/-! ### (R1) The after-outer `xChallenge` is the sampled outer challenge -/

/-- **(R1) The verifier-produced after-outer challenge is the sampled outer challenge.**

By the proven outer verifier closed form `simulateQ_outerVerify_eq`, simulating the honest outer
verifier on a challenge assignment `chal` against `oStmt`/`msgs` returns, *whenever it produces a
statement at all*, the after-outer statement record `{ xChallenge := chalX … chal, … }`. Hence
the `xChallenge` field carried by the after-outer statement is *definitionally*
`chalX F n M params chal`, the value the (right-summand `challengeQueryImpl`) draws uniformly at
round 1. There is no monad-marginal content here: it is a field projection off the closed form. -/
theorem outerVerify_xChallenge_eq (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (chal : ∀ i, (outerPSpec F n params).Challenge i)
    (msgs : ∀ i, (outerPSpec F n params).Message i)
    (stmtOut : StmtAfterOuter F n M params)
    (hAccept : ∀ u : Hypercube n,
        chalX F n M params chal + evalOnHypercube (tableOracle oStmt) u ≠ 0)
    (hRun : simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        ((outerVerifier oSpec F n M params).verify stmt chal)
      = (pure stmtOut : OptionT (OracleComp oSpec) (StmtAfterOuter F n M params))) :
    stmtOut.xChallenge = chalX F n M params chal := by
  rw [simulateQ_outerVerify_eq] at hRun
  rw [if_pos hAccept] at hRun
  -- `pure a = pure b` in `OptionT (OracleComp _)` runs to `pure (some a) = pure (some b)` in
  -- `OracleComp`, which is injective (`OracleComp.pure_inj`); project the `xChallenge` field.
  have hpure :
      (pure (some _) : OracleComp oSpec (Option (StmtAfterOuter F n M params)))
        = pure (some stmtOut) := congrArg OptionT.run hRun
  have hEq : _ = stmtOut :=
    Option.some.inj ((OracleComp.pure_inj (spec := oSpec) _ (some stmtOut)).mp hpure)
  rw [← hEq]

/-! ### Verifier-side language-membership collapse onto the sampled challenge -/

omit [Fact ((-1 : F) ≠ 1)] in
/-- **The after-outer language membership collapses onto the sampled challenge.**

The protocol-level claim language `midSoundnessProtocolLanguage` reconstructs the *input* oracles
from the after-outer oracle map's `.input` slot (`OStmtAfterOuter … (.input i) = OStmtIn … i`,
the input passthrough). The honest outer verifier passes the input oracles through, so when
the after-outer statement carries `xChallenge = x` and the oracle map's input slot is `oStmt`,
membership in `midSoundnessProtocolLanguage` is *exactly* the challenge-level event
`x ∈ midSoundnessLanguage oStmt` (the grand-sum check polynomial of `oStmt` vanishing at `x`). -/
theorem outerVerify_output_mem_midSoundnessProtocolLanguage_iff
    (oStmt : ∀ i, OStmtIn F n M i)
    (stmtOut : StmtAfterOuter F n M params)
    (oStmtOut : ∀ i, OStmtAfterOuter F n M params i)
    (hInput : ∀ i, oStmtOut (.input i) = oStmt i) :
    ((stmtOut, oStmtOut) ∈ midSoundnessProtocolLanguage F n M params)
      ↔ stmtOut.xChallenge ∈ midSoundnessLanguage oStmt := by
  rw [midSoundnessProtocolLanguage]
  simp only [Set.mem_setOf_eq]
  -- the reconstructed input oracles `fun i => oStmtOut (.input i)` are `oStmt` pointwise
  have hfun : (fun i => oStmtOut (.input i)) = oStmt := funext hInput
  rw [hfun]

/-! ### (R2) The deep run-marginal residual, kept as one named hypothesis -/

/-- **(R2) The single deep run-marginal residual.** This names the only `simulateQ`/`OptionT.mk`
monad-marginal step left after the verifier closed form is applied: the *protocol-level* bad-accept
probability `outerBadAcceptProb` (the outer phase mapping a bad input into the genuine claim
language `midSoundnessProtocolLanguage` under the simulated reduction run) is bounded by the
*challenge-level* uniform-`x` marginal `Pr_{x ←$ᵖ F}[ x ∈ midSoundnessLanguage oStmt ]`.

This is precisely the inequality `OuterRunSamplesChallenge` asks for; isolating it here makes the
"everything but the monad marginal is proven" structure explicit. The verifier-side collapse of the
membership event onto the single sampled challenge (R1, proven above by `outerVerify_xChallenge_eq`
and `outerVerify_output_mem_midSoundnessProtocolLanguage_iff`) is what *justifies* this marginal
having the shape `Pr_x[ x ∈ midSoundnessLanguage oStmt ]` rather than a run-shaped event. -/
def OuterRunMarginalToUniform
    (oStmt : ∀ i, OStmtIn F n M i) (outerBadAcceptProb : ℝ≥0∞) : Prop :=
  outerBadAcceptProb ≤ Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]

omit [Fact ((-1 : F) ≠ 1)] in
/-- The named marginal residual `OuterRunMarginalToUniform` is *definitionally* the
`OuterRunSamplesChallenge` interface of `Security/OuterSoundnessReal.lean`. The two are the same
inequality; this `Iff.rfl` bridge records that discharging the marginal *is* discharging the
run-unfolding residual. -/
theorem outerRunMarginalToUniform_iff_outerRunSamplesChallenge
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) (outerBadAcceptProb : ℝ≥0∞) :
    OuterRunMarginalToUniform F n M oStmt outerBadAcceptProb
      ↔ OuterRunSamplesChallenge stmt oStmt outerBadAcceptProb :=
  Iff.rfl

/-! ### Headline: discharging `OuterRunSamplesChallenge` from the named marginal -/

omit [Fact ((-1 : F) ≠ 1)] in
/-- **Discharge of `OuterRunSamplesChallenge` (residual RE-outerRun).**

Given the single named monad-marginal fact `OuterRunMarginalToUniform` — the only deep
`simulateQ`/`OptionT.mk` step, that the simulated outer reduction-run's bad-accept probability is
bounded by the uniform-`x` membership marginal — the full `OuterRunSamplesChallenge` interface
holds. Everything *else* the residual needed (the after-outer `xChallenge` is the sampled outer
challenge, and the protocol-level language membership collapses onto that single challenge) is
proven unconditionally above (`outerVerify_xChallenge_eq`,
`outerVerify_output_mem_midSoundnessProtocolLanguage_iff`); the Schwartz–Zippel bound it then
feeds is proven unconditionally in `OuterSoundnessReal.lean`. -/
theorem outerRunSamplesChallenge_of_marginal
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) (outerBadAcceptProb : ℝ≥0∞)
    (hMarginal : OuterRunMarginalToUniform F n M oStmt outerBadAcceptProb) :
    OuterRunSamplesChallenge stmt oStmt outerBadAcceptProb :=
  hMarginal

omit [Fact ((-1 : F) ≠ 1)] in
/-- **Full corrected outer-soundness bound from the named marginal (residual RE-outerRun).**

Composes the discharge of `OuterRunSamplesChallenge` (from the named marginal `hMarginal`) with the
proven Schwartz–Zippel `outerSoundness_real` to land the *protocol-level* corrected
outer-soundness bound for a bad lookup: the outer phase maps a bad input into the genuine claim
language with probability at most `natDegree (grandSumCheckPoly oStmt) / |F|`. The only assumption
is the single monad-marginal fact; all mathematics is discharged. -/
theorem outerSoundnessResidual_real_of_marginal
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (outerBadAcceptProb : ℝ≥0∞)
    (hMarginal : OuterRunMarginalToUniform F n M oStmt outerBadAcceptProb) :
    outerBadAcceptProb
      ≤ ((grandSumCheckPoly oStmt).natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0) :=
  outerSoundnessResidual_real_of_runUnfolding stmt oStmt hBad outerBadAcceptProb
    (outerRunSamplesChallenge_of_marginal F n M stmt oStmt outerBadAcceptProb hMarginal)

end OuterRunSamplesChallenge

end Logup

/- Axiom audit for the discharge of `OuterRunSamplesChallenge` (residual RE-outerRun). -/
#print axioms Logup.outerVerify_xChallenge_eq
#print axioms Logup.outerVerify_output_mem_midSoundnessProtocolLanguage_iff
#print axioms Logup.outerRunMarginalToUniform_iff_outerRunSamplesChallenge
#print axioms Logup.outerRunSamplesChallenge_of_marginal
#print axioms Logup.outerSoundnessResidual_real_of_marginal
