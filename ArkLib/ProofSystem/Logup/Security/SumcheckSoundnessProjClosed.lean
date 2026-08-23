/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckLensProjSound
import ArkLib.ProofSystem.Logup.Security.MarginalBridgeProof

/-!
# LogUp Protocol 2 — sum-check soundness residual with `hProj` CLOSED (issue #13)

This file welds the discharged lens projection soundness
`Logup.SumcheckLensProjSound_holds` (`Security/SumcheckLensProjSound.lean`) into the LogUp
embedded sum-check soundness chain, **eliminating the `hProj` named hypothesis** from
`Logup.sumcheckSoundnessResidual_holds_of_rbr` / `Logup.sumcheckSoundnessResidual_holds_wired`.

## The chosen inner language and why the downstream chain accepts it

`SumcheckLensProjSound_holds` discharges the projection soundness for the inner language

* `innerLangIn := logupSumcheckInputLanguage F n M params hSigns`
  `= (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (signDomain F hSigns) 0).language`,

the generic round-`0` sum-check language. This is exactly the round-`0` member of the per-round
language chain `lang i := (relationRound … i).language` for which the in-tree generic sum-check
development states its per-round round-by-round facts
(`Sumcheck.Spec` single-round bridges are stated `relationRound i.castSucc → relationRound i.succ`,
see `SingleRound.lean`), and which the multi-round assembly keystone
(`Sumcheck.Spec.oracleVerifier_rbrSoundness_of_round_append`, `SeqComposeRbrSoundness.lean`)
threads as `lang 0`. The remaining `hInnerRbr` slot below is therefore stated at *that* language —
the inner multi-round RBR fact the framework layer is assembling lands in this slot without any
language translation.

## What is closed and what remains

Closed here (all proven, axiom-clean):

* `hProj` — by `SumcheckLensProjSound_holds` (the round-`0` sum of the projected LogUp `Q`
  polynomial equals `logupOuterSumcheckClaim` unconditionally, so a nonzero mid-claim projects
  outside the round-`0` language);
* `hMarginal` — by the proven `Verifier.marginalBridge_holds` under the three standard
  honest-`impl` side conditions (state-preserving / never-failing / value-blind);
* `hRbrToSound` — already closed by `sumcheckRbrToSound` inside
  `sumcheckSoundnessResidual_holds_of_rbr`.

Remaining named hypotheses (genuine upstream residuals, supplied by their own bricks):

* `hError` — the union-bound error equation `sumcheckSoundnessError = ∑ i, rbrSoundnessError i`
  (pure bookkeeping, chosen by the caller);
* `hInnerRbr` — the inner concrete sum-check oracle reduction's multi-round round-by-round
  soundness *from* `logupSumcheckInputLanguage` *into* `Set.univ` (the oracle-level multi-round
  sum-check keystone);
* `himplSP`/`himplNF`/`himplVB` — the three standard honest-`impl` side conditions (the same three
  the downstream consumer `Logup.issue13_soundness_msgSeam` threads).

## Scope note: `midLanguage` vs `midSoundnessProtocolLanguage`

This closes `hProj` for the chain over the historical intermediate language `midLanguage`
(`SumcheckSoundnessResidual`). The corrected-language chain
(`SumcheckLensProjSoundFor … (midSoundnessProtocolLanguage …) …`, consumed by
`issue13_soundness_msgSeam_wiredSumcheck`) **cannot** be discharged at this inner language, and
provably so: take a bad-lookup input-oracle family, an `xChallenge` that is not a root of its
grand-sum check polynomial (so the pair is *outside* `midSoundnessProtocolLanguage`), and
adversarial `helpers ≡ 0` with `batchingScalars ≡ 0`. Then `qOnHypercube` vanishes identically
(each summand is `evalOnHypercube 0 u + Λ·0·domainIdentityTerm = 0`), so
`logupOuterSumcheckClaim = 0` and the projection lands *inside* the round-`0`
sum-check language. The corrected-language projection condition is therefore not a per-statement
algebraic fact at all — the missing content there is the *probabilistic* batching/zero-check step
(over `zChallenge`/`batchingScalars`), which belongs to the outer-phase soundness half, not to the
lens projection. Hence no `SumcheckLensProjSoundFor`-at-`midSoundnessProtocolLanguage` theorem is
(or honestly can be) provided here.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Logup

section SumcheckSoundnessProjClosed

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`); mirrors the named local instances used throughout the LogUp
security development. -/
local instance instInhabitedFieldSumcheckSoundnessProjClosed : Inhabited F := ⟨0⟩

/-- **`SumcheckSoundnessResidual` with `hProj` CLOSED (issue #13).**

`Logup.sumcheckSoundnessResidual_holds_of_rbr` with

* its `hProj` slot discharged by the proven `SumcheckLensProjSound_holds` at the inner language
  `logupSumcheckInputLanguage F n M params (Fact.out : (-1 : F) ≠ 1)` (the generic round-`0`
  sum-check language `(relationRound … 0).language`), and
* its `hMarginal` slot discharged by the proven `Verifier.marginalBridge_holds` under the three
  standard honest-`impl` side conditions.

The remaining inputs are the union-bound error equation `hError`, the inner multi-round
round-by-round soundness `hInnerRbr` — now pinned to the *canonical* inner language, exactly the
`lang 0 = (relationRound … 0).language` member of the per-round language chain that the generic
sum-check multi-round RBR assembly (`Sumcheck.Spec.oracleVerifier_rbrSoundness_of_round_append`)
produces — and the three honest-`impl` conditions. -/
theorem sumcheckSoundnessResidual_holds_projClosed
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        (logupSumcheckInputLanguage F n M params (Fact.out : (-1 : F) ≠ 1))
        (Set.univ) rbrSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  sumcheckSoundnessResidual_holds_of_rbr oSpec F n M params init impl sumcheckSoundnessError
    hError
    (SumcheckLensProjSound_holds oSpec F n M params (Fact.out : (-1 : F) ≠ 1))
    hInnerRbr
    (Verifier.marginalBridge_holds himplSP himplNF himplVB)

end SumcheckSoundnessProjClosed

end Logup

/- Axiom audit for the hProj-closed #13 sum-check soundness residual. -/

