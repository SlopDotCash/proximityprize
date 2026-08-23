/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessMsgSeam
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessPointwise
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessWired
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessFinal
import ArkLib.ProofSystem.Logup.Security.OuterMaliciousSoundness
import ArkLib.ProofSystem.Logup.Security.OuterSoundnessSharp
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessUncond
import ArkLib.ProofSystem.Logup.Security.SumcheckSoundnessProjClosed
import ArkLib.ProofSystem.Logup.Security.SumcheckSoundnessWired

/-!
# LogUp Protocol 2 — issue #13 final status

This file is the **single entry point** documenting and re-exporting the strongest in-tree LogUp
Protocol 2 completeness and soundness closures relevant to issue #13.

The original issue named three blockers: outer pole/grand-sum algebra, lifted sumcheck
completeness/soundness, and append composition.  The current tree has closed the purely mechanical
parts of those blockers:

* the soundness append blocker is discharged for LogUp's message seam by
  `logup_soundness_msgSeam`;
* the completeness append blocker is discharged for the general non-perfect outer error by
  `logup_completeness_wired`;
* the embedded-sumcheck completeness is fully discharged by
  `sumcheckCompletenessResidual_unconditional` (no honest-support hypothesis: the historical
  globally-quantified `hHonest` was unsatisfiable and has been removed — issue #13, dmvt audit);
* the embedded-sumcheck soundness marginal bridge is wired by
  `sumcheckVerifier_soundness_forLang_wired`, including the corrected intermediate language used by
  the final soundness close.

What remains in the strongest statements is now the genuinely semantic surface: the corrected outer
soundness theorem, the projection/RBR ingredients for the embedded sumcheck soundness, and honest
implementation/support assumptions needed by the probabilistic framework.  These are explicit
hypotheses, not hidden `sorryAx` placeholders.

## Headline entry points

* `Logup.issue13_soundness_end_to_end` — the current end-to-end LogUp Protocol 2 soundness
  capstone.  The outer malicious-prover algebra, lifted embedded-sumcheck rejection, and
  message-seam append composition are all discharged; the only assumptions left are
  non-degeneracy/cardinality facts and the standard state-preserving / never-failing /
  value-blind shared-oracle implementation conditions.

* `Logup.issue13_completeness_final` — the current end-to-end LogUp Protocol 2 completeness
  capstone.  The outer pole-rejection half, embedded-sumcheck completeness, and non-perfect append
  composition are all discharged; the theorem assumes only the standard init/support and
  honest-implementation side conditions.

* `Logup.issue13_soundness` — the headline LogUp Protocol 2 soundness, reduced to the **minimal**
  named residual set `{hOuter, hSumcheck, hPlainAppend}` (a straight re-export of
  `logup_soundness_uncond`). The deep oracle routing of the append seam has been discharged by the
  proven binary fusion; what remains is the corrected outer Schwartz–Zippel half over the
  non-degenerate `midSoundnessProtocolLanguage`, the embedded-sumcheck `liftContext` half over the
  same language, and the plain-verifier malicious-prover seam union bound.

* `Logup.issue13_soundness_msgSeam_wiredSumcheck` — soundness with the append blocker and
  generic RBR-to-plain marginal bridge closed; it takes the corrected outer half, the sumcheck
  projection and inner-RBR facts, the union-bound error equation, and the honest-`impl` side
  conditions.

* `Logup.issue13_soundness_msgSeam_wiredRoundAppend` — the same soundness close with the inner
  multi-round sumcheck RBR fact further reduced to per-round RBR soundness plus the binary
  append-RBR keystone.

* `Logup.issue13_soundness_pointwiseSumcheck` — soundness over the historical zero-claim
  `midLanguage` with the embedded sumcheck and append seam discharged pointwise; its only protocol
  soundness input is outer soundness into `midLanguage`.

* `Logup.issue13_sumcheckSoundnessResidual_projClosed` — the historical embedded-sumcheck
  `SumcheckSoundnessResidual` with the lens projection algebra closed at the canonical round-0
  sumcheck language.

* `Logup.issue13_completeness_wired` — completeness with the outer half, embedded-sumcheck inner
  completeness, and the general non-perfect append blocker closed; it takes the honest support and
  honest-implementation assumptions that describe the actual honest run.

**Regime warning (audit 2026-06-10).** The conditional entry points whose `hOuter` slot is typed
at `midSoundnessProtocolLanguage` with the paper error — `issue13_soundness`,
`issue13_soundness_msgSeam`,
`issue13_soundness_msgSeam_wiredSumcheck`, `issue13_soundness_msgSeam_wiredRoundAppend` — are
**vacuously conditional in the typical (small-support, large-field) regime**: that `hOuter` is
refuted there by `prob_midSoundnessLanguage_ge_compl_support` (`OuterSoundnessSharp.lean`).  They
are kept as historical composition bricks only.  The live, discharged routes are
`issue13_soundness_end_to_end` (= `logup_soundness_end_to_end`, `OuterMaliciousSoundness.lean`,
over `midLanguage`) and `outerVerifier_soundness_sharp` (`OuterRbrSoundness.lean`, over the sharp
language).

No `sorry`/`sorryAx`/`admit`: every step is a real proof or an explicitly named hypothesis. The
axiom audit at the bottom confirms axiom-cleanliness (`propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section Issue13

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances (`instOuterPSpecChallengeSampleable`) used when stating `outerVerifier.soundness` and
the outer/sumcheck completeness obligations — matching the local instances used throughout the
LogUp security development. -/
local instance instInhabitedFieldIssue13 : Inhabited F := ⟨0⟩

/-! ### Issue #13 capstones — end-to-end soundness and completeness -/

/-- **Issue #13 — LogUp Protocol 2 soundness, end-to-end.**

This is the strongest current soundness headline: the outer malicious-prover RBR theorem,
pointwise embedded-sumcheck rejection, and LogUp message-seam append composition are all wired.
There are no `SubPhaseSoundnessResidual` / `SumcheckSoundnessResidual` / append residual
hypotheses left.  The remaining hypotheses are standard semantic side conditions:

* `hn` — a nonempty Boolean cube;
* `hpole` — a field large enough to make the pole denominator nonzero;
* `hnK` — enough batching groups for the `(z, lambda)` Schwartz-Zippel budget; and
* `himplSP` / `himplNF` / `himplVB` — state-preserving, never-failing, value-blind shared-oracle
  implementation assumptions. -/
theorem issue13_soundness_end_to_end [oSpec.Fintype] [oSpec.Inhabited]
    (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (hpole : 2 ^ n < Fintype.card F) (hnK : n ≤ params.numGroups)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_end_to_end oSpec F n M params init impl
    sumcheckSoundnessError hn hpole hnK himplSP himplNF himplVB

/-- **Issue #13 — LogUp Protocol 2 completeness, end-to-end.**

The outer completeness half, embedded-sumcheck completeness half, and non-perfect message-seam
append composition are discharged.  In particular this theorem does not consume the historical
`SubPhaseCompletenessResidual`, `SumcheckCompletenessResidual`, or append-completeness residual
front doors. -/
theorem issue13_completeness_final [oSpec.Fintype] [oSpec.Inhabited]
    (hn : 0 < n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_final oSpec F n M params init impl hn hInit hImplSupp
    himplSP himplNF himplVB

/-! ### Issue #13 soundness — minimal residual `{hOuter, hSumcheck, hPlainAppend}` -/

/-- **Issue #13 — LogUp Protocol 2 soundness (final status).**

The full LogUp verifier is sound from the input language into the (trivial) output language
`Set.univ` with the paper-shaped error
`logupSoundnessError F n M params sumcheckSoundnessError =
outerSoundnessError F n M params + sumcheckSoundnessError`. Everything mechanical — the
definitional `logupVerifier = OracleVerifier.append outerVerifier sumcheckVerifier`, the error
reconciliation, the `append_soundness` chaining, and crucially the **oracle routing of the append
seam** (discharged by the proven binary verifier fusion `oracleVerifier_append_toVerifier`) — is
closed. The smallest honest residual set:

* `hOuter` — the corrected protocol-level outer soundness over the non-degenerate
  `midSoundnessProtocolLanguage` (Schwartz–Zippel mathematics proven in `OuterSoundnessReal.lean`,
  run-marginal isolated to the proven `OuterRunMarginalToUniform`);
* `hSumcheck` — the embedded-sumcheck soundness over `midSoundnessProtocolLanguage` (the
  `liftContext` of generic sum-check soundness; `sumcheckSoundnessResidual_holds` supplies the
  `midLanguage` analogue);
* `hPlainAppend` — the **plain-verifier** append-soundness residual (malicious-prover seam
  decomposition + union bound, oracle routing already discharged).

This is a straight re-export of `logup_soundness_uncond`.

**VACUOUSLY CONDITIONAL in the typical regime (audit 2026-06-10).** The `hOuter` slot at
`midSoundnessProtocolLanguage` with the paper error is refuted in the typical (small-support,
large-field) regime by `prob_midSoundnessLanguage_ge_compl_support` (`OuterSoundnessSharp.lean`);
kept as a historical composition brick.  Live discharged route: `issue13_soundness_end_to_end`. -/
theorem issue13_soundness (sumcheckSoundnessError : ℝ≥0)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hSumcheck :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midSoundnessProtocolLanguage F n M params) outputRelation.language
        sumcheckSoundnessError)
    (hPlainAppend :
      (Verifier.append (outerVerifier oSpec F n M params).toVerifier
          (sumcheckVerifier oSpec F n M params).toVerifier).soundness init impl
        (inputRelation F n M).language outputRelation.language
        (outerSoundnessError F n M params + sumcheckSoundnessError)) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_uncond oSpec F n M params init impl sumcheckSoundnessError
    hOuter hSumcheck hPlainAppend

/-! The bundled-residual front door `issue13_soundness_of_residual` (re-export of
`logup_soundness_uncond_of_residual` over `LogupSoundnessUncondResidual`) was DELETED in the
#351 burn-down (2026-06-11): the bundle was shown uninstantiable in the typical regime by the
2026-06-10 audit (`prob_midSoundnessLanguage_ge_compl_support`, `OuterSoundnessSharp.lean`),
making it vacuously conditional.  Use `issue13_soundness` with the three obligations held
individually, or the live routes `issue13_soundness_end_to_end` /
`outerVerifier_soundness_sharp`. -/

/-- **Issue #13 — LogUp Protocol 2 soundness with the append blocker CLOSED (message seam).**

The plain-verifier append-soundness residual `hPlainAppend` of `issue13_soundness` is no longer a
hypothesis: LogUp's outer → sumcheck seam is a prover message (the embedded sumcheck opens with the
round-0 univariate polynomial), so the proven unconditional message-seam keystone
`Verifier.append_soundness_msg` discharges it (`LogupSoundnessMsgSeam.lean`).  The honest soundness
residual surface of issue #13 is now `{hOuter, hSumcheck}` plus `0 < n` and the three standard
honest-`impl` side conditions.  A straight re-export of `logup_soundness_msgSeam`. -/
theorem issue13_soundness_msgSeam (sumcheckSoundnessError : ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hSumcheck :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midSoundnessProtocolLanguage F n M params) outputRelation.language
        sumcheckSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_msgSeam oSpec F n M params init impl sumcheckSoundnessError hn
    hOuter hSumcheck himplSP himplNF himplVB

/-- **Issue #13 — pointwise sumcheck-and-append close over `midLanguage`.**

This route uses the proved pointwise rejection theorem for the LogUp-lifted sumcheck verifier:
outside `midLanguage`, the verifier fails outright.  Consequently the embedded-sumcheck soundness
half has error `0` and the message-seam append theorem discharges the composition.  The remaining
protocol soundness input is exactly the outer verifier's soundness into `midLanguage`; this is the
historical zero-claim language, not the sharp support-cleared outer language. -/
theorem issue13_soundness_pointwiseSumcheck [oSpec.Fintype] [oSpec.Inhabited]
    (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midLanguage F n M params)
        (outerSoundnessError F n M params))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_pointwiseSumcheck oSpec F n M params
    (init := init) (impl := impl) sumcheckSoundnessError hn hOuter
    himplSP himplNF himplVB

/-- **Issue #13 — soundness with the message seam and embedded-sumcheck marginal bridge wired.**

Compared with `issue13_soundness_msgSeam`, this theorem no longer assumes the embedded-sumcheck
plain soundness fact directly.  Instead it derives that fact from:

* a projection-soundness fact for the corrected intermediate language
  `midSoundnessProtocolLanguage`;
* inner round-by-round soundness of the concrete generic sumcheck verifier;
* the union-bound error equation; and
* the standard honest-`impl` side conditions, which also discharge the message-seam append theorem.

Thus the remaining soundness surface is the corrected outer soundness plus the genuinely algebraic /
inner-RBR ingredients of the embedded sumcheck. -/
theorem issue13_soundness_msgSeam_wiredSumcheck [oSpec.Fintype]
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hProj :
      SumcheckLensProjSoundFor oSpec F n M params
        (midSoundnessProtocolLanguage F n M params) innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  issue13_soundness_msgSeam oSpec F n M params init impl sumcheckSoundnessError hn
    hOuter
    (sumcheckVerifier_soundness_forLang_wired oSpec F n M params init impl
      (midSoundnessProtocolLanguage F n M params) sumcheckSoundnessError
      hError hProj hInnerRbr himplSP himplNF himplVB)
    himplSP himplNF himplVB

/-- **Issue #13 — historical embedded-sumcheck soundness with projection CLOSED.**

This re-exports `sumcheckSoundnessResidual_holds_projClosed`: the `hProj` lens-projection algebra is
no longer a hypothesis for the historical `SumcheckSoundnessResidual`.  It is discharged at the
canonical inner input language
`logupSumcheckInputLanguage F n M params (Fact.out : (-1 : F) ≠ 1)`, i.e. the generic sumcheck
round-0 relation.  The remaining inputs are the union-bound error equation, the inner multi-round
RBR theorem into `Set.univ`, and the standard honest-`impl` marginal-bridge side conditions. -/
theorem issue13_sumcheckSoundnessResidual_projClosed [oSpec.Fintype]
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
  sumcheckSoundnessResidual_holds_projClosed oSpec F n M params init impl
    sumcheckSoundnessError hError hInnerRbr himplSP himplNF himplVB

/-- **Issue #13 — language-generic message-seam soundness with inner sumcheck RBR assembled.**

This is the most reusable soundness composition theorem in this status module.  It accepts any
intermediate language `langMid`, an outer soundness proof into that language, and derives the
embedded-sumcheck soundness from:

* projection soundness for `langMid`;
* per-round RBR soundness of the generic single-round sumcheck verifier;
* the binary `Verifier.append` RBR keystone that assembles those rounds; and
* the usual union-bound/error and honest-`impl` side conditions.

The conclusion has additive error `outerError + sumcheckSoundnessError`, exactly matching the
language-generic message-seam composition theorem. -/
theorem issue13_soundness_msgSeam_anyMid_wiredRoundAppend [oSpec.Fintype]
    (langMid : Set (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)))
    (outerError sumcheckSoundnessError : ℝ≥0)
    (lang : (i : Fin (n + 1)) →
      Set (Sumcheck.Spec.StatementRound F n i ×
        (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
    (rbrSoundnessError :
      ∀ _ : Fin n,
        (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language langMid outerError)
    (hLast : lang (Fin.last n) = Set.univ)
    (hError : sumcheckSoundnessError =
      ∑ i : (logupSumcheckPSpec F n M params).ChallengeIdx,
        (fun combinedIdx =>
          letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) i)
    (hProj : SumcheckLensProjSoundFor oSpec F n M params langMid (lang 0))
    (hRound : ∀ i : Fin n,
      (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (outerError + sumcheckSoundnessError) :=
  logup_soundness_msgSeam_anyMid oSpec F n M params init impl langMid outerError
    sumcheckSoundnessError hn hOuter
    (sumcheckVerifier_soundness_forLang_wired_roundAppend oSpec F n M params init impl langMid
      sumcheckSoundnessError lang rbrSoundnessError hLast hError hProj hRound hAppend
      himplSP himplNF himplVB)
    himplSP himplNF himplVB

/-- **Issue #13 — paper-shaped soundness with inner multi-round RBR reduced to per-round facts.**

This specializes `issue13_soundness_msgSeam_anyMid_wiredRoundAppend` to the current
`midSoundnessProtocolLanguage` and paper-shaped outer error.  Compared with
`issue13_soundness_msgSeam_wiredSumcheck`, it no longer assumes the opaque inner multi-round RBR
fact directly. -/
theorem issue13_soundness_msgSeam_wiredRoundAppend [oSpec.Fintype]
    (sumcheckSoundnessError : ℝ≥0)
    (lang : (i : Fin (n + 1)) →
      Set (Sumcheck.Spec.StatementRound F n i ×
        (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
    (rbrSoundnessError :
      ∀ _ : Fin n,
        (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hLast : lang (Fin.last n) = Set.univ)
    (hError : sumcheckSoundnessError =
      ∑ i : (logupSumcheckPSpec F n M params).ChallengeIdx,
        (fun combinedIdx =>
          letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) i)
    (hProj :
      SumcheckLensProjSoundFor oSpec F n M params
        (midSoundnessProtocolLanguage F n M params) (lang 0))
    (hRound : ∀ i : Fin n,
      (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  issue13_soundness_msgSeam_anyMid_wiredRoundAppend oSpec F n M params init impl
    (midSoundnessProtocolLanguage F n M params) (outerSoundnessError F n M params)
    sumcheckSoundnessError lang rbrSoundnessError hn hOuter hLast hError hProj hRound hAppend
    himplSP himplNF himplVB

/-- **Issue #13 — sharp-language soundness route with inner multi-round RBR reduced.**

This version uses the support-cleared sharp outer language from `OuterSoundnessSharp.lean`, the
language for which the paper-sized Schwartz–Zippel outer bound is proved.  The remaining hypotheses
state the two protocol-level compatibility facts not hidden by the algebra: outer soundness into the
sharp language, and projection soundness of the embedded sumcheck from that same sharp language. -/
theorem issue13_soundness_msgSeam_sharp_wiredRoundAppend [oSpec.Fintype]
    (sumcheckSoundnessError : ℝ≥0)
    (lang : (i : Fin (n + 1)) →
      Set (Sumcheck.Spec.StatementRound F n i ×
        (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
    (rbrSoundnessError :
      ∀ _ : Fin n,
        (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguageSharp F n M params)
        (outerSoundnessError F n M params))
    (hLast : lang (Fin.last n) = Set.univ)
    (hError : sumcheckSoundnessError =
      ∑ i : (logupSumcheckPSpec F n M params).ChallengeIdx,
        (fun combinedIdx =>
          letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) i)
    (hProj :
      SumcheckLensProjSoundFor oSpec F n M params
        (midSoundnessProtocolLanguageSharp F n M params) (lang 0))
    (hRound : ∀ i : Fin n,
      (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  issue13_soundness_msgSeam_anyMid_wiredRoundAppend oSpec F n M params init impl
    (midSoundnessProtocolLanguageSharp F n M params) (outerSoundnessError F n M params)
    sumcheckSoundnessError lang rbrSoundnessError hn hOuter hLast hError hProj hRound hAppend
    himplSP himplNF himplVB

/-! ### Issue #13 completeness

The historical `issue13_completeness` front door is retained for callers that already package the
original `SubPhaseCompletenessResidual`.  The stronger `issue13_completeness_wired` below uses the
new non-perfect append keystone and the unconditional inner sumcheck completeness bridge, so it no
longer assumes the append residual or the embedded-sumcheck residual as opaque facts. -/

/-- **Issue #13 — LogUp Protocol 2 completeness (final status).**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n`
(`= |Hypercube n| / |F|`, the outer pole-rejection error plus the perfect sumcheck error `0`),
reduced through the
genuine sequential-composition completeness interface `OracleReduction.append_completeness`. The
remaining obligations:

* `h : SubPhaseCompletenessResidual …` — the two sub-phase completeness facts: the outer phase is
  complete with error `logupCompletenessError F n`, and the embedded sumcheck phase is *perfectly*
  complete. This bundle is itself a theorem under `{hInit, hImplSupp}`
  (`subPhaseCompletenessResidual_unconditional`, `SumcheckCompletenessUncond.lean`).
* `hAppendCompleteness : … .appendCompletenessResidual …` — the sequential-composition
  completeness fact carried as the explicit residual hypothesis by the `append_completeness` API.

This is a straight re-export of `logup_completeness_of_residual`. -/
theorem issue13_completeness
    (h : SubPhaseCompletenessResidual oSpec F n M params init impl)
    (hAppendCompleteness :
      (outerOracleReduction oSpec F n M params).appendCompletenessResidual
        (sumcheckOracleReduction oSpec F n M params) h.1 h.2) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_residual oSpec F n M params init impl h hAppendCompleteness

/-- **Issue #13 — LogUp Protocol 2 completeness with append and embedded sumcheck wired.**

The outer pole-rejection half is discharged by `outerCompletenessResidual_of_neverFail`; the
embedded-sumcheck half is supplied by the unconditional
`sumcheckCompletenessResidual_unconditional` (no honest-support hypothesis — the historical
globally-quantified `hHonest` was unsatisfiable and has been removed; issue #13, dmvt audit); and
the general non-perfect append composition is discharged by `logup_completeness_wired`. The only
remaining assumptions are the non-degeneracy `0 < n`, standard initialization/support facts, and
the honest-`impl` side conditions required by the message-seam completeness keystone — all of which
are *satisfiable* (see `logup_completeness_final_instantiable`,
`LogupCompletenessFinal.lean`, for a concrete `ZMod 5` instantiation). -/
theorem issue13_completeness_wired [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hn : 0 < n)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_wired oSpec F n M params init impl hInit
    (sumcheckCompletenessResidual_unconditional oSpec F n M params init impl hInit hImplSupp)
    (logupSumcheck_length_pos n hn)
    (by simpa [pSpec] using (logup_seam_dir F n M params hn))
    (logupSumcheckPSpec_first_dir F n M params hn)
    himplSP himplNF himplVB

end Issue13

end Logup

/- Axiom audit for the issue #13 final-status entry points. -/
#print axioms Logup.issue13_soundness_end_to_end
#print axioms Logup.issue13_completeness_final
#print axioms Logup.issue13_soundness
#print axioms Logup.issue13_soundness_msgSeam
#print axioms Logup.issue13_soundness_pointwiseSumcheck
#print axioms Logup.issue13_soundness_msgSeam_wiredSumcheck
#print axioms Logup.issue13_sumcheckSoundnessResidual_projClosed
#print axioms Logup.issue13_soundness_msgSeam_anyMid_wiredRoundAppend
#print axioms Logup.issue13_soundness_msgSeam_wiredRoundAppend
#print axioms Logup.issue13_soundness_msgSeam_sharp_wiredRoundAppend
#print axioms Logup.issue13_completeness
#print axioms Logup.issue13_completeness_wired
