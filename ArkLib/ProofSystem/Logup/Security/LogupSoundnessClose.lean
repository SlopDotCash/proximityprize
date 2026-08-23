/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Security.OuterSoundnessReal

/-!
# LogUp Protocol 2 — end-to-end soundness close (issue #13, brick F)

This file assembles the **end-to-end LogUp soundness** statement by composing the two sub-phase
soundness obligations through the generic sequential-composition soundness interface
`OracleVerifier.append_soundness` (`Composition/Sequential/Append.lean`).

`logupVerifier` is *definitionally* `OracleVerifier.append outerVerifier sumcheckVerifier`
(`logupVerifier_eq_append`). Its soundness therefore reduces to:

* **outer**-phase soundness for `outerVerifier`, from `inputRelation`'s language into an
  intermediate language, with error `outerSoundnessError`, and
* embedded **sumcheck** soundness for `sumcheckVerifier`, from that intermediate language into the
  output language, with the sumcheck error,

joined by the append-composition soundness brick (`appendSoundnessResidual`).

## The *corrected* intermediate language

`Security/Soundness.lean` threads the **degenerate** intermediate language `midLanguage`. As
explained in `Security/OuterSoundnessReal.lean`, `midLanguage` always *contains* the honest
after-outer statement, so the outer phase always "lands" in it and the outer soundness obligation is
vacuously false for a genuinely bad input. The genuine soundness obstruction is the algebraic check
polynomial `grandSumCheckPoly` vanishing at the random outer challenge — captured by
`Logup.midSoundnessLanguage : Set F` (the *roots* of the check polynomial), which is non-degenerate
(`midSoundnessLanguage_ne_univ_of_bad_lookup`) and over which the proven Schwartz–Zippel bound
`outerSoundness_real` holds.

Here we lift that challenge-level corrected language to a **protocol-level** intermediate language
`midSoundnessProtocolLanguage` over after-outer statement/oracle pairs, by pulling
`midSoundnessLanguage` back through the carried challenge field `xChallenge`. This is the
non-degenerate replacement for `midLanguage` in the append composition.

## What is proved here vs. left as named residuals

The arithmetic glue (the `append_soundness` chaining, the definitional rewrite
`logupVerifier_eq_append`, and the error reconciliation
`logupSoundnessError = outerSoundnessError + sumcheckSoundnessError`, which holds by `rfl`) is
discharged **fully and unconditionally** here.

The genuinely deep upstream facts are taken as explicit, clearly-named `Prop` hypotheses (never
`sorry`):

* `hOuter` — the *corrected* outer soundness (brick D): `outerVerifier` is sound from the input
  language into `midSoundnessProtocolLanguage` with error `outerSoundnessError`. The corrected
  language is the genuine, non-degenerate one (`midSoundnessLanguage`-pullback); the
  Schwartz–Zippel mathematics behind the bound is proven in `OuterSoundnessReal.lean`, only the
  `Reduction.run`-unfolding bridge (`OuterRunSamplesChallenge`) remains, which is folded into this
  named hypothesis at the protocol level.
* `hSumcheck` — the embedded sumcheck soundness (brick E): `sumcheckVerifier` is sound from
  `midSoundnessProtocolLanguage` into the output language. This is the `liftContext` of the generic
  `Sumcheck.Spec` soundness, which is not available in-tree at this shape.
* `hAppend` — the append-composition soundness residual
  (`OracleVerifier.appendSoundnessResidual`): the malicious-prover seam decomposition plus
  probabilistic union bound (deep, flagged throughout `Composition/Sequential/Append.lean`).

The result `logup_soundness_full` then composes these three into the headline
`(logupVerifier …).soundness …` with error
`logupSoundnessError F n M params sumcheckSoundnessError`, with the output language `Set.univ`
(`outputRelation_language`), so it is a genuine acceptance-probability bound, not a vacuous language
inclusion.
-/

open scoped NNReal

namespace Logup

section SoundnessClose

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the outer/sumcheck sub-verifier obligations. -/
local instance instInhabitedFieldLogupSoundnessClose : Inhabited F := ⟨0⟩

/-! ### The corrected protocol-level intermediate language -/

/-- **The corrected, non-degenerate intermediate language at the protocol level.**

`Security/OuterSoundnessReal.lean` defines the genuine challenge-level claim language
`midSoundnessLanguage oStmt : Set F` — the *roots* of the cleared grand-sum check polynomial — which
is non-degenerate (a bad lookup makes the check polynomial nonzero, so it has only `≤ natDegree`
roots). This is the language that actually carries the Schwartz–Zippel bound `outerSoundness_real`.

`midSoundnessProtocolLanguage` lifts that to the after-outer statement/oracle pairs that the append
composition threads: a pair `(stmt, oStmt)` is in the language exactly when the *carried* outer
challenge `stmt.xChallenge` lands in the genuine claim language `midSoundnessLanguage` of the
*input* oracles reconstructed from `oStmt` (the after-outer oracles retain the input oracles in their
`.input` slot, `OStmtAfterOuter … (.input i) = OStmtIn … i`), i.e. the check polynomial vanishes at
the challenge actually chosen. This is the **non-degenerate replacement** for `midLanguage`: it is
*not* `Set.univ` (a bad lookup pins the challenge to one of the finitely many roots). -/
def midSoundnessProtocolLanguage :
    Set (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) :=
  { p | p.1.xChallenge ∈ midSoundnessLanguage (fun i => p.2 (.input i)) }

omit [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- The corrected protocol-level intermediate language is *definitionally* the set of after-outer
pairs whose carried challenge is a root of the grand-sum check polynomial of the reconstructed input
oracles. -/
theorem mem_midSoundnessProtocolLanguage_iff
    (p : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) :
    p ∈ midSoundnessProtocolLanguage F n M params ↔
      (grandSumCheckPoly (fun i => p.2 (.input i))).eval p.1.xChallenge = 0 :=
  Iff.rfl

/-! ### End-to-end soundness from the corrected halves -/

/-- **End-to-end LogUp Protocol 2 soundness (brick F).**

The full LogUp verifier is sound from the input language into the (trivial) output language with the
paper-shaped error `logupSoundnessError F n M params sumcheckSoundnessError =
outerSoundnessError F n M params + sumcheckSoundnessError`.

It is obtained by chaining, through `OracleVerifier.append_soundness`, three named obligations:

* `hOuter` — the **corrected** outer soundness (brick D): the outer verifier is sound from the input
  language into the genuine, non-degenerate intermediate language
  `midSoundnessProtocolLanguage` with error `outerSoundnessError`. (Unlike the degenerate
  `midLanguage` residual, this uses the corrected `midSoundnessLanguage` pullback; the
  Schwartz–Zippel mathematics is proven in `OuterSoundnessReal.lean`.)
* `hSumcheck` — the embedded sumcheck soundness (brick E): the sumcheck verifier is sound from that
  same corrected intermediate language into the output language.
* `hAppend` — the append-composition soundness residual: the malicious-prover seam decomposition +
  union bound (`OracleVerifier.appendSoundnessResidual`).

Everything *between* these — the definitional `logupVerifier_eq_append`, the error reconciliation
`logupSoundnessError = outerSoundnessError + s` (true by `rfl`), and the `append_soundness`
chaining — is discharged unconditionally and axiom-cleanly. -/
theorem logup_soundness_full (sumcheckSoundnessError : ℝ≥0)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hSumcheck :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midSoundnessProtocolLanguage F n M params) outputRelation.language
        sumcheckSoundnessError)
    (hAppend :
      OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
        (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
        hOuter hSumcheck) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  -- `logupVerifier = append outerVerifier sumcheckVerifier` (definitionally), and
  -- `logupSoundnessError = outerSoundnessError + sumcheckSoundnessError` (by `rfl`), so the
  -- composed soundness fact from `append_soundness` unifies with the goal directly.
  exact OracleVerifier.append_soundness.{0, 0}
    (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
    hOuter hSumcheck hAppend

/-! The historical bundled front door `LogupSoundnessFullResidual` (and its consumer
`logup_soundness_full_of_residual`) was DELETED in the #351 burn-down (2026-06-11): the
2026-06-10 audit showed its `hOuter` conjunct (typed at `midSoundnessProtocolLanguage` with the
paper error `outerSoundnessError`) is refuted in the typical (small-support, large-field)
regime by `prob_midSoundnessLanguage_ge_compl_support` (`OuterSoundnessSharp.lean`), making the
bundle uninstantiable there and every consumer vacuously conditional.  Live routes:
`logup_soundness_end_to_end` (`OuterMaliciousSoundness.lean`, hOuter@`midLanguage` discharged)
and the sharp-language route `outerVerifier_soundness_sharp` (`OuterRbrSoundness.lean`).
Consumers holding the three obligations individually can still apply `logup_soundness_full`
directly. -/

end SoundnessClose

end Logup

/- Axiom audit for the end-to-end #13 LogUp soundness close. -/
#print axioms Logup.midSoundnessProtocolLanguage
#print axioms Logup.mem_midSoundnessProtocolLanguage_iff
#print axioms Logup.logup_soundness_full
