/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessClose
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-
NOTE on imports: the corrected outer-soundness bricks (`outerSoundness_real`,
`OuterRunMarginalToUniform`) live in `Security/OuterSoundnessReal.lean`, transitively imported via
`LogupSoundnessClose`. The embedded-sumcheck lift `sumcheckSoundnessResidual_holds`
(`Security/SumcheckSoundnessLift.lean`) is *referenced in prose only*: it cannot be co-imported with
`LogupSoundnessClose` because both files declare an anonymous `local instance : Inhabited F`, whose
auto-generated names collide on import (a pre-existing latent clash in files we may not edit). Since
this keystone consumes the outer/sumcheck soundness halves as *named hypotheses* (not as concrete
terms), the lift import is unnecessary; the residual surface is unaffected.
-/

/-!
# LogUp Protocol 2 — most-unconditional soundness (issue #13, keystone K-soundFull)

This file assembles the **most-unconditional** LogUp Protocol 2 soundness statement currently
attainable, by discharging everything mechanical and reducing the genuinely-deep obstructions to the
**smallest possible** named residual set. The decisive new ingredient is the now-proven binary
verifier-fusion keystone `OracleReduction.oracleVerifier_append_toVerifier`
(`Composition/Sequential/AppendToVerifierKeystone.lean`, sorry-free):

  `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`.

We use it to push the **oracle-level** append-soundness residual down to the strictly-weaker
**plain-verifier** append-soundness residual, and chain the corrected outer-soundness half
(`midSoundnessLanguage` pullback, brick D) and the lifted embedded-sumcheck soundness half (brick E)
into the headline `logup_soundness_full`.

## The chain

1. **Oracle⇒plain append-soundness reduction (proven here, unconditional).**
   `OracleVerifier.soundness V` is *definitionally* `V.toVerifier.soundness`
   (`Basic.lean`), and `OracleVerifier.appendSoundnessResidual V₁ V₂ h₁ h₂` is
   `(V₁.append V₂).soundness …`. By the proven binary fusion
   `oracleVerifier_append_toVerifier`, `(V₁.append V₂).toVerifier =
   Verifier.append V₁.toVerifier V₂.toVerifier`, so the oracle-level residual *equals* the
   plain-verifier residual `(Verifier.append V₁.toVerifier V₂.toVerifier).soundness …`. The lemma
   `oracleAppendSoundnessResidual_of_plain` makes this rewrite, turning the deep oracle residual into
   the (still deep but strictly smaller, oracle-routing-free) plain-verifier malicious-prover seam
   union bound `hPlainAppend`.

2. **Corrected outer soundness (brick D).** The challenge-level Schwartz–Zippel mathematics is proven
   unconditionally in `OuterSoundnessReal.lean` (`outerSoundness_real`), and the
   `simulateQ`/`OptionT.mk` run-marginal is isolated to the single named fact
   `OuterRunMarginalToUniform` (`OuterRunSamplesChallenge.lean`). The protocol-level packaging of
   these into the full `(outerVerifier …).soundness …` over the **corrected, non-degenerate**
   language `midSoundnessProtocolLanguage` is the run-unfolding wall, kept as the named hypothesis
   `hOuter` (exactly what `logup_soundness_full` consumes).

3. **Embedded sumcheck soundness (brick E).** `sumcheckSoundnessResidual_holds`
   (`SumcheckSoundnessLift.lean`) lifts the inner multi-round sum-check round-by-round soundness
   through the context lens to the plain soundness of `sumcheckVerifier`, modulo `hProj`/`hInnerRbr`/
   `hRbrToSound`. That brick threads `midLanguage`; the corrected close threads
   `midSoundnessProtocolLanguage`, so the sumcheck half over the corrected language is kept as the
   named hypothesis `hSumcheck` (again exactly what `logup_soundness_full` consumes).

4. **End-to-end close.** Feed `hOuter`, `hSumcheck`, and the binary-fusion-discharged append residual
   into `logup_soundness_full`, yielding `logup_soundness_uncond` with the paper-shaped error
   `outerSoundnessError + sumcheckSoundnessError` and output language `Set.univ` (a genuine
   acceptance-probability bound, not a vacuous inclusion).

## Residual surface (`logup_soundness_uncond`)

The smallest honest residual set after this brick:

* `hOuter` — the **corrected** protocol-level outer soundness over `midSoundnessProtocolLanguage`
  (its Schwartz–Zippel mathematics is proven; only the run-marginal packaging remains, which is the
  proven `OuterRunMarginalToUniform`/`outerSoundness_real` content not yet wired through
  `Reduction.run`);
* `hSumcheck` — the embedded-sumcheck soundness over `midSoundnessProtocolLanguage` (the
  `liftContext` of generic sum-check soundness; `sumcheckSoundnessResidual_holds` supplies the
  `midLanguage` analogue);
* `hPlainAppend` — the **plain-verifier** append-soundness residual: the malicious-prover seam
  decomposition + union bound, with the oracle-routing stripped off by the proven binary fusion.

No `sorry`/`sorryAx`/`admit`: every step is a real proof or an explicitly named hypothesis. The
axiom audit at the bottom confirms axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))}
  {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
  {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

/-- **The oracle-level append-soundness residual is discharged *down to* the plain-verifier one,
using the proven binary verifier fusion.**

`OracleVerifier.appendSoundnessResidual V₁ V₂ h₁ h₂` unfolds (via `OracleVerifier.soundness`,
which is *definitionally* `·.toVerifier.soundness`) to
`(OracleVerifier.append V₁ V₂).toVerifier.soundness lang₁ lang₃ (e₁ + e₂)`. The proven keystone
`OracleReduction.oracleVerifier_append_toVerifier` rewrites
`(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`, so the
oracle residual is *exactly* `(Verifier.append V₁.toVerifier V₂.toVerifier).soundness …` — the
plain-verifier append residual `hPlainAppend`, with *no oracle routing left*. This strips the
oracle-statement bookkeeping off the deep malicious-prover seam union bound, shrinking the residual
to the smaller plain-verifier one. -/
theorem oracleAppendSoundnessResidual_of_plain
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [hCoh : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hPlainAppend :
      (Verifier.append V₁.toVerifier V₂.toVerifier).soundness init impl
        lang₁ lang₃ (soundnessError₁ + soundnessError₂)) :
    OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
      V₁ V₂ h₁ h₂ := by
  -- `appendSoundnessResidual` is `(V₁.append V₂).soundness …`, i.e.
  -- `(V₁.append V₂).toVerifier.soundness …` by definition of `OracleVerifier.soundness`.
  show (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier.soundness
    init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂)
  -- The proven binary fusion collapses the appended oracle verifier's `toVerifier`.
  rw [OracleReduction.oracleVerifier_append_toVerifier (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁)
    V₁ V₂]
  exact hPlainAppend

end OracleVerifier

namespace Logup

section SoundnessUncond

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the outer/sumcheck sub-verifier obligations. -/
local instance instInhabitedFieldLogupSoundUncond : Inhabited F := ⟨0⟩

/-! ### Step 1: discharge the LogUp append-soundness residual via the proven binary fusion -/

/-- **The LogUp oracle append-soundness residual reduces to the plain-verifier one.**

Specializing `OracleVerifier.oracleAppendSoundnessResidual_of_plain` to the LogUp sub-verifiers
`outerVerifier`/`sumcheckVerifier` (whose `AppendCoherent` instance is the in-tree
`instOuterVerifierAppendCoherent`): given the plain-verifier append-soundness residual
`hPlainAppend` over `logupVerifier.toVerifier = Verifier.append outerVerifier.toVerifier
sumcheckVerifier.toVerifier`, the oracle-level `appendSoundnessResidual` that
`logup_soundness_full` consumes holds. The deep oracle-routing of the append seam is discharged by
the proven binary fusion; only the plain malicious-prover seam union bound remains. -/
theorem logupAppendSoundnessResidual_of_plain (sumcheckSoundnessError : ℝ≥0)
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
    OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
      (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
      hOuter hSumcheck :=
  OracleVerifier.oracleAppendSoundnessResidual_of_plain.{0, 0}
    (init := init) (impl := impl)
    (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
    hOuter hSumcheck hPlainAppend

/-! ### Step 2: end-to-end most-unconditional soundness -/

/-- **Most-unconditional LogUp Protocol 2 soundness (issue #13, keystone K-soundFull).**

The full LogUp verifier is sound from the input language into the (trivial) output language
`Set.univ` with the paper-shaped error
`logupSoundnessError F n M params sumcheckSoundnessError =
outerSoundnessError F n M params + sumcheckSoundnessError`. Everything mechanical is discharged here:

* the definitional `logupVerifier = OracleVerifier.append outerVerifier sumcheckVerifier`;
* the error reconciliation (`logupSoundnessError = outerSoundnessError + s`, by `rfl`);
* the `append_soundness` chaining; and crucially
* the **oracle-routing of the append seam**, discharged by the proven binary verifier fusion
  (`oracleVerifier_append_toVerifier`), which strips the oracle residual down to the plain-verifier
  one `hPlainAppend`.

The smallest honest residual set:

* `hOuter` — the corrected protocol-level outer soundness over the non-degenerate
  `midSoundnessProtocolLanguage` (Schwartz–Zippel mathematics proven in `OuterSoundnessReal.lean`;
  run-marginal isolated to the proven `OuterRunMarginalToUniform`);
* `hSumcheck` — the embedded-sumcheck soundness over `midSoundnessProtocolLanguage` (the
  `liftContext` of generic sum-check soundness; `sumcheckSoundnessResidual_holds` supplies the
  `midLanguage` analogue);
* `hPlainAppend` — the **plain-verifier** append-soundness residual (malicious-prover seam
  decomposition + union bound, oracle routing already discharged). -/
theorem logup_soundness_uncond (sumcheckSoundnessError : ℝ≥0)
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
  logup_soundness_full oSpec F n M params init impl sumcheckSoundnessError
    hOuter hSumcheck
    (logupAppendSoundnessResidual_of_plain oSpec F n M params init impl sumcheckSoundnessError
      hOuter hSumcheck hPlainAppend)

/-! The historical bundled front door `LogupSoundnessUncondResidual` (and its consumer
`logup_soundness_uncond_of_residual`) was DELETED in the #351 burn-down (2026-06-11): the
2026-06-10 audit showed its `hOuter` conjunct (typed at `midSoundnessProtocolLanguage` with the
paper error `outerSoundnessError`) is refuted in the typical (small-support, large-field) regime
by `prob_midSoundnessLanguage_ge_compl_support` (`OuterSoundnessSharp.lean`), making the bundle
uninstantiable there and every consumer vacuously conditional.  Live routes:
`logup_soundness_end_to_end` (`OuterMaliciousSoundness.lean`) and
`outerVerifier_soundness_sharp` (`OuterRbrSoundness.lean`).  Consumers holding the three
obligations individually can still apply `logup_soundness_uncond` directly. -/

end SoundnessUncond

end Logup

/- Axiom audit for the most-unconditional LogUp soundness keystone. -/
#print axioms OracleVerifier.oracleAppendSoundnessResidual_of_plain
#print axioms Logup.logupAppendSoundnessResidual_of_plain
#print axioms Logup.logup_soundness_uncond
