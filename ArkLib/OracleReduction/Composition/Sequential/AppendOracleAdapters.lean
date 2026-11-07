/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessMsgProof

/-!
# Oracle-level adapters for sequential append

Verifier conversion, perfect completeness, and soundness transport for appended
oracle reductions, preserving the assumptions of each underlying theorem.
-/

-- These historical events observe all subsets of the complete optional transcript output.
private local instance (A : Type) : MeasurableSpace A := ⊤
private local instance (A B : Type) : MeasurableSpace (A × B) := ⊤
private local instance (A : Type) : MeasurableSpace (Option A) := ⊤
private local instance (A : Type) : @DiscreteMeasurableSpace A ⊤ := ⟨fun _ => True.intro⟩

section

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/


/-!
# The `toVerifier`/`append` keystone for oracle reductions

This file discharges the last generic obstruction of the sequential-composition append
perfect-completeness keystone (shared by issues #29, #114, #62, #13): the verifier-fusion equation

  `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`.

The proof (`oracleVerifier_append_toVerifier`) delegates the canonical fusion theorem. Its output
materialization covers both embedded and virtual output oracles, so the compiled verifier agrees
with the two-stage composition without imposing an embedding-only routing premise.

Consequently `appendToReductionResidual` is discharged for every pair of oracle reductions
(`appendToReductionResidual_proof`), which unblocks `append_perfectCompleteness_msg_proof` to give
unconditional message-seam append perfect completeness.
-/

open OracleComp OracleSpec ProtocolSpec OracleInterface QueryImpl

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

/-- Canonical output materialization composes for both embedded and virtual oracles. -/
theorem materializeOutput_append
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (oStmt : ∀ i, OStmt₁ i) (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : ιₛ₃) :
    (OracleVerifier.append V₁ V₂).materializeOutput tr.challenges oStmt tr.messages i =
      V₂.materializeOutput tr.snd.challenges
        (V₁.materializeOutput tr.fst.challenges oStmt tr.fst.messages) tr.snd.messages i := rfl

theorem oracleVerifier_append_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
    (OracleVerifier.append (Oₛ₁:=Oₛ₁) (Oₛ₂:=Oₛ₂) (Oₘ₁:=Oₘ₁) V₁ V₂).toVerifier
      = Verifier.append V₁.toVerifier V₂.toVerifier :=
  OracleVerifier.append_toVerifier V₁ V₂
/-- **The append-to-reduction residual is discharged for every pair of oracle reductions.** This is
the single named bridge consumed by `OracleReduction.append_perfectCompleteness_msg_proof`; with it
proven, that keystone gives unconditional message-seam append perfect completeness. -/
theorem appendToReductionResidual_proof
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
    appendToReductionResidual (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁ R₂ :=
  (appendToReductionResidual_iff_verifier R₁ R₂).mpr
    (oracleVerifier_append_toVerifier R₁.verifier R₂.verifier)

variable [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level append perfect completeness — UNCONDITIONAL (message seam).** Perfect
completeness of `R₁.append R₂` from the two component perfect-completenesses and the message-seam
direction/`NeverFail`/support facts, with the residual bridge now discharged internally
(`appendToReductionResidual_proof`). This is the keystone consumers (#29/#114/#62/#13) need:
no `appendToReductionResidual`/`hBridge` hypothesis remains. -/
theorem append_perfectCompleteness_keystone
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    [∀ q, Fintype ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Inhabited ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₁.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₁.Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  append_perfectCompleteness_msg_proof R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp
    (appendToReductionResidual_proof R₁ R₂)

end OracleReduction

end

section

/-!
# Oracle-level append perfect completeness at a challenge seam (#114)

The challenge-seam (`V_to_P` seam) analogue of `OracleReduction.append_perfectCompleteness_keystone`
(`AppendToVerifierKeystone.lean`, message seam): perfect completeness of `R₁.append R₂` for
**oracle** reductions whose seam round (`pSpec₂`'s round 0) is a verifier challenge.

The verifier-side content of the oracle-level lift — the `toVerifier`/`append` fusion
`appendToReductionResidual` — is *seam-agnostic*: `appendToReductionResidual_proof`
(`AppendToVerifierKeystone.lean`) discharges it for every pair of oracle reductions, with no
direction hypotheses. So the lift is a pure pass-through: collapse `(R₁.append R₂).toReduction` to
`R₁.toReduction.append R₂.toReduction` via the proven residual, then apply the `Reduction`-level
challenge-seam theorem `Reduction.append_perfectCompleteness_challenge`
(`AppendPerfectCompletenessChallenge.lean`).

Compared to the message-seam keystone, the side conditions differ exactly as the underlying
`Reduction`-level theorems do: the challenge seam needs the honest implementation to be
state-preserving and never-failing (`himplSP`/`himplNF`, both vacuous for `oSpec = []ₒ` and
satisfied by any read-only oracle implementation), instead of the message seam's
support-faithfulness, and it does not need the extra combined-spec `Fintype`/`Inhabited`
instances.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
    {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level append perfect completeness — UNCONDITIONAL (challenge seam).** Perfect
completeness of `R₁.append R₂` for oracle reductions whose seam round is a verifier challenge
(`V_to_P`), from the two component perfect-completenesses, the seam direction facts, and the
honest-implementation side conditions (state-preserving / never-failing `impl`, never-failing
`init`). The verifier-fusion residual is discharged internally by the seam-agnostic
`appendToReductionResidual_proof`; the probabilistic content is the `Reduction`-level
`Reduction.append_perfectCompleteness_challenge`. This is the challenge-seam companion of
`append_perfectCompleteness_keystone` that #114's composed (sum-check-leading) phases need. -/
theorem append_perfectCompleteness_challenge_keystone
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (hInit : NeverFail init) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_challenge R₁.toReduction R₂.toReduction
    h₁ h₂ hn hDir hDir₂ himplSP himplNF hInit

end OracleReduction

#print axioms OracleReduction.append_perfectCompleteness_challenge_keystone

end

section

/-!
# Oracle-level append perfect completeness at an empty trailing seam (#114)

The `pSpec₂ : ProtocolSpec 0` analogue of `OracleReduction.append_perfectCompleteness_keystone`
(message seam, `AppendToVerifierKeystone.lean`) and
`OracleReduction.append_perfectCompleteness_challenge_keystone` (challenge seam,
`AppendChallengeKeystoneOracle.lean`): perfect completeness of `R₁.append R₂` for **oracle**
reductions whose trailing protocol is empty (a zero-round adapter/check phase).

This is the third and final seam case the right-associated Spartan composed-PC fold (#114) needs:
its innermost append is `secondSumcheck ▷ finalCheck` where `finalCheck` is a `ProtocolSpec 0`
`CheckClaim` phase, so neither the message-seam nor the challenge-seam keystone applies (both
require `0 < n`). The verifier-fusion residual is seam-agnostic and already discharged
(`appendToReductionResidual_proof`); the probabilistic content is the unconditional
`Reduction.append_perfectCompleteness_empty_proof`. No seam-direction hypotheses are needed.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
    {m : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level append perfect completeness — UNCONDITIONAL (empty trailing seam).** Perfect
completeness of `R₁.append R₂` for oracle reductions with an empty trailing protocol
(`pSpec₂ : ProtocolSpec 0`), from the two component perfect-completenesses and the
`NeverFail`/support-faithfulness side conditions. No seam-direction hypotheses: the trailing block
has no rounds. The verifier-fusion residual is discharged internally by the seam-agnostic
`appendToReductionResidual_proof`; the probabilistic content is the `Reduction`-level
`Reduction.append_perfectCompleteness_empty_proof`. This is the empty-tail case of the #114
composed fold (`secondSumcheck ▷ finalCheck`). -/
theorem append_perfectCompleteness_empty_keystone
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    [∀ q, Fintype ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Inhabited ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₁.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₁.Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_empty_proof R₁.toReduction R₂.toReduction
    h₁ h₂ hInit hImplSupp

end OracleReduction

#print axioms OracleReduction.append_perfectCompleteness_empty_keystone

end

section

/-!
# Oracle-level append knowledge soundness: transport from the plain layer

`OracleVerifier.knowledgeSoundness` is *defined* as knowledge soundness of the underlying
`toVerifier`, and the proven verifier-fusion keystone
`OracleReduction.oracleVerifier_append_toVerifier` identifies the `toVerifier` of an appended
oracle verifier with the plain append of the `toVerifier`s.  Hence the oracle-level named residual
`OracleVerifier.appendKnowledgeSoundnessResidual` (Append.lean) is *equivalent* to its plain-layer
counterpart `Verifier.appendKnowledgeSoundnessResidual` on `V₁.toVerifier` / `V₂.toVerifier`.

This file records that transport (`append_knowledgeSoundness_of_toVerifier`,
`appendKnowledgeSoundnessResidual_of_plain`): any discharge of the plain straightline-KS append
residual transfers verbatim to the oracle layer.  No new probabilistic content — the entire load
is carried by the proven fusion equation.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι} {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level appended knowledge soundness from the plain layer.**  Knowledge soundness of an
appended oracle verifier *is* (definitionally + via the proven fusion
`oracleVerifier_append_toVerifier`) knowledge soundness of the plain append of the `toVerifier`s.
Any plain-layer append-KS theorem therefore transports to the oracle layer with no further work. -/
theorem append_knowledgeSoundness_of_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError : ℝ≥0}
    (hPlain : (Verifier.append V₁.toVerifier V₂.toVerifier).knowledgeSoundness
      init impl rel₁ rel₃ knowledgeError) :
    (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).knowledgeSoundness
      init impl rel₁ rel₃ knowledgeError := by
  unfold OracleVerifier.knowledgeSoundness
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact hPlain

/-- **The oracle-level append-KS named residual reduces to the plain-layer one.**  Discharges
`OracleVerifier.appendKnowledgeSoundnessResidual` from any discharge of
`Verifier.appendKnowledgeSoundnessResidual` on the `toVerifier`s (e.g. the message-seam /
deterministic-`V₁` discharge `Verifier.append_knowledgeSoundness_msg_residual`). -/
theorem appendKnowledgeSoundnessResidual_of_plain
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂)
    (hPlain : Verifier.appendKnowledgeSoundnessResidual (init := init) (impl := impl)
      (rel₁ := rel₁) (rel₂ := rel₂) (rel₃ := rel₃) V₁.toVerifier V₂.toVerifier h₁ h₂) :
    OracleVerifier.appendKnowledgeSoundnessResidual (init := init) (impl := impl)
      (rel₁ := rel₁) (rel₂ := rel₂) (rel₃ := rel₃) V₁ V₂ h₁ h₂ :=
  append_knowledgeSoundness_of_toVerifier V₁ V₂ hPlain

end OracleVerifier

-- Axiom audit: transport lemmas must be axiom-clean.
#print axioms OracleVerifier.append_knowledgeSoundness_of_toVerifier
#print axioms OracleVerifier.appendKnowledgeSoundnessResidual_of_plain

end

section

/-!
# Oracle-level challenge-seam and empty-seam append perfect completeness

The `V_to_P`-seam (challenge) and empty-seam (`n = 0`) analogues of
`OracleReduction.append_perfectCompleteness_msg_proof`. Identical structure: an `OracleReduction`'s
perfect completeness is the perfect completeness of its `toReduction`; the verifier-fusion bridge
`appendToReductionResidual_proof` (proven *unconditionally*) rewrites
`(R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction`; the underlying Reduction-level
result is `Reduction.append_perfectCompleteness_challenge` / `_empty_proof`. These give the
oracle-level seam keystones for the two remaining seam directions of the Spartan composed PIOP
(`composedPIOP_Rc`): challenge seams (`firstMessage▷…`, `sendEvalClaim▷…`) and empty seams
(`…▷finalCheck`, `…▷prependClaim`). The message seams use the existing
`append_perfectCompleteness_msg_proof`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
    {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level challenge-seam append perfect completeness.** The `V_to_P` analogue of
`append_perfectCompleteness_msg_proof`, with the verifier-fusion bridge supplied inline by the
unconditional `appendToReductionResidual_proof`. Reduces to
`Reduction.append_perfectCompleteness_challenge`. -/
theorem append_perfectCompleteness_challenge
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (hInit : NeverFail init)
    [∀ q, Fintype ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Inhabited ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₁.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₁.Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_challenge
    R₁.toReduction R₂.toReduction h₁ h₂ hn hDir hDir₂ himplSP himplNF hInit

/-- **Oracle-level empty-seam append perfect completeness.** The `n = 0` analogue: appending a
0-round oracle reduction `R₂` (empty trailing protocol) preserves perfect completeness. Reduces to
`Reduction.append_perfectCompleteness_empty_proof`. -/
theorem append_perfectCompleteness_empty
    {pSpecE : ProtocolSpec 0}
    [OₘE : ∀ i, OracleInterface (pSpecE.Message i)]
    [∀ i, SampleableType (pSpecE.Challenge i)]
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpecE)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    [∀ q, Fintype ((oSpec + [(pSpec₁ ++ₚ pSpecE).Challenge]ₒ).Range q)]
    [∀ q, Inhabited ((oSpec + [(pSpec₁ ++ₚ pSpecE).Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₁.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₁.Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpecE.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpecE.Challenge]ₒ).Range q)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_empty_proof
    R₁.toReduction R₂.toReduction h₁ h₂ hInit hImplSupp

end OracleReduction

end

section

/-!
# OracleVerifier-level plain-soundness append keystone, message seam (issues #62 / #13 / #114)

The generic `OracleVerifier` lift of the unconditional message-seam append-soundness keystone
`Verifier.append_soundness_msg` (`AppendSoundnessMsgProof.lean`), discharging the named residual
`OracleVerifier.appendSoundnessResidual` (`Append.lean`) with no oracle routing left.

LogUp already performs this exact combination ad-hoc
(`Logup.Security/LogupSoundnessUncond.lean`: `oracleAppendSoundnessResidual_of_plain` applied to
`Verifier.append_soundness_msg`); this file records the *generic* combinator so other consumers —
notably the eight `h_residual` call sites in `BatchedFri/Security.lean` /
`BatchedFri/QueryRoundSoundness.lean` and the FRI top seam (`Fri/Spec/Soundness.lean`) — can
discharge their append-soundness hypotheses without re-deriving the fusion plumbing.

The lift is definitional: `OracleVerifier.soundness` *is* `toVerifier`-level
(`Security/Basic.lean`), and the proven binary fusion
`OracleReduction.oracleVerifier_append_toVerifier` identifies the appended oracle verifier's
`toVerifier` with `Verifier.append V₁.toVerifier V₂.toVerifier`, to which the plain message-seam
keystone applies directly.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))}
    {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

/-- **OracleVerifier-level plain-soundness append keystone, message seam (unconditional).** The
appended oracle verifier is sound with the additive error `ε₁ + ε₂`, from the two components'
soundness alone, given the message-seam direction facts (`hn`/`hDir`/`hDir₂`) and the standard
honest-implementation side conditions (`himplSP`/`himplNF`/`himplVB` — state-preserving,
never-failing, value-blind; all vacuous for `oSpec = []ₒ`).

Proof: `OracleVerifier.soundness` is definitionally `toVerifier`-level; rewrite the appended
`toVerifier` via the proven binary fusion `oracleVerifier_append_toVerifier`, then apply the
unconditional plain message-seam keystone `Verifier.append_soundness_msg`. -/
theorem append_soundness_msg
    [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).soundness
        init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold OracleVerifier.soundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact Verifier.append_soundness_msg V₁.toVerifier V₂.toVerifier h₁ h₂ hn hDir hDir₂
    himplSP himplNF himplVB

/-- **Discharge of the named residual `OracleVerifier.appendSoundnessResidual`** (`Append.lean`)
for the message-first seam under the standard honest-implementation side conditions. The
residual's conclusion is precisely the keystone's, so this is definitional from
`append_soundness_msg`. With this, `OracleVerifier.append_soundness` no longer needs an unproved
hypothesis at a message seam — the regime of the BCS opening phase, LogUp Protocol 2, and the
Batched-FRI batching/fold seams. -/
theorem appendSoundnessResidual_msg
    [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    appendSoundnessResidual (init := init) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_soundness_msg V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleVerifier.append_soundness_msg
#print axioms OracleVerifier.appendSoundnessResidual_msg

end
