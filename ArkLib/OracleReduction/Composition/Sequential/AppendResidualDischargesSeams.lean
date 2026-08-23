/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDetEmpty
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessTotal

/-!
# Seam-variant discharges of `Verifier.appendRbrKnowledgeSoundnessResidual` (issue #340)

`AppendResidualDischarges.lean` wires the **message-seam** rbr-knowledge-soundness keystone
into the named residual of `Append.lean`. This file completes the wiring for the remaining
proven keystone variants — the residual's conclusion is in each case *definitionally* the
keystone's, so every discharge is a direct application:

* `appendRbrKnowledgeSoundnessResidual_challenge_subsingleton` — **challenge seam**
  (`V_to_P` at the boundary), deterministic `V₁`, `Subsingleton σ`
  (`append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`);
* `appendRbrKnowledgeSoundnessResidual_failingDet_subsingleton` — **failing-deterministic**
  `V₁` (verdict `Option`-valued: `OptionT.mk (pure (verify? s tr))`), message seam,
  `Subsingleton σ` (`append_rbrKnowledgeSoundness_failingDet_subsingleton`);
* `appendRbrKnowledgeSoundnessResidual_failingDet_empty` — failing-deterministic `V₁`,
  **empty trailing phase** (`pSpec₂ = !p[]`-shaped, no direction facts needed, arbitrary `σ`)
  (`append_rbrKnowledgeSoundness_failingDet_empty`).

Together with the message-seam discharge, every proven keystone regime now discharges the
named residual directly; the residual remains *statement-gapped by design* (its docstring),
so these conditional forms are the honest endpoints. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

section ChallengeSeam

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Challenge-seam discharge of `appendRbrKnowledgeSoundnessResidual`** (deterministic `V₁`,
`Subsingleton σ`, the right block opening with a `V_to_P` challenge round). Direct from the
keystone. -/
theorem appendRbrKnowledgeSoundnessResidual_challenge_subsingleton [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
    appendRbrKnowledgeSoundnessResidual V₁ V₂ h₁ h₂ :=
  append_rbrKnowledgeSoundness_keystone_subsingleton_challenge V₁ V₂ verify hVerify
    hInit hInitNF hNE₂ hNEW₂ hn hDir hDir₂ h₁ h₂

end ChallengeSeam

section FailingDet

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Wit₂ : Type} {m : ℕ} {pSpec₁ : ProtocolSpec m}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Failing-deterministic message-seam discharge of `appendRbrKnowledgeSoundnessResidual`**
(`Subsingleton σ`): for a left verifier of the failing-deterministic shape
`⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩`, the named residual holds. Direct from
`append_rbrKnowledgeSoundness_failingDet_subsingleton`. -/
theorem appendRbrKnowledgeSoundnessResidual_failingDet_subsingleton
    [Subsingleton σ] [Inhabited Stmt₂]
    {Stmt₃ Wit₁ Wit₃ : Type} {n : ℕ} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0} {err₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ err₂) :
    appendRbrKnowledgeSoundnessResidual
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
      V₂ h₁ h₂ :=
  append_rbrKnowledgeSoundness_failingDet_subsingleton verify? V₂ hInit hInitNF hNEW₂
    hn hDir hDir₂ h₁ h₂

/-- **Failing-deterministic empty-trailing-seam discharge of
`appendRbrKnowledgeSoundnessResidual`** (arbitrary `σ`, no direction facts — the right block
has no rounds). Direct from `append_rbrKnowledgeSoundness_failingDet_empty`. -/
theorem appendRbrKnowledgeSoundnessResidual_failingDet_empty
    [Inhabited Stmt₂]
    {Stmt₃ Wit₁ Wit₃ : Type} {pSpec₂ : ProtocolSpec 0}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0} {err₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂)
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ err₂) :
    appendRbrKnowledgeSoundnessResidual
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
      V₂ h₁ h₂ :=
  append_rbrKnowledgeSoundness_failingDet_empty verify? V₂ hInit hNEW₂ h₁ h₂

end FailingDet

end Verifier

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Error-ful discharge of `reductionAppendCompletenessResidual`** (the statement-match
verification of issue #340): `append_completeness_total_pos` concludes exactly the residual's
body, so the named residual holds — seam-agnostically — for every nonempty trailing protocol,
under the standard honest-implementation side conditions. (The `n = 0` error-ful case stays
honestly open per that theorem's docstring; the perfect-completeness `n = 0` case is covered
by the existing `AppendPerfectCompletenessTotal` discharges.) -/
theorem reductionAppendCompletenessResidual_total_pos
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    reductionAppendCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_completeness_total_pos R₁ R₂ h₁ h₂ hn hInit himplSP himplNF himplVB

end Reduction

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.appendRbrKnowledgeSoundnessResidual_challenge_subsingleton
#print axioms Verifier.appendRbrKnowledgeSoundnessResidual_failingDet_subsingleton
#print axioms Verifier.appendRbrKnowledgeSoundnessResidual_failingDet_empty
#print axioms Reduction.reductionAppendCompletenessResidual_total_pos
