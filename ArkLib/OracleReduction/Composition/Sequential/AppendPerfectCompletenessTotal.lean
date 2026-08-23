/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracleChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges3

/-!
# Total (seam-agnostic) append perfect completeness

The three proven binary append perfect-completeness keystones cover *every* possible seam:
the trailing protocol is empty (`append_perfectCompleteness_empty_proof`), or its first round
is a `P_to_V` message (`append_perfectCompleteness_msg_proof`), or a `V_to_P` challenge
(`append_perfectCompleteness_challenge`). This module packages the case split into a single
seam-agnostic theorem and uses it to **discharge** the general
`reductionAppendPerfectCompletenessResidual` (and its oracle twin
`appendPerfectCompletenessResidual`) from `Append.lean` — previously named residuals because no
single keystone covered an arbitrary seam.

Side conditions are the union of the keystones': `hInit`/`hImplSupp` (msg + empty legs) and
`himplSP`/`himplNF` (challenge leg); all are vacuous for `oSpec = []ₒ` consumers.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Seam-agnostic append perfect completeness.** From perfectly-complete components, the
appended reduction is perfectly complete, for *any* trailing protocol: total case split over
the trailing protocol being empty / message-leading / challenge-leading, each case the
corresponding proven keystone. -/
theorem append_perfectCompleteness_total
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact append_perfectCompleteness_empty_proof R₁ R₂ h₁ h₂ hInit hImplSupp
  · have hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n))
        = pSpec₂.dir (⟨0, hn⟩ : Fin n) := by
      rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, hn⟩ from by ext; simp,
        Prover.append_dir_natAdd]
    cases hd : pSpec₂.dir (⟨0, hn⟩ : Fin n) with
    | V_to_P =>
      exact append_perfectCompleteness_challenge R₁ R₂ h₁ h₂ hn (hDir.trans hd) hd
        himplSP himplNF hInit
    | P_to_V =>
      exact append_perfectCompleteness_msg_proof R₁ R₂ h₁ h₂ hn (hDir.trans hd) hd
        hInit hImplSupp

/-- **`reductionAppendPerfectCompletenessResidual` is DISCHARGED** (seam-agnostic). -/
theorem reductionAppendPerfectCompletenessResidual_holds
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    reductionAppendPerfectCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_perfectCompleteness_total R₁ R₂ h₁ h₂ hInit hImplSupp himplSP himplNF

end Reduction

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
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
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Seam-agnostic oracle append perfect completeness**, and the discharge of the general
`appendPerfectCompletenessResidual`: total case split over the trailing protocol being
empty / message-leading / challenge-leading. -/
theorem append_perfectCompleteness_total
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact append_perfectCompleteness_empty R₁ R₂ h₁ h₂ hInit hImplSupp
  · have hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n))
        = pSpec₂.dir (⟨0, hn⟩ : Fin n) := by
      rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, hn⟩ from by ext; simp,
        Prover.append_dir_natAdd]
    cases hd : pSpec₂.dir (⟨0, hn⟩ : Fin n) with
    | V_to_P =>
      exact append_perfectCompleteness_challenge R₁ R₂ h₁ h₂ hn (hDir.trans hd) hd
        himplSP himplNF hInit
    | P_to_V =>
      exact append_perfectCompleteness_msg_proof R₁ R₂ h₁ h₂ hn (hDir.trans hd) hd
        hInit hImplSupp (appendToReductionResidual_proof R₁ R₂)

/-- **`appendPerfectCompletenessResidual` is DISCHARGED** (seam-agnostic, oracle level). -/
theorem appendPerfectCompletenessResidual_holds
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    appendPerfectCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_perfectCompleteness_total R₁ R₂ h₁ h₂ hInit hImplSupp himplSP himplNF

end OracleReduction

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Reduction.append_perfectCompleteness_total
#print axioms Reduction.reductionAppendPerfectCompletenessResidual_holds
#print axioms OracleReduction.append_perfectCompleteness_total
#print axioms OracleReduction.appendPerfectCompletenessResidual_holds

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Seam-agnostic append completeness with additive error, for a nonempty trailing protocol.**
The error-ful analogue of `append_perfectCompleteness_total` over the message/challenge split
(`append_completeness_msg` from `AppendSeamBridges3`, `append_completeness_challenge` from
`AppendPerfectCompletenessChallenge`). The `n = 0` (empty trailing) error-ful case is NOT yet
covered: the perfect empty keystone's support-based proof does not generalize, and the empty
game-factoring for the union-bound engine has not been built — hence the `0 < n` hypothesis
(every concrete ArkLib consumer to date has a nonempty trailing protocol). -/
theorem append_completeness_total_pos
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
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n))
      = pSpec₂.dir (⟨0, hn⟩ : Fin n) := by
    rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, hn⟩ from by ext; simp,
      Prover.append_dir_natAdd]
  cases hd : pSpec₂.dir (⟨0, hn⟩ : Fin n) with
  | V_to_P =>
    exact append_completeness_challenge R₁ R₂ h₁ h₂ hn (hDir.trans hd) hd
      himplSP himplNF himplVB hInit
  | P_to_V =>
    exact append_completeness_msg R₁ R₂ h₁ h₂ hn (hDir.trans hd) hd
      hInit.probFailure_eq_zero himplSP himplNF himplVB

end Reduction

-- Axiom audit (error-ful positive-seam total): only [propext, Classical.choice, Quot.sound].
#print axioms Reduction.append_completeness_total_pos
