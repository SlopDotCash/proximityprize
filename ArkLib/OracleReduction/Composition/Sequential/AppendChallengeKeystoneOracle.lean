/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge

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
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (hInit : NeverFail init) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_challenge R₁.toReduction R₂.toReduction
    h₁ h₂ hn hDir hDir₂ himplSP himplNF hInit

end OracleReduction

#print axioms OracleReduction.append_perfectCompleteness_challenge_keystone
