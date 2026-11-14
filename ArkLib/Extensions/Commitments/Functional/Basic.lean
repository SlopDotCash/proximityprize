/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Commitments.Functional.Basic

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Tobias Rothmann
-/

import VCVio
import ArkLib.Compatibility.DiscreteProbability
import ArkLib.Extensions.OracleReduction.Security.Basic
import ArkLib.Data.Fin.Fold

/-!
# Commitment games with a separate setup interpreter

The canonical binding games thread the state left by setup, and canonical extractability
also logs the commitment phase and continues from its final state. The downstream binding
games below allow key generation to use a separate interpreter, for example to sample
private setup randomness without recording it in the shared query cache. The downstream
extractability variant also gives both public keys to the claim, opening prover, and extractor.
-/

namespace Commitment

open OracleSpec OracleComp SubSpec ProtocolSpec

variable {ι : Type} (oSpec : OracleSpec ι) (Data Commitment Decommitment ComKey VerifKey : Type)

variable [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n)

section Security

noncomputable section

open scoped NNReal ENNReal

variable [DecidableEq ι]
  {oSpec : OracleSpec ι} {Data : Type} [O : OracleInterface Data]
  {Commitment Decommitment ComKey VerifKey : Type} {n : ℕ}
  {pSpec : ProtocolSpec n}
  [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)

/-- The evaluation-binding game in the **setup-state-threaded** model: key generation is
interpreted by `setupImpl`, and the oracle state it leaves behind is the starting state of the
adversary/opening phase (interpreted by `impl`). Using the same interpreter for both phases recovers `Commitment.bindingGame`. -/
abbrev threadedBindingGame (setupImpl : QueryImpl oSpec (StateT σ ProbComp)) (AuxState : Type)
    (adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey) :
    OptionT ProbComp ((query : O.Query) × O.Response query × O.Response query × Bool × Bool) :=
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec))
  OptionT.mk do
    let s ← init
    let ⟨⟨ck, vk⟩, s'⟩ ← (simulateQ setupImpl scheme.keygen).run s
    (simulateQ pImpl <| (show OracleComp _ _ from do
      let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim ck) _
      let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
      let accept₁ := (← (reduction.verdict
        (cm, (⟨query, resp₁⟩ : (q : O.Query) × O.Response q)) st₁).run).getD false
      let accept₂ := (← (reduction.verdict
        (cm, (⟨query, resp₂⟩ : (q : O.Query) × O.Response q)) st₂).run).getD false
      pure (some ((⟨query, resp₁, resp₂, accept₁, accept₂⟩ :
        (query : O.Query) × O.Response query × O.Response query × Bool × Bool)))
    )).run' s'

/-- Evaluation binding in the setup-state-threaded model (see `threadedBindingGame`). -/
def threadedBinding (setupImpl : QueryImpl oSpec (StateT σ ProbComp))
    (bindingError : ℝ≥0) : Prop :=
  ∀ AuxState : Type,
  ∀ adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey,
    Pr{let result ← threadedBindingGame init impl scheme setupImpl AuxState adversary}[
      bindingCondition (Data := Data) result] ≤ bindingError

omit [DecidableEq ι] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- A common interpreter for setup and opening gives the canonical binding game. -/
theorem threadedBindingGame_eq_bindingGame
    [∀ t, Fintype (oSpec.Range t)] [∀ t, Inhabited ([pSpec.Challenge]ₒ.Range t)]
    [∀ t, Fintype ([pSpec.Challenge]ₒ.Range t)]
    (AuxState : Type)
    (adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey) :
    threadedBindingGame init impl scheme impl AuxState adversary =
      bindingGame init impl scheme AuxState adversary := rfl

/-- The function-binding game with a separate interpreter for setup. -/
abbrev threadedFunctionBindingGame {L : ℕ} (hn : n = 1)
    (setupImpl : QueryImpl oSpec (StateT σ ProbComp)) (AuxState : Type)
    [∀ i, VCVCompatible ((hn ▸ pSpec).Challenge i)]
    [∀ i, SampleableType ((hn ▸ pSpec).Challenge i)]
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey (hn ▸ pSpec))
    (adversary :
      FunctionBindingAdversary oSpec Data Commitment AuxState L (hn ▸ pSpec) ComKey) :
    OptionT ProbComp ((queryOf : Fin L → O.Query) ×
      ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)) :=
  let pImpl : QueryImpl (oSpec + [(hn ▸ pSpec).Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl (challengeQueryImpl (pSpec := hn ▸ pSpec))
  OptionT.mk do
    let s ← init
    let ⟨⟨ck, vk⟩, s'⟩ ← (simulateQ setupImpl scheme.keygen).run s
    (simulateQ pImpl <| (show OracleComp _ _ from do
      let ⟨cm, queryOf, responseOf, stateOf⟩ ← liftComp (adversary.claim ck) _
      let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
      let (accepts : Option (Fin L → Bool)) ← reduction.allVerdicts
        (fun i ↦
          (cm, (⟨queryOf i, responseOf i⟩ : (q : O.Query) × O.Response q)))
        stateOf
      pure (accepts.map fun accepts ↦ (⟨queryOf, responseOf, accepts⟩ :
        (queryOf : Fin L → O.Query) ×
          ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)))
    )).run' s'

/-- Function binding in the setup-state-threaded model (see `threadedFunctionBindingGame`). -/
def threadedFunctionBinding {L : ℕ} (hn : n = 1)
    (setupImpl : QueryImpl oSpec (StateT σ ProbComp))
    [∀ i, VCVCompatible ((hn ▸ pSpec).Challenge i)]
    [∀ i, SampleableType ((hn ▸ pSpec).Challenge i)]
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey (hn ▸ pSpec))
    (functionBindingError : ℝ≥0) : Prop :=
  ∀ AuxState : Type,
  ∀ adversary : FunctionBindingAdversary oSpec Data Commitment AuxState L (hn ▸ pSpec) ComKey,
    Pr{let result ← threadedFunctionBindingGame init impl hn setupImpl AuxState scheme
        adversary}[functionBindingCondition (Data := Data) result] ≤ functionBindingError

/-- The winning condition of the public-setup extractability game: the opening is accepted, yet the
extracted data answers the query differently from the claimed response. -/
abbrev extractabilityCondition :
    ((query : O.Query) × O.Response query × O.Response query × Bool) → Prop :=
  fun ⟨_, claimedResponse, extractedResponse, accepted⟩ ↦
    accepted ∧ extractedResponse ≠ claimedResponse

/-- A **public-setup straightline extractor** receives the public keys, the commitment, and the
log of the adversary's oracle queries made while producing its claim. -/
abbrev PublicSetupStraightlineExtractor (oSpec : OracleSpec ι)
    (Data Commitment ComKey VerifKey : Type) :=
  ComKey → VerifKey → Commitment → QueryLog oSpec → Data

/-- A **public-setup extractability adversary**: both its claim phase and its malicious opening
prover receive the public setup keys `(ck, vk)`. -/
structure PublicSetupExtractabilityAdversary (oSpec : OracleSpec ι)
    (Data Commitment AuxState : Type) [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n)
    (ComKey VerifKey : Type) where
  claim : ComKey → VerifKey →
    OracleComp oSpec (Commitment × (q : O.Query) × O.Response q × AuxState)
  prover : ComKey → VerifKey →
    Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec

/-- The **public-setup** extractability game: setup queries are interpreted by `setupImpl` and
the post-setup state is threaded into the security phase; the adversary, its prover, and the
extractor all receive the public keys. -/
abbrev publicSetupExtractabilityGame (setupImpl : QueryImpl oSpec (StateT σ ProbComp))
    (AuxState : Type)
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (extractor : PublicSetupStraightlineExtractor oSpec Data Commitment ComKey VerifKey)
    (adversary : PublicSetupExtractabilityAdversary oSpec Data Commitment AuxState pSpec
      ComKey VerifKey) :
    OptionT ProbComp ((query : O.Query) × O.Response query × O.Response query × Bool) :=
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec))
  OptionT.mk do
    let s ← init
    let ⟨⟨ck, vk⟩, s'⟩ ← (simulateQ setupImpl scheme.keygen).run s
    let ((⟨cm, query, claimedResponse, proverState⟩, queryLog), sAfterCommit) ←
      ((simulateQ impl.withLogging (adversary.claim ck vk)).run).run s'
    (simulateQ pImpl <| (show OracleComp _ _ from do
      let extractedData := extractor ck vk cm queryLog
      let stmt : Commitment × (q : O.Query) × O.Response q :=
        (cm, ⟨query, claimedResponse⟩)
      let reduction := Reduction.mk (adversary.prover ck vk) (scheme.opening (ck, vk)).verifier
      let accepted := (← (reduction.verdict stmt proverState).run).getD false
      pure (some (⟨query, claimedResponse, O.answer extractedData query, accepted⟩ :
        (query : O.Query) × O.Response query × O.Response query × Bool))
    )).run' sAfterCommit

/-- **Public-setup extractability** with error `extractabilityError`: there is a public-setup
straightline extractor such that every key-aware adversary/prover wins
`publicSetupExtractabilityGame` with probability at most `extractabilityError`. -/
def publicSetupExtractability (setupImpl : QueryImpl oSpec (StateT σ ProbComp))
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (extractabilityError : ℝ≥0) : Prop :=
  ∃ extractor : PublicSetupStraightlineExtractor oSpec Data Commitment ComKey VerifKey,
  ∀ AuxState : Type,
  ∀ adversary : PublicSetupExtractabilityAdversary oSpec Data Commitment AuxState pSpec
      ComKey VerifKey,
    probEvent (extractabilityCondition (Data := Data))
      (publicSetupExtractabilityGame init impl setupImpl AuxState scheme extractor adversary) ≤
      extractabilityError

end

end Security

end Commitment
