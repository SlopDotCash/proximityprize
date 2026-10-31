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
import ProximityPrize.Compatibility.DiscreteProbability
import ProximityPrize.Extensions.OracleReduction.Security.Basic
import ArkLib.Data.Fin.Fold

/-!
  # Functional Commitment Schemes (with Oracle Openings)

  A commitment scheme, relative to an oracle `oSpec : OracleSpec ι`, and for a given
  function `oracle : Data → Query → Response` transforming underlying data `Data` into an
  oracle `Query → Response`, is a tuple of three operations:

  - KeyGen, which is a function `keygen : OracleComp oSpec (ComKey × VerifKey)` that samples keys
    for the committer and the verifier.
  - Commit, which is a function `commit : Data → OracleComp oSpec (Commitment × Decommitment)`.
    The `Decommitment` value captures any auxiliary information (e.g. blinding randomness) produced
    during the commit phase that is needed to open the commitment later.
  - Open, which is (roughly) an interactive proof (relative to `oSpec`) for the following relation:
    - `StmtIn := (cm : Commitment) × (x : Query) × (y : Response)`
    - `WitIn := Data × Decommitment`
    - `rel : StmtIn → WitIn → Prop :=
        fun ⟨cm, x, y⟩ ⟨d, dc⟩ ↦ commit d ⇝ (cm, dc) ∧ oracle d x = y`

  For deterministic schemes (e.g. KZG), `Decommitment` is `Unit`.
  For randomized schemes (e.g. Pedersen, RO-based), `Decommitment` carries the blinding factor.

  There is one inaccuracy about the relation above: `commit` is an oracle computation, and not a
  deterministic function; hence the relation is not literally true as described. This is why
  security definitions for commitment schemes have to be stated differently than those for IOPs.

  ## References

  * [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z., *On the Fiat-Shamir Security of
      Succinct Arguments from Functional Commitments*][CGKY25]
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

/-! ### Setup models

The canonical games `Commitment.bindingGame` and `Commitment.functionBindingGame`
(`ArkLib.Commitments.Functional.Basic`) run key generation from a fresh state `s ← init` with
`(simulateQ impl scheme.keygen).run' s` and then run the adversary/opening phase with
`.run' s` again: the oracle state left behind by key generation is **discarded** and the
security phase restarts from the pre-setup state. They therefore model a *reset* shared oracle,
whereas `Commitment.correctness` runs setup, commitment, and opening in one pipeline. For a
stateful shared oracle (e.g. a lazily cached random oracle queried during setup) the two
models differ.

This file keeps the canonical (reset) games unchanged and adds explicitly named
**setup-state-threaded** variants (`threadedBindingGame`, `threadedFunctionBindingGame`,
`publicSetupExtractabilityGame`). These separate the two roles setup queries can play:

* `setupImpl` interprets the queries of `scheme.keygen`. It may interpret private setup
  randomness (e.g. a KZG trapdoor sampled through `unifSpec`) without recording it in the shared
  state, so that threading the state does not leak it to the adversary;
* `impl` interprets the queries of the adversary and the opening verifier;
* the post-setup state returned by `setupImpl` is passed to the security phase.

Choosing `setupImpl := impl` gives continuous shared-oracle execution. When `setupImpl` never
changes the state, the threaded games coincide with the canonical reset games
(`threadedBindingGame_eq_bindingGame_of_setup_preserves_state`). -/

/-- Setup key generation leaves the oracle state unchanged under `setupImpl`: every run from
state `s` returns state `s`. This is the condition under which the reset and threaded setup
models agree. -/
def SetupPreservesState
    (setupImpl : QueryImpl oSpec (StateT σ ProbComp))
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec) : Prop :=
  ∀ s : σ, (simulateQ setupImpl scheme.keygen).run s =
    (fun keys => (keys, s)) <$> (simulateQ setupImpl scheme.keygen).run' s

/-- The evaluation-binding game in the **setup-state-threaded** model: key generation is
interpreted by `setupImpl`, and the oracle state it leaves behind is the starting state of the
adversary/opening phase (interpreted by `impl`). Compare the canonical reset-model
`Commitment.bindingGame`. -/
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
/-- If key generation does not change the oracle state, the threaded binding game with
`setupImpl := impl` is the canonical reset-model `Commitment.bindingGame`. -/
theorem threadedBindingGame_eq_bindingGame_of_setup_preserves_state
    [∀ t, Fintype (oSpec.Range t)] [∀ t, Inhabited ([pSpec.Challenge]ₒ.Range t)]
    [∀ t, Fintype ([pSpec.Challenge]ₒ.Range t)]
    (h : SetupPreservesState impl scheme) (AuxState : Type)
    (adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey) :
    threadedBindingGame init impl scheme impl AuxState adversary =
      bindingGame init impl scheme AuxState adversary := by
  simp only [threadedBindingGame, bindingGame]
  congr 1
  refine bind_congr fun s => ?_
  rw [h s, bind_map_left]

/-- The function-binding game in the **setup-state-threaded** model; compare the canonical
reset-model `Commitment.functionBindingGame`. -/
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

/-! ### Extractability

The canonical `Commitment.extractability` is an inherited upstream **placeholder**: its body is
`False` under the quantifiers, so it is unsatisfiable whenever an adversary/prover exists and
must not be used as a security notion. Its `ExtractabilityAdversary` and `StraightlineExtractor`
also receive no setup keys.

This file provides two honest, separately named notions:

* `setupObliviousExtractability` (game `setupObliviousExtractabilityGame`): the adversary,
  malicious prover, and extractor are given **no** setup keys, and the canonical reset setup
  model is used. This is a *setup-oblivious* notion; it is strictly weaker than public-setup
  extractability for schemes such as KZG, since an attacker independent of `ck` cannot adapt its
  claim to the published key.
* `publicSetupExtractability` (game `publicSetupExtractabilityGame`): the adversary's claim
  phase, its malicious prover, and the extractor all receive the public keys `(ck, vk)`, and the
  post-setup oracle state is threaded (see *Setup models* above). This is the notion intended for
  public-setup schemes. -/

/-- The winning condition of the extractability games: the opening is accepted, yet the
extracted data answers the query differently from the claimed response. -/
abbrev extractabilityCondition :
    ((query : O.Query) × O.Response query × O.Response query × Bool) → Prop :=
  fun ⟨_, claimedResponse, extractedResponse, accepted⟩ ↦
    accepted ∧ extractedResponse ≠ claimedResponse

/-- The **setup-oblivious** extractability game (reset setup model): the adversary, its
malicious prover, and the extractor never see the setup keys. See
`publicSetupExtractabilityGame` for the public-setup notion. -/
abbrev setupObliviousExtractabilityGame (AuxState : Type)
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (extractor : StraightlineExtractor oSpec Data Commitment)
    (adversary : ExtractabilityAdversary oSpec Data Commitment AuxState)
    (prover : Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec) :
    OptionT ProbComp ((query : O.Query) × O.Response query × O.Response query × Bool) :=
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec))
  OptionT.mk do
    let s ← init
    let (ck, vk) ← (simulateQ impl scheme.keygen).run' s
    (simulateQ pImpl <| (show OracleComp _ _ from do
      let ⟨⟨cm, query, claimedResponse, proverState⟩, queryLog⟩ ←
        liftComp (WriterT.run (simulateQ loggingOracle adversary)) _
      let extractedData := extractor cm queryLog
      let stmt : Commitment × (q : O.Query) × O.Response q :=
        (cm, ⟨query, claimedResponse⟩)
      let reduction := Reduction.mk prover (scheme.opening (ck, vk)).verifier
      let accepted := (← (reduction.verdict stmt proverState).run).getD false
      pure (some (⟨query, claimedResponse, O.answer extractedData query, accepted⟩ :
        (query : O.Query) × O.Response query × O.Response query × Bool))
    )).run' s

/-- The probability of breaking setup-oblivious extractability for a specific
extractor/adversary/prover triple. -/
def setupObliviousExtractabilityExperiment (AuxState : Type)
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (extractor : StraightlineExtractor oSpec Data Commitment)
    (adversary : ExtractabilityAdversary oSpec Data Commitment AuxState)
    (prover : Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec) :
    ℝ≥0∞ :=
  probEvent (extractabilityCondition (Data := Data))
    (setupObliviousExtractabilityGame init impl AuxState scheme extractor adversary prover)

/-- **Setup-oblivious extractability** (an honest replacement for the canonical placeholder
`Commitment.extractability`, with the same key-free interfaces). -/
def setupObliviousExtractability
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (extractabilityError : ℝ≥0) : Prop :=
  ∃ extractor : StraightlineExtractor oSpec Data Commitment,
  ∀ AuxState : Type,
  ∀ adversary : ExtractabilityAdversary oSpec Data Commitment AuxState,
  ∀ prover : Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec,
    setupObliviousExtractabilityExperiment init impl AuxState scheme extractor adversary prover ≤
      extractabilityError

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
    (simulateQ pImpl <| (show OracleComp _ _ from do
      let ⟨⟨cm, query, claimedResponse, proverState⟩, queryLog⟩ ←
        liftComp (WriterT.run (simulateQ loggingOracle (adversary.claim ck vk))) _
      let extractedData := extractor ck vk cm queryLog
      let stmt : Commitment × (q : O.Query) × O.Response q :=
        (cm, ⟨query, claimedResponse⟩)
      let reduction := Reduction.mk (adversary.prover ck vk) (scheme.opening (ck, vk)).verifier
      let accepted := (← (reduction.verdict stmt proverState).run).getD false
      pure (some (⟨query, claimedResponse, O.answer extractedData query, accepted⟩ :
        (query : O.Query) × O.Response query × O.Response query × Bool))
    )).run' s'

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
