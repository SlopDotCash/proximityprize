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

abbrev extractabilityCondition :
    ((query : O.Query) × O.Response query × O.Response query × Bool) → Prop :=
  fun ⟨_, claimedResponse, extractedResponse, accepted⟩ ↦
    accepted ∧ extractedResponse ≠ claimedResponse

abbrev extractabilityGame (AuxState : Type)
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

/-- The probability of breaking extractability for a specific extractor/adversary/prover triple. -/
def extractabilityExperiment (AuxState : Type)
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (extractor : StraightlineExtractor oSpec Data Commitment)
    (adversary : ExtractabilityAdversary oSpec Data Commitment AuxState)
    (prover : Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec) :
    ℝ≥0∞ :=
  probEvent (extractabilityCondition (Data := Data)) (extractabilityGame init impl AuxState scheme extractor adversary prover)

set_option linter.unusedVariables false

set_option linter.unusedVariables true

end

end Security

end Commitment
