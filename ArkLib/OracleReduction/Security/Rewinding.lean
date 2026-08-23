/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import VCVio.OracleComp.QueryTracking.CostModel

/-!
  # Rewinding Knowledge Soundness

  This file defines rewinding knowledge soundness for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Extractor

section Rewinding

/-! Rewinding extractor interface. -/

/-- The oracle interface to call the prover as a black box -/
def OracleSpec.proverOracle (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    OracleSpec ((i : pSpec.MessageIdx) × StmtIn × pSpec.Transcript i.val.castSucc) :=
  fun q => pSpec.Message q.1

structure Rewinding (oSpec : OracleSpec ι)
    (StmtIn StmtOut WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The state of the extractor -/
  ExtState : Type
  /-- Simulate challenge queries for the prover -/
  simChallenge : QueryImpl [pSpec.Challenge]ₒ (StateT ExtState (OracleComp [pSpec.Challenge]ₒ))
  /-- Simulate oracle queries for the prover -/
  simOracle : QueryImpl oSpec (StateT ExtState (OracleComp oSpec))
  /-- Run the extractor with the prover's oracle interface, allowing for calling the prover multiple
    times -/
  runExt : StmtOut → WitOut → StmtIn →
    StateT ExtState (OracleComp (OracleSpec.proverOracle StmtIn pSpec)) WitIn

-- Challenge: need environment to update & maintain the prover's states after each extractor query
-- This will hopefully go away after the refactor of prover's type to be an iterated monad

end Rewinding

end Extractor

namespace Prover

variable {Statement Message : Type}

/-- A malicious non-interactive prover in the argument model chooses both the input statement and
the proof, with oracle access to the ambient shared oracle. -/
abbrev NARG (oSpec : OracleSpec ι) (Statement Message : Type) :=
  OracleComp oSpec (Statement × Message)

/-- Paper-facing total `t`-query bound for a malicious NARG prover.

This is the structural `IsQueryBound` predicate with a single natural-number budget shared across
all oracle indices. It directly matches the `t`-query quantification used in CO25 Definition 3.8.
-/
abbrev NARG.queryBounded
    (prover : NARG oSpec Statement Message) (queryBound : ℕ) : Prop :=
  OracleComp.IsQueryBound prover queryBound (fun _ b => 0 < b) (fun _ b => b - 1)

/-- Stronger per-oracle-index query bound for a malicious NARG prover. This is not the primary
paper-facing notion for CO25 Definition 3.8, but it is often more convenient for later reductions.
-/
abbrev NARG.perIndexQueryBounded [DecidableEq ι]
    (prover : NARG oSpec Statement Message) (queryBound : (oracleIdx : ι) → ℕ) : Prop :=
  OracleComp.IsPerIndexQueryBound prover queryBound

/-- A family of malicious NARG provers indexed by the security parameter `λ : ℕ`. This is the
paper-facing wrapper that makes `λ` explicit without refactoring the fixed-parameter definitions.
-/
abbrev NARG.Family (oSpec : (secParam : ℕ) → OracleSpec ι)
    (Statement : (secParam : ℕ) → Type)
    (Message : (secParam : ℕ) → Type) :=
  ∀ secParam : ℕ, NARG (oSpec secParam) (Statement secParam) (Message secParam)

/-- Explicit `t(λ)`-query bound for a `λ`-indexed malicious NARG family. -/
abbrev NARG.Family.queryBounded
    {oSpec : ℕ → OracleSpec ι}
    {Statement Message : ℕ → Type}
    (prover : NARG.Family oSpec Statement Message)
    (queryBound : (secParam : ℕ) → ℕ) : Prop :=
  ∀ secParam, (prover secParam).queryBounded (queryBound secParam)

/-- Explicit per-oracle-index query bound for a `λ`-indexed malicious NARG family. -/
abbrev NARG.Family.perIndexQueryBounded [DecidableEq ι]
    {oSpec : ℕ → OracleSpec ι}
    {Statement Message : ℕ → Type}
    (prover : NARG.Family oSpec Statement Message)
    (queryBound : (secParam : ℕ) → (oracleIdx : ι) → ℕ) : Prop :=
  ∀ secParam, (prover secParam).perIndexQueryBounded (queryBound secParam)

end Prover

namespace Extractor

variable {Statement Witness Message : Type}

/-- A rewinding extractor for a non-interactive argument.

It receives the statement and proof from a target execution, the prover's and verifier's shared
oracle query logs for that execution, and black-box access to the malicious prover itself. The
extractor may then re-run the prover inside the ambient oracle computation, which is the ArkLib
counterpart of rewinding in CO25 Definition 3.8. -/
def RewindingNARG (oSpec : OracleSpec ι) (Statement Witness Message : Type) :=
  (stmt : Statement) →
  (proof : Message) →
  (proveQueryLog : QueryLog oSpec) → -- accepting transcript/query logs
  (verifyQueryLog : QueryLog oSpec) →
  (prover : Prover.NARG oSpec Statement Message) →
  OracleComp oSpec Witness -- Future work: should we make this OptionT to model extractor abort

/-- Uniform expected-cost bound for a rewinding extractor over its explicit ArkLib input
interface.

The paper states an expected running-time bound for the extractor. ArkLib models that through an
arbitrary additive oracle cost model and asks that every invocation of the extractor through its
public interface satisfy the same expected-cost bound.

This is to model the expected runtime of straightline/rewinding extractors in
Definition 3.6 & 3.8 of CO25
-/
def RewindingNARG.expectedCostBound
    [oSpec.Fintype] [oSpec.Inhabited]
    {ω : Type} [AddCommMonoid ω] -- `ω`: cost Type
    (extractor : RewindingNARG oSpec Statement Witness Message)
    (prover : Prover.NARG oSpec Statement Message)
    (costModel : CostModel oSpec ω)
    (val : ω → ℝ≥0∞) -- `val`: cost type value → evaluable cost
    (bound : ℝ≥0∞) : Prop :=
  ∀ stmt proof proveQueryLog verifyQueryLog,
    _root_.ExpectedCostBound (extractor stmt proof proveQueryLog verifyQueryLog prover)
      costModel val bound

end Extractor

namespace Verifier

section NonInteractive

variable {ι : Type} {oSpec : OracleSpec ι}
  [oSpec.Fintype] [oSpec.Inhabited]
  {Statement Witness Message : Type}

/-- CO25 Definition 3.7, adapted to ArkLib's non-interactive verifier interface.

The paper's size bound `|x| ≤ n` is represented here by an arbitrary set `admissible`, so the same
definition can be reused for statement-size bounds or any other well-formedness predicate on
instances. -/
def failureProbability
    (admissible : Set Statement)
    (verifier : NonInteractiveVerifier Message oSpec Statement Bool)
    (prover : OracleComp oSpec (Statement × Message))
    (failureError : ℝ≥0) : Prop :=
  Pr[ fun ⟨stmt, accepted⟩ => stmt ∉ admissible ∨ accepted ≠ some true
    | do
        let ⟨stmt, proof⟩ ← prover
        let transcript : FullTranscript ⟨!v[Direction.P_to_V], !v[Message]⟩ :=
          fun
          | ⟨0, _⟩ => proof
        let accepted ← (verifier.run stmt transcript).run
        return (stmt, accepted)
  ] ≤ failureError

/-- The extraction experiment for CO25 Definition 3.8 in ArkLib's non-interactive interface.

This runs the malicious prover once to obtain the target statement and proof, records the prover's
and verifier's shared-oracle query logs for that accepting attempt, and then invokes the rewinding
extractor with black-box access to the prover itself. -/
def rewindingKnowledgeSoundnessGame
    (verifier : NonInteractiveVerifier Message oSpec Statement Bool)
    (extractor : Extractor.RewindingNARG oSpec Statement Witness Message)
    (prover : Prover.NARG oSpec Statement Message) :
    OracleComp oSpec (Statement × Witness × Option Bool) := do
  let ⟨⟨stmt, proof⟩, proveQueryLog⟩ ← (simulateQ loggingOracle prover).run
  let transcript : FullTranscript ⟨!v[Direction.P_to_V], !v[Message]⟩ :=
    fun
    | ⟨0, _⟩ => proof
  let ⟨accepted, verifyQueryLog⟩ ←
    (simulateQ loggingOracle (verifier.run stmt transcript).run).run
  let wit ← extractor stmt proof proveQueryLog verifyQueryLog prover
  return (stmt, wit, accepted)

/-- CO25 Definition 3.8, adapted to ArkLib's non-interactive argument interface.

ArkLib's `Prover.NARG` type already models the paper's deterministic malicious provers: the only
source of variation is oracle answers. The definition therefore adds the remaining paper-side
resource quantification explicitly:

- `queryBound` formalizes the `t`-query restriction on malicious provers
- `knowledgeError` may depend on that query bound and on a certified failure bound
- `timeBound` is the ArkLib rendering of the paper's expected-time clause, phrased through an
  abstract additive oracle cost model

The parameters hidden in the paper notation, such as the security parameter, statement size, or an
external runtime accounting for the malicious prover, can be absorbed into `admissible`,
`knowledgeError`, and `timeBound`. -/
def rewindingKnowledgeSoundness
    (admissible : Set Statement)
    (relation : Set (Statement × Witness))
    (verifier : NonInteractiveVerifier Message oSpec Statement Bool)
    (knowledgeError : (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0)
    {ω : Type} [AddCommMonoid ω]
    (costModel : CostModel oSpec ω)
    (val : ω → ℝ≥0∞)
    (timeBound :
      (prover : Prover.NARG oSpec Statement Message) →
        (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0∞)
      -- running time `τ_𝒫̃(λ, n)` of the prover
    : Prop :=
  ∃ extractor : Extractor.RewindingNARG oSpec Statement Witness Message,
  ∀ prover : Prover.NARG oSpec Statement Message,
  ∀ queryBound : ℕ,
  ∀ failureError : ℝ≥0,
    prover.queryBounded queryBound →
    failureProbability admissible verifier prover failureError → -- `δ_𝒫̃(λ, n)`
      Pr[fun ⟨stmt, wit, accepted⟩ =>
          stmt ∈ admissible ∧ (stmt, wit) ∉ relation ∧ accepted = some true
        | rewindingKnowledgeSoundnessGame verifier extractor prover] ≤
          knowledgeError queryBound failureError ∧
        -- `ℰ` runs in expected time `et_NARG(λ, t, n, δ_𝒫̃(λ, n), τ_𝒫̃(λ, n))`
        extractor.expectedCostBound prover costModel val
          (timeBound prover queryBound failureError)
          -- Future work: double check this `extractor.expectedCostBound` separate bound, should we
          -- move it to param

end NonInteractive

section AsymptoticNonInteractive

variable {oSpec : ℕ → OracleSpec ι}
  [∀ secParam, (oSpec secParam).Fintype] [∀ secParam, (oSpec secParam).Inhabited]
  {Statement Witness Message : ℕ → Type}

/-- CO25 Definition 3.7 with the security parameter `λ` made explicit as an external index. -/
def failureProbabilityFamily
    (admissible : (secParam : ℕ) → Set (Statement secParam))
    (verifier :
      (secParam : ℕ) → NonInteractiveVerifier (Message secParam) (oSpec secParam)
        (Statement secParam) Bool)
    (prover : Prover.NARG.Family oSpec Statement Message)
    (failureError : (secParam : ℕ) → ℝ≥0) : Prop :=
  ∀ secParam, failureProbability (admissible secParam) (verifier secParam) (prover secParam)
    (failureError secParam)

/-- CO25 Definition 3.8 with the security parameter `λ` made explicit as an external index.

This is a wrapper over the fixed-`λ` notion `rewindingKnowledgeSoundness`, intended to expose the
paper's `(λ, t, n, ...)` quantification pattern without rewriting the underlying local semantics.
-/
def rewindingKnowledgeSoundnessFamily
    (admissible : (secParam : ℕ) → Set (Statement secParam))
    (relation : (secParam : ℕ) → Set (Statement secParam × Witness secParam))
    (verifier :
      (secParam : ℕ) → NonInteractiveVerifier (Message secParam) (oSpec secParam)
        (Statement secParam) Bool)
    (knowledgeError :
      (secParam : ℕ) → (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0)
    {ω : Type} [AddCommMonoid ω]
    (costModel : (secParam : ℕ) → CostModel (oSpec secParam) ω)
    (val : ω → ℝ≥0∞)
    (timeBound :
      (secParam : ℕ) →
        (prover : Prover.NARG (oSpec secParam) (Statement secParam) (Message secParam)) →
        (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0∞) : Prop :=
  ∀ secParam, rewindingKnowledgeSoundness (admissible secParam) (relation secParam)
    (verifier secParam) (knowledgeError secParam) (costModel secParam) val (timeBound secParam)

end AsymptoticNonInteractive

end Verifier
