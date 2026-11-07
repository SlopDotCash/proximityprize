/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Security.Rewinding

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.Basic
import VCVio.OracleComp.QueryTracking.CostModel

/-!
  # Rewinding Knowledge Soundness

  This file defines rewinding knowledge soundness for (oracle) reductions.

  ## Oracle semantics of the non-interactive (NARG) predicates

  `Verifier.failureProbability`, `Verifier.rewindingKnowledgeSoundnessGame` /
  `Verifier.rewindingKnowledgeSoundness` and their `…Family` wrappers measure a raw
  `OracleComp oSpec` with `Pr{…}[…]` under `[OracleSpec.UniformAnswerMeasure oSpec]`. They take no
  oracle interpreter, cached random-function table or ideal-permutation implementation, so every
  query is answered by an **independent fresh uniform sample**. These predicates are therefore
  **memoryless-oracle** notions:

  * repeated queries are not consistent: querying the same Boolean-valued key twice yields
    disagreeing answers with probability `1/2`, whereas under a (lazily sampled) random function
    they always agree;
  * forward/inverse consistency of an ideal permutation is not enforced either.

  So, by themselves, they do **not** express security in the cached random-oracle model or the
  ideal-permutation model. A ROM or ideal-permutation claim needs either versions of these games
  parameterized by the intended shared oracle interpretation (with the interpreter/cache preserved
  across the prover, verifier and rewinding calls) or an explicit interpretation bridge; neither is
  provided in this file.

  The expected-time clause (`Extractor.RewindingNARG.expectedCostBound`) is likewise an expected
  **oracle-cost** bound: its `CostModel` charges oracle operations only, and pure local
  computation is free. It is not a bound on arbitrary local running time without a separate
  computation model.
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
Definition 3.6 & 3.8 of CO25. Scope: the `CostModel` charges oracle operations only (pure local
computation is free), so this is an expected **oracle-cost** bound, not a bound on arbitrary local
running time; the expectation is over the raw memoryless (fresh-uniform-answer) semantics of
`OracleComp` (see the module docstring).
-/
def RewindingNARG.expectedCostBound
    [OracleSpec.UniformAnswerMeasure oSpec]
    {ω : Type} [AddCommMonoid ω] -- `ω`: cost Type
    (extractor : RewindingNARG oSpec Statement Witness Message)
    (prover : Prover.NARG oSpec Statement Message)
    (costModel : CostModel oSpec ω)
    (val : ω → ℝ≥0∞) -- `val`: cost type value → evaluable cost
    (bound : ℝ≥0∞) : Prop :=
  letI : MeasurableSpace ω := ⊤
  ∀ stmt proof proveQueryLog verifyQueryLog,
    _root_.ExpectedCostBound (extractor stmt proof proveQueryLog verifyQueryLog prover)
      costModel val bound

end Extractor

namespace Verifier

section NonInteractive

variable {ι : Type} {oSpec : OracleSpec ι}
  [OracleSpec.UniformAnswerMeasure oSpec]
  {Statement Witness Message : Type}

/-- CO25 Definition 3.7, adapted to ArkLib's non-interactive verifier interface.

The paper's size bound `|x| ≤ n` is represented here by an arbitrary set `admissible`, so the same
definition can be reused for statement-size bounds or any other well-formedness predicate on
instances.

The probability is that of the raw `OracleComp oSpec`, i.e. every oracle query receives an
independent fresh uniform answer (memoryless oracle); no random-function cache or
ideal-permutation interpreter is applied. See the module docstring. -/
def failureProbability
    (admissible : Set Statement)
    (verifier : NonInteractiveVerifier Message oSpec Statement Bool)
    (prover : OracleComp oSpec (Statement × Message))
    (failureError : ℝ≥0) : Prop :=
  Pr{
    let ⟨stmt, proof⟩ ← prover
    let transcript : FullTranscript ⟨!v[Direction.P_to_V], !v[Message]⟩ :=
      fun | ⟨0, _⟩ => proof
    let accepted ← (verifier.run stmt transcript).run
  }[stmt ∉ admissible ∨ accepted ≠ some true] ≤ failureError

/-- The extraction experiment for CO25 Definition 3.8 in ArkLib's non-interactive interface.

This runs the malicious prover once to obtain the target statement and proof, records the prover's
and verifier's shared-oracle query logs for that accepting attempt, and then invokes the rewinding
extractor with black-box access to the prover itself.

The game is a raw `OracleComp oSpec`: when measured with `Pr[…]`, the prover's, verifier's and
extractor's queries all receive independent fresh uniform answers. No shared random-function cache
is threaded across these three calls, so a repeated query (e.g. the verifier re-querying a key the
prover already queried) need not return the same answer. -/
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
  abstract additive oracle cost model; it bounds expected **oracle cost**, not arbitrary local
  running time (pure local computation is free in a `CostModel`)

The parameters hidden in the paper notation, such as the security parameter, statement size, or an
external runtime accounting for the malicious prover, can be absorbed into `admissible`,
`knowledgeError`, and `timeBound`.

**Oracle model.** This is a *memoryless-oracle* notion: the extraction game and the failure
probability are measured on raw `OracleComp oSpec`, where every query is answered by a fresh
independent uniform sample (see the module docstring). It does not by itself express knowledge
soundness in the cached random-oracle model or the ideal-permutation model; a ROM claim requires a
version parameterized by the intended oracle interpreter or an explicit interpretation bridge,
neither of which is provided here. -/
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
      Pr{let ⟨stmt, wit, accepted⟩ ← rewindingKnowledgeSoundnessGame verifier extractor prover}[
        stmt ∈ admissible ∧ (stmt, wit) ∉ relation ∧ accepted = some true] ≤
          knowledgeError queryBound failureError ∧
        -- `ℰ` runs in expected time `et_NARG(λ, t, n, δ_𝒫̃(λ, n), τ_𝒫̃(λ, n))`
        extractor.expectedCostBound prover costModel val
          (timeBound prover queryBound failureError)
          -- Future work: double check this `extractor.expectedCostBound` separate bound, should we
          -- move it to param

end NonInteractive

section AsymptoticNonInteractive

variable {oSpec : ℕ → OracleSpec ι}
  [∀ secParam, OracleSpec.UniformAnswerMeasure (oSpec secParam)]
  {Statement Witness Message : ℕ → Type}

/-- CO25 Definition 3.7 with the security parameter `λ` made explicit as an external index
(memoryless-oracle semantics, as for `failureProbability`). -/
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
paper's `(λ, t, n, ...)` quantification pattern without rewriting the underlying local semantics;
in particular it inherits the memoryless-oracle semantics and the oracle-cost time clause described
in the module docstring.
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
