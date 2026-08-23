/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Execution

/-!
  # Security Definitions for (Oracle) Reductions

  This file defines basic security notions for (oracle) reductions:

  - (Perfect) Completeness

  - (Straightline) (Knowledge) Soundness

  - (Honest-verifier) Zero-knowledge

  For each security notion, we provide a typeclass for it, so that security can be synthesized
  automatically with verified transformations.

  See other files in the same directory for more refined soundness notions (i.e. state-restoration,
  round-by-round, rewinding, etc.)
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  -- Note: `σ` may depend on the previous data, like `StmtIn`, `pSpec`, and so on
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-
Future work: the "right" factoring for the security definitions are the following:

- We have a two-layer interpretation approach: first, interpret the oracle queries into some monad
  `m` which admits a monad morphism into `PMF` (i.e. `HasEvalDist`); then we interpret the resulting
  monad into `PMF`.

  This does not preclude `m` from being the same oracle computation type, but more interesting
  possibilities are possible, such as `m = ReaderT ρ` for lazy sampling of the shared oracle.

  Another possibility: given `OracleInterface OStmt`, we have an interpretation map

  `interpOStmt : OracleComp (oSpec + [OStmt]ₒ) →ᵐ ReaderT OStmt (OracleComp oSpec)`

- Relations should be `Stmt → Wit → m Prop`, with `m` being the intermediate monad. When `m` is the
  result of `interpOStmt` above, for instance, we get `Stmt → Wit → OStmt → Prop`, which is what we
  want. Same for when we interpret `oSpec` into `Reader (QueryImpl oSpec Id)`; we then have
  `Stmt → Wit → QueryImpl oSpec Id → Prop`, which allows us to define relations that rely
  on the (randomly sampled, at the beginning) values of the shared oracle.
-/

namespace Reduction

section Completeness

/-- A generalized completeness predicate parameterized by an arbitrary honest execution experiment.

This is the right abstraction when the verifier-side challenge process is not the default
`challengeQueryImpl`, for example when challenges are derived from a cached Fiat-Shamir function or
from the duplex-sponge oracle used by DSFS. -/
def completenessFromRun
    {ιᵣ : Type} {runSpec : OracleSpec ιᵣ} {σᵣ : Type} {Trace : Type}
    (runInit : ProbComp σᵣ)
    (runImpl : QueryImpl runSpec (StateT σᵣ ProbComp))
    -- generalized V's challenge query implementation that handles all oracle queries made during
      -- the honest execution (run). E.g. it can be lifted `challengeQueryImpl`
      -- for interactive protocols, or FS-derived/DSFS-derived challenge oracles for NARG
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (run : (stmtIn : StmtIn) → (witIn : WitIn) →
      OptionT (OracleComp runSpec) ((Trace × StmtOut × WitOut) × StmtOut))
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  (stmtIn, witIn) ∈ relIn →
    Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
        ((stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut) | OptionT.mk do
          (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit)] ≥ 1 - completenessError

/-- Perfect completeness for an arbitrary honest execution experiment. -/
def perfectCompletenessFromRun
    {ιᵣ : Type} {runSpec : OracleSpec ιᵣ} {σᵣ : Type} {Trace : Type}
    (runInit : ProbComp σᵣ)
    (runImpl : QueryImpl runSpec (StateT σᵣ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (run : (stmtIn : StmtIn) → (witIn : WitIn) →
      OptionT (OracleComp runSpec) ((Trace × StmtOut × WitOut) × StmtOut)) : Prop :=
  completenessFromRun runInit runImpl relIn relOut run 0

/-- A reduction satisfies **completeness** with regards to:
  - an initialization function `init : ProbComp σ` for some ambient state `σ`,
  - a stateful query implementation `impl` (in terms of `StateT σ ProbComp`)
  for the shared oracles `oSpec`,
  - an input relation `relIn` and output relation `relOut` (represented as sets), and
  - an error `completenessError ≥ 0`,

  if for all valid statement-witness pair `(stmtIn, witIn) ∈ relIn`, the execution between the
  honest prover and the honest verifier will result in a tuple `((prvStmtOut, witOut), stmtOut)`
  such that

  - `(stmtOut, witOut) ∈ relOut`, (the output statement-witness pair is valid) and
  - `prvStmtOut = stmtOut`, (the output statements are the same from both prover and verifier)

  except with probability `completenessError`.
-/
def completeness (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  completenessFromRun init
    (QueryImpl.addLift impl challengeQueryImpl)
    relIn relOut reduction.run completenessError

/-- A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`. -/
def perfectCompleteness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  completeness init impl relIn relOut reduction 0

/-- `Reduction.completeness` is the specialization of `completenessFromRun` to the standard
interactive execution with fresh verifier challenges from `challengeQueryImpl`. -/
@[simp]
theorem completeness_iff_completenessFromRun
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) :
    reduction.completeness init impl relIn relOut completenessError ↔
      completenessFromRun init
        (QueryImpl.addLift impl challengeQueryImpl)
        relIn relOut reduction.run completenessError := by
  rfl

/-- `Reduction.perfectCompleteness` is the specialization of `perfectCompletenessFromRun` to the
standard interactive execution with fresh verifier challenges from `challengeQueryImpl`. -/
@[simp]
theorem perfectCompleteness_iff_perfectCompletenessFromRun
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    reduction.perfectCompleteness init impl relIn relOut ↔
      perfectCompletenessFromRun init
        (QueryImpl.addLift impl challengeQueryImpl)
        relIn relOut reduction.run := by
  rfl

/-- Type class for completeness for a reduction -/
class IsComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    where
  completenessError : ℝ≥0
  is_complete : completeness init impl relIn relOut reduction completenessError

/-- Type class for perfect completeness for a reduction -/
class IsPerfectComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  is_perfect_complete : perfectCompleteness init impl relIn relOut reduction

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}

instance [reduction.IsPerfectComplete init impl relIn relOut] :
    IsComplete init impl relIn relOut reduction where
  completenessError := 0
  is_complete := IsPerfectComplete.is_perfect_complete

/-- If a reduction satisfies completeness with error `ε₁`, then it satisfies completeness with error
  `ε₂` for all `ε₂ ≥ ε₁`. -/
@[grind]
theorem completeness_error_mono {ε₁ ε₂ : ℝ≥0} (hε : ε₁ ≤ ε₂) :
    completeness init impl relIn relOut reduction ε₁ →
        completeness init impl relIn relOut reduction ε₂ := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hstmtIn
  have := h stmtIn witIn hstmtIn
  refine ge_trans this ?_
  exact tsub_le_tsub_left (by simp [hε]) 1

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relIn'` that is a subset of `relIn`. -/
@[simp, grind]
theorem completeness_relIn_mono {ε : ℝ≥0} {relIn' : Set (StmtIn × WitIn)}
    (hrelIn : relIn' ⊆ relIn) :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn' relOut reduction ε := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hStmtIn
  exact h stmtIn witIn (hrelIn hStmtIn)

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relOut'` that is a superset of `relOut`.
-/

theorem completeness_relOut_mono {ε : ℝ≥0} {relOut' : Set (StmtOut × WitOut)}
    (hrelOut : relOut ⊆ relOut') :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn relOut' reduction ε := by
  intro h stmtIn witIn hIn
  exact ge_trans (probEvent_mono fun _ _ ⟨h1, h2⟩ => ⟨hrelOut h1, h2⟩) (h stmtIn witIn hIn)

/-- Perfect completeness means that the probability of the reduction outputting a valid
  statement-witness pair is _exactly_ 1 (instead of at least `1 - 0`). -/
@[simp]
theorem perfectCompleteness_eq_prob_one :
    reduction.perfectCompleteness init impl relIn relOut ↔
    ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
        QueryImpl.addLift impl challengeQueryImpl
      Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
          ((stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut)
        | OptionT.mk do (simulateQ pImpl (reduction.run stmtIn witIn)).run' (← init)] = 1 := by
  simp only [perfectCompleteness, completeness, completenessFromRun, ENNReal.coe_zero, tsub_zero]
  refine forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ => ?_
  exact ⟨fun h => le_antisymm probEvent_le_one (ge_iff_le.mp h),
     fun h => ge_of_eq h⟩

-- /-- For a reduction without shared oracles (i.e. `oSpec = []ₒ`), perfect completeness occurs
--   when the reduction produces satisfying statement-witness pairs for all possible challenges. -/
-- theorem perfectCompleteness_forall_challenge [reduction.IsDeterministic] :
--       reduction.perfectCompleteness relIn relOut ↔
--         ∀ stmtIn witIn, relIn stmtIn witIn → ∀ chals : ∀ i, pSpec.Challenge i,
--           reduction.runWithChallenges stmtIn witIn chals = 1 := by

end Completeness

end Reduction

section Soundness

/-! We define 3 variants each of soundness and knowledge soundness:

  1. (Plain) soundness
  2. Knowledge soundness

  For adaptivity, we may want to seed the definition with a term
    `chooseStmtIn : OracleComp oSpec StmtIn`
  (though this is essentially the same as quantifying over all `stmtIn : StmtIn`).

  Note: all soundness definitions are really defined for the **verifier** only. The (honest)
prover does not feature into the definitions.
-/

namespace Extractor

/- We define different types of extractors here -/

variable (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)

/-- A straightline, deterministic, non-oracle-querying extractor takes in the output witness, the
  initial statement, the IOR transcript, and the query logs from the prover and verifier, and
  returns a corresponding initial witness.

  Note that the extractor does not need to take in the output statement, since it can be derived
  via re-running the verifier on the initial statement, the transcript, and the verifier's query
  log.

  This form of extractor suffices for proving knowledge soundness of most hash-based IOPs.
-/
def Straightline :=
  StmtIn → -- input statement
  WitOut → -- output witness
  FullTranscript pSpec → -- reduction transcript
  QueryLog oSpec → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OptionT (OracleComp oSpec) WitIn -- input witness

end Extractor

namespace Verifier

/-- A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input
  language `langIn : Set StmtIn` and output language `langOut : Set StmtOut` if:
  - for all (malicious) provers with arbitrary types for `WitIn`, `WitOut`,
  - for all arbitrary `witIn`,
  - for all input statement `stmtIn ∉ langIn`,

  the execution between the prover and the honest verifier will result in an output statement
  `stmtOut` that is in `langOut` is at most `soundnessError`.

  (technical note: since execution may fail, this is _not_ equivalent to saying that
  `stmtOut ∉ langOut` with probability at least `1 - soundnessError`)
-/
def soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ stmtIn ∉ langIn,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    letI reduction := Reduction.mk prover verifier
    Pr[fun ⟨_, stmtOut⟩ => stmtOut ∈ langOut | OptionT.mk do
      (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)] ≤ soundnessError

/-- Type class for soundness for a verifier -/
class IsSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  soundnessError : ℝ≥0
  is_sound : soundness init impl langIn langOut verifier soundnessError

/-- Verifier soundness is monotone in the allowed soundness error. -/
theorem soundness.mono_error
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (hSound : soundness init impl langIn langOut verifier soundnessError₁)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    soundness init impl langIn langOut verifier soundnessError₂ := by
  intro WitIn WitOut witIn prover stmtIn hstmtIn
  exact le_trans (hSound WitIn WitOut witIn prover stmtIn hstmtIn)
    (ENNReal.coe_le_coe.mpr hle)

/-- Verifier soundness is monotone in the input and output languages.

If soundness holds for a smaller honest input language and a larger accepting output language, then
it also holds after enlarging the honest input language and shrinking the accepting output language.
-/
theorem soundness.mono_languages
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {soundnessError : ℝ≥0}
    (hSound : soundness init impl langIn langOut verifier soundnessError)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut) :
    soundness init impl langIn' langOut' verifier soundnessError := by
  intro WitIn WitOut witIn prover stmtIn hstmtIn
  refine le_trans ?_ (hSound WitIn WitOut witIn prover stmtIn ?_)
  · exact probEvent_mono fun _ _ h => hOut h
  · exact fun h => hstmtIn (hIn h)

-- How would one define a rewinding extractor? It should have oracle access to the prover's
-- functions (receive challenges and send messages), and be able to observe & simulate the prover's
-- oracle queries
#check Reduction.runWithLog
/-- A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and
  with respect to input relation `relIn` and output relation `relOut` if:
  - there exists a straightline extractor `E`, such that
  - for all input statement `stmtIn`, witness `witIn`, and (malicious) prover `prover`,
  - if the execution with the honest verifier results in a pair `(stmtOut, witOut)`,
  - and the extractor produces some `witIn'`,

  then the probability that `(stmtIn, witIn')` is not valid and yet `(stmtOut, witOut)` is valid
  is at most `knowledgeError`.
-/
def knowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
      let extractedWitIn ← extractor stmtIn witOut transcript proveQueryLog.fst verifyQueryLog
      return (stmtIn, extractedWitIn, stmtOut, witOut)
    Pr[fun ⟨stmtIn, witIn, stmtOut, witOut⟩ =>
        (stmtIn, witIn) ∉ relIn ∧ (stmtOut, witOut) ∈ relOut
      | OptionT.mk do (simulateQ pImpl exec.run).run' (← init)] ≤ knowledgeError

/-- Type class for knowledge soundness for a verifier -/
class IsKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  knowledgeError : ℝ≥0
  is_knowledge_sound : knowledgeSoundness init impl relIn relOut verifier knowledgeError

/-- Straightline knowledge soundness is monotone in the allowed knowledge error. -/
theorem knowledgeSoundness.mono_error
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (hSound : knowledgeSoundness init impl relIn relOut verifier knowledgeError₁)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    knowledgeSoundness init impl relIn relOut verifier knowledgeError₂ := by
  obtain ⟨extractor, hSound⟩ := hSound
  exact ⟨extractor, fun stmtIn witIn prover =>
    le_trans (hSound stmtIn witIn prover) (ENNReal.coe_le_coe.mpr hle)⟩

/-- Straightline knowledge soundness is monotone in the input and output relations.

If knowledge soundness holds for a smaller valid input relation and a larger valid output relation,
then it also holds after enlarging the valid input relation and shrinking the valid output relation.
-/
theorem knowledgeSoundness.mono_relations
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {knowledgeError : ℝ≥0}
    (hSound : knowledgeSoundness init impl relIn relOut verifier knowledgeError)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut) :
    knowledgeSoundness init impl relIn' relOut' verifier knowledgeError := by
  obtain ⟨extractor, hSound⟩ := hSound
  refine ⟨extractor, fun stmtIn witIn prover => ?_⟩
  refine le_trans ?_ (hSound stmtIn witIn prover)
  exact probEvent_mono fun ⟨stmtIn', witIn', stmtOut, witOut⟩ _ h =>
    ⟨fun hValid => h.1 (hIn hValid), hOut h.2⟩

/-- An extractor is **monotone** if its success probability on a given query log is the same as
  the success probability on any extension of that query log. -/
class Extractor.Straightline.IsMonotone
    (relIn : Set (StmtIn × WitIn))
    (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    [oSpec.Fintype] [oSpec.Inhabited]
    where
  is_monotone : ∀ witOut stmtIn transcript, ∀ proveQueryLog₁ proveQueryLog₂ : oSpec.QueryLog,
    ∀ verifyQueryLog₁ verifyQueryLog₂ : oSpec.QueryLog,
    proveQueryLog₁.Sublist proveQueryLog₂ →
    verifyQueryLog₁.Sublist verifyQueryLog₂ →
    -- Monotonicity is stated over the extractor's success probability on the current query logs.
    Pr[fun witIn => (stmtIn, witIn) ∈ relIn |
      E stmtIn witOut transcript proveQueryLog₁ verifyQueryLog₁] ≤
    Pr[fun witIn => (stmtIn, witIn) ∈ relIn |
      E stmtIn witOut transcript proveQueryLog₂ verifyQueryLog₂]
    -- Pr[extraction game succeeds on proveQueryLog₁, verifyQueryLog₁]
    -- ≤ Pr[extraction game succeeds on proveQueryLog₂, verifyQueryLog₂]

end Verifier

end Soundness

namespace Reduction

section ZeroKnowledge

/-- A simulator for a reduction needs to produce the same transcript as the prover (but potentially
  all at once, instead of sequentially). We also grant the simulator the power to program the shared
  oracles `oSpec` -/
structure Simulator (oSpec : OracleSpec ι) (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  SimState : Type
  oracleSim : QueryImpl oSpec (StateT SimState (OracleComp oSpec))
  proverSim : StmtIn → StateT SimState (OracleComp oSpec) pSpec.FullTranscript


end ZeroKnowledge

end Reduction

/-! Completeness and soundness are the same as for non-oracle reductions. Only zero-knowledge is
  different (but we haven't defined it yet) -/

open Reduction

section OracleProtocol

variable [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleReduction

open Classical in
/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
def completeness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  Reduction.completeness init impl relIn relOut oracleReduction.toReduction completenessError

open Classical in
/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
def perfectCompleteness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      Prop :=
  Reduction.perfectCompleteness init impl relIn relOut oracleReduction.toReduction

end OracleReduction

namespace OracleVerifier

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
def soundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.toVerifier.soundness init impl langIn langOut soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
def knowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundness init impl relIn relOut knowledgeError

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)] {Witness : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

/-! All security notions are inherited from `Reduction`, with the output relation specialized to the
  trivial accept/reject one: `fun accRej _ => accRej`. -/

open Reduction Classical

@[reducible, simp]
def completeness (relation : Set (Statement × Witness)) (completenessError : ℝ≥0)
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.completeness init impl relation acceptRejectRel proof completenessError

@[reducible, simp]
def perfectCompleteness (relation : Set (Statement × Witness))
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.perfectCompleteness init impl relation acceptRejectRel proof

@[reducible, simp]
def soundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.soundness init impl langIn acceptRejectRel.language soundnessError

@[reducible, simp]
def knowledgeSoundness (relation : Set (Statement × Bool))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.knowledgeSoundness init impl relation acceptRejectRel knowledgeError

end Proof

namespace OracleProof

open OracleReduction Classical

/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def completeness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec)
    (completenessError : ℝ≥0) : Prop :=
  OracleReduction.completeness init impl
    relation acceptRejectOracleRel oracleProof completenessError

/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def perfectCompleteness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec) :
      Prop :=
  OracleReduction.perfectCompleteness init impl relation acceptRejectOracleRel oracleProof

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def soundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.toVerifier.soundness init impl langIn acceptRejectOracleRel.language soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def knowledgeSoundness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundness init impl relation acceptRejectOracleRel knowledgeError

end OracleProof

section Trivial

-- We show that the trivial (oracle) reduction is perfectly complete, sound, and knowledge sound.

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem Reduction.id_perfectCompleteness {rel : Set (StmtIn × WitIn)} :
    (Reduction.id : Reduction oSpec _ _ _ _ _).perfectCompleteness init impl rel rel := by
  simp only [perfectCompleteness, completeness, completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  simp only [Reduction.id_run]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- Pr[⊥ | OptionT.mk ...] = 0
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, stmtIn, witIn), stmtIn)) :
        OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ support
      (Prod.fst <$> (pure (some ((default, stmtIn, witIn), stmtIn)) :
        StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp [map_pure]
  · -- ∀ x ∈ support, event x
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, stmtIn, witIn), stmtIn)) :
        OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure (some ((default, stmtIn, witIn), stmtIn)) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hx
    cases hx
    exact ⟨hIn, rfl⟩

private lemma Reduction.run_mk_verifier_id {WitIn WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtIn WitOut !p[])
    (stmtIn : StmtIn) (witIn : WitIn) :
    (Reduction.mk prover Verifier.id).run stmtIn witIn =
      (fun pr => (pr, stmtIn)) <$> prover.run stmtIn witIn := by
  simp only [Reduction.run, Verifier.run, Verifier.id, OptionT.run_pure,
    monadLift_bind, Function.comp_apply, monadLift_pure,
    pure_bind, Option.getM, map_eq_bind_pure_comp]

/-- The identity / trivial verifier is perfectly sound. -/
@[simp]
theorem Verifier.id_soundness {lang : Set StmtIn} :
    (Verifier.id : Verifier oSpec _ _ _).soundness init impl lang lang 0 := by
  unfold soundness
  intro WitIn WitOut witIn prover stmtIn hstmtIn
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Reduction.run_mk_verifier_id,
    probEvent_eq_zero_iff]
  intro x hx hev
  apply hstmtIn
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  simp only [StateT.run'_eq, support_map, Set.mem_image] at hx
  obtain ⟨⟨a, s'⟩, ha, rfl⟩ := hx
  have hliftM : (liftM ((fun pr => (pr, stmtIn)) <$> Prover.run stmtIn witIn prover) :
      OptionT (OracleComp _) _).run =
      (fun pr => some (pr, stmtIn)) <$> Prover.run stmtIn witIn prover := by
    simp [Functor.map_map]
  rw [hliftM, simulateQ_map, StateT.run_map] at ha
  simp only [support_map, Set.mem_image, Prod.exists] at ha
  obtain ⟨pr, s'', ⟨b, _, _, heq⟩⟩ := ha
  have := (Prod.mk.inj heq).1
  have := Option.some.inj this
  have := (Prod.mk.inj this).2
  rw [← this] at hev
  exact hev

/-- The straightline extractor for the identity / trivial reduction, which just returns the input
  witness. -/
@[reducible]
def Extractor.Straightline.id : Extractor.Straightline oSpec StmtIn WitIn WitIn !p[] :=
  fun _ witOut _ _ _ => pure witOut

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp]
theorem Verifier.id_knowledgeSoundness {rel : Set (StmtIn × WitIn)} :
    (Verifier.id : Verifier oSpec _ _ _).knowledgeSoundness init impl rel rel 0 := by
  unfold knowledgeSoundness
  refine ⟨Extractor.Straightline.id, fun stmtIn witIn prover => ?_⟩
  simp only [Extractor.Straightline.id, ENNReal.coe_zero, nonpos_iff_eq_zero,
    probEvent_eq_zero_iff]
  intro x hx ⟨hNotIn, hIn⟩
  -- hNotIn : (x.1, x.2.1) ∉ rel, hIn : (x.2.2.1, x.2.2.2) ∈ rel
  -- From the computation structure: x.2.1 = x.2.2.2 (extractor returns witOut)
  -- and x.1 = x.2.2.1 (Verifier.id gives stmtOut = stmtIn).
  -- Follow id_soundness support analysis pattern.
  -- Decompose support to extract x's structure.
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  simp only [StateT.run'_eq, support_map, Set.mem_image] at hx
  obtain ⟨⟨a, s'⟩, ha, rfl⟩ := hx
  apply hNotIn
  -- Simplify the OptionT do block in ha: liftM (pure v) = pure v, then bind collapses to map
  -- Since OptionT is transparent, these rewrite inside .run
  -- Decompose the OptionT bind via OptionT.run_bind + simulateQ_bind
  simp only [OptionT.run_bind, Option.elimM] at ha
  rw [simulateQ_bind] at ha
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion, Prod.exists] at ha
  obtain ⟨opt, s₂, hopt, ha'⟩ := ha
  -- Case split: runWithLog returns some d or none
  rcases opt with _ | d
  · -- none case: contradiction with some x
    simp [simulateQ_pure, StateT.run_pure, support_pure] at ha'
  · -- some d: continuation simplifies to pure (some (stmtIn, d.1.1.2.2, d.1.2, d.1.1.2.2))
    dsimp at ha'
    simp only [OptionT.run_pure] at ha'
    have hx : x = (stmtIn, d.1.1.2.2, d.1.2, d.1.1.2.2) :=
      Option.some.inj (Prod.mk.inj ha').1
    rw [hx]; rw [hx] at hIn
    -- Goal: (stmtIn, d.1.1.2.2) ∈ rel; hIn: (d.1.2, d.1.1.2.2) ∈ rel
    suffices h : d.1.2 = stmtIn by rwa [h] at hIn
    -- Derive d.1.2 = stmtIn from runWithLog_discard_logs_eq_run + run_mk_verifier_id
    have hfst_eq := Reduction.runWithLog_discard_logs_eq_run
      (reduction := { prover := prover, verifier := Verifier.id })
      (stmt := stmtIn) (wit := witIn)
    rw [Reduction.run_mk_verifier_id] at hfst_eq
    -- Convert hfst_eq to OracleComp level via OptionT.run
    have h_eq := congr_arg OptionT.run hfst_eq
    simp only [OptionT.run_map] at h_eq
    -- h_eq : (Option.map Prod.fst) <$> (runWithLog ...).run = (...) <$> prover.run
    -- Build membership in the target support directly
    have hmem : (some d.1, s₂) ∈ support
        (((fun pr => some (pr, stmtIn)) <$>
          simulateQ (impl.addLift challengeQueryImpl)
            (Prover.run stmtIn witIn prover) : StateT σ ProbComp _).run s) := by
      have h1 : (some d.1, s₂) ∈ support
          (((Option.map Prod.fst) <$>
            simulateQ (impl.addLift challengeQueryImpl)
              (runWithLog stmtIn witIn
                { prover := prover, verifier := Verifier.id }).run :
            StateT σ ProbComp _).run s) := by
        rw [StateT.run_map, support_map]; exact ⟨(some d, s₂), hopt, rfl⟩
      rw [← simulateQ_map, h_eq] at h1
      -- h1 has monadLift form which is definitionally equal to the goal
      convert h1 using 2
      simp [Functor.map_map, simulateQ_map]
    rw [StateT.run_map, support_map, Set.mem_image] at hmem
    obtain ⟨⟨pr, s₃⟩, _, heq⟩ := hmem
    exact (Prod.mk.inj (Option.some.inj (Prod.mk.inj heq).1)).2.symm

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem OracleReduction.id_perfectCompleteness
    {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)} :
    (OracleReduction.id : OracleReduction oSpec _ _ _ _ _ _ _).perfectCompleteness
      init impl rel rel := by
  unfold OracleReduction.perfectCompleteness
  simp only [OracleReduction.id_toReduction, Reduction.id_perfectCompleteness]

/-- The identity / trivial verifier is perfectly sound. -/
@[simp, grind .]
theorem OracleVerifier.id_soundness {lang : Set (StmtIn × ∀ i, OStmtIn i)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).soundness
      init impl lang lang 0 := by
  simp [OracleVerifier.soundness]

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp, grind .]
theorem OracleVerifier.id_knowledgeSoundness {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).knowledgeSoundness
      init impl rel rel 0 := by
  simp [OracleVerifier.knowledgeSoundness]

end Trivial

end
