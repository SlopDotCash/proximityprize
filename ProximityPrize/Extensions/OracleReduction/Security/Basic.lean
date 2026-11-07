/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Security.Basic

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Execution

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
    Pr{let ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ ← OptionT.mk do
      (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit)}[
        (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut] ≥ 1 - completenessError

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

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}

instance [reduction.IsPerfectComplete init impl relIn relOut] :
    IsComplete init impl relIn relOut reduction where
  completenessError := 0
  is_complete := IsPerfectComplete.is_perfect_complete

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

end Extractor

namespace Verifier

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
  · exact prEvent_mono _ _ _ fun _ h => hOut h
  · exact fun h => hstmtIn (hIn h)

-- How would one define a rewinding extractor? It should have oracle access to the prover's
-- functions (receive challenges and send messages), and be able to observe & simulate the prover's
-- oracle queries
#check Reduction.runWithLog
/-- Straightline knowledge soundness is monotone in the allowed knowledge error. -/
theorem knowledgeSoundness.mono_error
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (hSound : knowledgeSoundness init impl relIn relOut verifier knowledgeError₁)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    knowledgeSoundness init impl relIn relOut verifier knowledgeError₂ := by
  obtain ⟨extractor, hSound⟩ := hSound
  exact ⟨extractor, fun Aux stmtIn aux prover =>
    le_trans (hSound Aux stmtIn aux prover) (ENNReal.coe_le_coe.mpr hle)⟩

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
  refine ⟨extractor, fun Aux stmtIn aux prover => ?_⟩
  refine le_trans ?_ (hSound Aux stmtIn aux prover)
  refine prEvent_mono _ _ _ ?_
  rintro ⟨stmtIn', extractedWitIn?, stmtOut, witOut⟩ h
  exact ⟨fun witIn hmem hValid => h.1 witIn hmem (hIn hValid), hOut h.2⟩

end Verifier

end Soundness

namespace Reduction

section ZeroKnowledge

end ZeroKnowledge

end Reduction

/-! Completeness and soundness are the same as for non-oracle reductions. Only zero-knowledge is
  different (but we haven't defined it yet) -/

open Reduction

section OracleProtocol

variable [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleReduction

end OracleReduction

namespace OracleVerifier

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

end Proof

namespace OracleProof

open OracleReduction Classical

end OracleProof

section Trivial

-- We show that the trivial (oracle) reduction is perfectly complete, sound, and knowledge sound.

private lemma Reduction.run_mk_verifier_id {WitIn WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtIn WitOut !p[])
    (stmtIn : StmtIn) (witIn : WitIn) :
    (Reduction.mk prover Verifier.id).run stmtIn witIn =
      (fun pr => (pr, stmtIn)) <$> prover.run stmtIn witIn := by
  simp only [Reduction.run, Verifier.run, Verifier.id, OptionT.run_pure,
    monadLift_bind, Function.comp_apply, monadLift_pure,
    pure_bind, Option.getM, map_eq_bind_pure_comp]

end Trivial

end
