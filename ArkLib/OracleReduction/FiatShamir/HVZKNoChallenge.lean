/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.ProverRunCharacterization
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
# Challenge-free basic Fiat-Shamir HVZK coupling — honest-distribution reduction (#116)

For a public-coin reduction with **no challenge rounds** and **no shared oracle** (`oSpec = []ₒ`),
the honest transcript distribution is deterministic: the run makes no oracle queries at all (the
combined spec `[]ₒ + [pSpec.Challenge]ₒ` has empty query domain), so `simulateQ` collapses to a
`pure` of the deterministic value (`simulateQ_run'_eq_pure_of_isEmpty_domain`).

`honestTranscriptDist_noChallenge_eq` records this reduction: the honest transcript distribution
equals `pure` of the answer-table evaluation of the run, projected to the transcript. This is the
step that brings the `honestTranscriptDist` (probabilistic) form of the HVZK coupling into the
deterministic `evalWithAnswerFn` form where `Reduction.prover_correspondence` and the verifier
characterization `Messages.deriveTranscriptFS_noChallenge` live.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {σ : Type}

set_option linter.unusedSectionVars false in
/-- **Challenge-free honest transcript distribution is a `pure` deterministic value.** With no
challenge rounds and no shared oracle, the interactive honest transcript distribution equals `pure`
of the answer-table evaluation of the projected run — for any answer table `f`, since the run makes
no queries. The bridge from the probabilistic `honestTranscriptDist` to the deterministic
`evalWithAnswerFn` semantics. -/
theorem honestTranscriptDist_noChallenge_eq [IsEmpty pSpec.ChallengeIdx]
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (R : Reduction []ₒ StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (f : QueryImpl ([]ₒ + [pSpec.Challenge]ₒ) Id) :
    honestTranscriptDist init impl R stmt wit
      = OptionT.mk (init >>= fun _ =>
          pure (evalWithAnswerFn f ((fun r => r.1.1) <$> R.run stmt wit).run)) := by
  unfold honestTranscriptDist
  apply OptionT.ext
  simp only [OptionT.run_mk]
  congr 1
  funext s
  rw [simulateQ_run'_eq_pure_of_isEmpty_domain (impl.addLift challengeQueryImpl) _ s f]

end Reduction

#print axioms Reduction.honestTranscriptDist_noChallenge_eq
