/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ProximityPrize.Extensions.ProofSystem.Spartan.Basic

/-!
# The completed downstream first-challenge phase

The padded proof chain starts after its witness message, so the remaining witness is `Unit`.
This stage delegates the canonical random-query program on the retained statement and oracle
family.
-/

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)

/-- Completed first-challenge implementation for the downstream post-message `Unit` witness. -/
noncomputable def oracleReduction.completedFirstChallenge :
    OracleReduction oSpec
      (Statement.AfterFirstMessage R pp) (OracleStatement.AfterFirstMessage R pp) Unit
      (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
      ⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ where
  prover := firstChallengeProver R pp oSpec
  verifier := firstChallengeVerifier R pp oSpec

end Spartan.Spec
