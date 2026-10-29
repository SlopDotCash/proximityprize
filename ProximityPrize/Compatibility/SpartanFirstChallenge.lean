/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ProximityPrize.Extensions.ProofSystem.Spartan.Basic

/-!
# The completed downstream first-challenge phase

Canonical `oracleReduction.firstChallenge` retains its inherited admitted definition and its
original witness interface. This concrete downstream phase starts after the first message,
where the remaining witness is `Unit`. It uses the completed query program and carries the
input oracle family through the canonical output materialization interface.
-/

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)

/-- Completed first-challenge implementation for the downstream post-message `Unit` witness. -/
def oracleReduction.completedFirstChallenge :
    OracleReduction oSpec
      (Statement.AfterFirstMessage R pp) (OracleStatement.AfterFirstMessage R pp) Unit
      (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
      ⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ where
  prover := firstChallengeProver R pp oSpec
  verifier := firstChallengeVerifier R pp oSpec

end Spartan.Spec
