/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ProximityPrize.Extensions.ProofSystem.Spartan.Basic

/-!
# The completed downstream linear-combination phase

The padded proof chain samples the linear-combination coefficients after the evaluation-claim
message. Its `Unit`-witness stage carries the scalar claim oracles and delegates the canonical
random-query program.
-/

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)

/-- Completed post-evaluation-claim challenge phase, with its real `Unit` witness interface. -/
noncomputable def oracleReduction.completedLinearCombination :
    OracleReduction oSpec
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ where
  prover := linearCombinationProver R pp oSpec
  verifier := linearCombinationVerifier R pp oSpec

end Spartan.Spec
