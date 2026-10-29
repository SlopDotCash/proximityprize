/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ProximityPrize.Extensions.ProofSystem.Spartan.Basic

/-!
# The completed downstream evaluation-claim phase

The canonical admitted constructor retains its original witness interface. This completed phase
follows the first sum-check, consumes a `Unit` witness, and materializes each canonical scalar claim
from the completed prover's bundled evaluation-claim message.
-/

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)

/-- Completed evaluation-claim message phase after the first sum-check's `Unit` witness. -/
noncomputable def oracleReduction.completedSendEvalClaim :
    OracleReduction oSpec
      (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  prover := sendEvalClaimProver R pp oSpec
  verifier := sendEvalClaimVerifier R pp oSpec

end Spartan.Spec
