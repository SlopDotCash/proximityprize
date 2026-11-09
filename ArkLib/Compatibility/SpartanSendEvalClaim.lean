/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ArkLib.Extensions.ProofSystem.Spartan.Basic

/-!
# The completed downstream evaluation-claim phase

This stage follows the padded first sumcheck and consumes a `Unit` witness. It exposes the three
components of the bundled claim message as scalar output oracles for the downstream proof chain.
The canonical Spartan evaluation stage retains its claims in the public statement.
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
