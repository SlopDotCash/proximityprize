/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Conditional sumcheck facts under canonical message-polynomial semantics

The input-only rejection and transcript-independent concrete knowledge-state claims from the old
verifier are retired. The declarations below retain only mathematical correspondence, outer-phase,
or explicitly conditional knowledge-flip results. No zero-error sumcheck completion follows from
this module. Exact retired commands are in
`scripts/integration/sumcheck-message-semantics-retirements.json`.
-/

open Polynomial MvPolynomial OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal ENNReal

namespace Sumcheck.Spec

variable {ι : Type} (oSpec : OracleSpec ι)
variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
  [DecidableEq R] [SampleableType R]

namespace SingleRound.Simple

end SingleRound.Simple

namespace SingleRound

/-- **The round lens carries the round relation exactly (statement side).** The projected Simple
statement satisfies `Simple.inputRelation` **iff** the outer round statement satisfies
`relationRound i.castSucc`: both sides reduce to a sum-equals-target claim, and the two sums agree
by the (now public) `sumcheck_round_split` splitting identity — the same identity behind the lens
*completeness* (`oCtxLens_complete.proj_complete`); soundness reads it right-to-left. -/
theorem simpleProj_mem_iff (n : ℕ) (i : Fin n)
    (stmt : StatementRound R n i.castSucc) (oStmt : ∀ j, OracleStatement R n deg j) :
    (((oStmtLens R n deg D i).proj (stmt, oStmt)), ()) ∈ Simple.inputRelation R deg D
      ↔ ((stmt, oStmt), ()) ∈ relationRound R n deg D i.castSucc := by
  have h := projected_sum_iff_relationRound R n deg D i stmt (oStmt ())
  have hsum := Multiset.sum_map_toList (univ.map D).val
    (fun x => (projectedRoundPolynomial R n deg D i stmt.challenges (oStmt ())).val.eval x)
  change (List.map _ (univ.map D).toList).sum = ∑ x ∈ univ.map D, _ at hsum
  rw [hsum] at h
  simpa [Simple.inputRelation, oStmtLens, Statement.Lens.proj] using h

end SingleRound

end Sumcheck.Spec

/- Axiom audit. -/
#print axioms Sumcheck.Spec.SingleRound.simpleProj_mem_iff
