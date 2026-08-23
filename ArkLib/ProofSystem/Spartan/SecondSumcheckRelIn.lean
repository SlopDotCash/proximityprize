/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.SpartanBricks
import ArkLib.ProofSystem.Spartan.SumcheckCubeBridge
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Sumcheck.Domain

/-!
# Second sum-check input-relation completeness (issue #114)

This module proves the honest-prover completeness ingredient for Spartan's second sum-check phase:
with the carried target equal to the random-linear-combination of the bundled evaluation claims, the
projected sum-check input statement satisfies the sum-check round-0 relation `∑_{cube} ℳ(x) = target`.

This is the `proj_complete` half of the `OracleContext.Lens.IsComplete` condition for the second
sum-check `liftContext` (the other half, `lift_complete`, and the verifier-coherence condition
`LiftContextCoherent`, are the remaining ingredients of the completeness transfer). It ties together
the cube-reindex bridge (`Spartan.sum_piFinset_const_map`) and the second sum-check claimed-sum
identity (`secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue`).
-/

open MvPolynomial OracleComp

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : Spartan.PublicParams)

set_option maxHeartbeats 1000000 in
/-- **Second sum-check input-relation completeness.** With the honest carried target (the RLC of the
bundled eval-claims), the projected sum-check input statement satisfies the sum-check round-0
relation `∑_{cube} ℳ(x) = target`. -/
theorem secondSC_relationRound_zero
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (M : R⦃≤ 2⦄[X Fin pp.ℓ_n])
    (hM : M.val = secondSumCheckVirtualPolynomial R pp stmt oStmt) :
    (((⟨∑ idx, stmt.1 idx * evalClaimValue R pp stmt.2 (fun i => oStmt (.inr i)) idx,
        Fin.elim0⟩ : Sumcheck.Spec.StatementRound R pp.ℓ_n 0),
      fun _ => M), ()) ∈ Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0 := by
  classical
  simp only [Sumcheck.Spec.relationRound, Set.mem_setOf_eq, Fin.val_zero, Nat.sub_zero]
  rw [hM]
  rw [← secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue R pp stmt oStmt]
  refine Eq.trans (Spartan.sum_piFinset_const_map (k := pp.ℓ_n) (boolEmbedding R)
    (f := fun (x : Fin pp.ℓ_n → R) => MvPolynomial.eval
      (Fin.append Fin.elim0 x ∘ Fin.cast (Nat.zero_add pp.ℓ_n).symm)
      (secondSumCheckVirtualPolynomial R pp stmt oStmt))) ?_
  refine Finset.sum_congr rfl fun Y _ => ?_
  have hpt : (Fin.append Fin.elim0 (fun i => boolEmbedding R (Y i))
        ∘ Fin.cast (Nat.zero_add pp.ℓ_n).symm)
      = (fun i => ((Y i : Fin 2) : R)) := by
    funext i
    rw [Function.comp_apply, Fin.elim0_append, Function.comp_apply]
    simp only [Fin.cast_cast, Fin.cast_eq_self]
    generalize Y i = b
    fin_cases b <;> simp [boolEmbedding]
  rw [hpt]

#print axioms secondSC_relationRound_zero

end Spartan.Spec.Bricks
