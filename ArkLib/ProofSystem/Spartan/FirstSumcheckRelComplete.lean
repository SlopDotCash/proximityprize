/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckCubeSum
import ArkLib.ProofSystem.Spartan.SumcheckCubeBridge
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# The honest first sum-check projection satisfies the inner sum-check relation (issue #114)

The Spartan first sum-check is the lift of the generic sum-check onto `ℱ`. Transferring the
sum-check's completeness through that lift requires the lens' `proj_complete` obligation: an honest
(R1CS-satisfying) Spartan instance must project to an inner sum-check instance satisfying the
round-`0` relation `Sumcheck.Spec.relationRound … 0`, i.e. the Boolean-hypercube sum of the
projected polynomial equals the (constant `0`) target.

`firstSumcheck_proj_mem_relationRound` discharges exactly that: with the projection sending the
challenge to the empty vector, the target to `0`, and the oracle to `ℱ`, the round-`0` relation
`∑_{x ∈ (boolEmbedding cube)^ℓ_m} ℱ(x) = 0` holds. The proof bridges the sum-check Boolean domain to
the `Fin ℓ_m → Fin 2` cube (`sum_boolDomain_eq_sum_boolFn`) and applies the first sum-check cube-sum
identity on satisfying instances (`firstSumCheckVirtualPolynomial_hypercubeSum_eq_zero_of_satisfied`).

This is the relation-level (`proj_complete`) core of the first sum-check's completeness transfer; it
is independent of the protocol-run composition layer.
-/

open MvPolynomial Sumcheck

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams)

/-- **First sum-check `proj_complete`.** On any R1CS-satisfying instance, the projected inner
sum-check instance (empty challenge, target `0`, oracle `ℱ`) satisfies the round-`0` sum-check
relation: the Boolean-hypercube sum of `ℱ` equals the target `0`. -/
theorem firstSumcheck_proj_mem_relationRound
    (τ : Fin pp.ℓ_m → R) (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (h : R1CS.relation R pp.toSizeR1CS 𝕩 (fun idx => oStmt (.inl idx)) (oStmt (.inr 0))) :
    ((((⟨(0 : R), Fin.elim0⟩ : Sumcheck.Spec.StatementRound R pp.ℓ_m (0 : Fin (pp.ℓ_m + 1))),
        (fun _ => ⟨firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt,
                   firstSumCheckVirtualPolynomial_mem_restrictDegree pp τ 𝕩 oStmt⟩ :
          ∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i)), ())
      ∈ Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1))) := by
  simp only [Sumcheck.Spec.relationRound, Set.mem_setOf_eq]
  rw [Spartan.sum_boolDomain_eq_sum_boolFn,
    ← firstSumCheckVirtualPolynomial_hypercubeSum_eq_zero_of_satisfied pp τ 𝕩 oStmt h]
  refine Finset.sum_congr rfl fun Y _ => ?_
  apply congrArg (fun pt => MvPolynomial.eval pt (firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt))
  funext j
  simp only [Function.comp_apply, Fin.append, Fin.addCases, Fin.cast,
    eq_rec_constant, Fin.castLT, Fin.subNat]
  rfl

end Spartan.Spec
