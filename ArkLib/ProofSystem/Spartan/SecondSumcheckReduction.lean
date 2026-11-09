/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.SumcheckDegreeBound
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.Extensions.ProofSystem.Sumcheck.Domain
import ArkLib.Extensions.OracleReduction.LiftContext.OracleReduction

/-!
# The Spartan second sum-check oracle reduction (issue #114)

Constructs Spartan's second sum-check oracle reduction by lifting the proven full sum-check oracle
reduction (`Sumcheck.Spec.oracleReduction`) onto Spartan's virtual polynomial
`M(Y) = sum_idx r_idx * M_idx(r_x, Y) * Z(Y)` (`secondSumCheckVirtualPolynomial`), via
`OracleReduction.liftContextLegacy`.

The inner sum-check input `Sumcheck.Spec.StatementRound R l_n 0` has a `target` field equal to the
random-linear-combination of the bundled eval-claims -- an oracle-dependent value, which
`liftContext`'s `projStmt` cannot compute. So the outer input statement carries the target:
`R x Statement.AfterLinearCombination` (mirroring the final `CheckClaim`'s
`FinalClaimStatement := R x FinalStatement`). The honest-prover identity that this target equals the
cube-sum is `secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue`.

Inner univariate queries to `M` at a point are answered by querying the matrix oracles at
`(r_x, point)` (the matrix oracle interface is the bivariate matrix-MLE evaluation) and reconstructing
`Z(point)` from the public input plus witness oracle (Boolean-cube fold). The degree bound
`secondSCVP_mem_restrictDegree` packages `M` as the `R[<=2][X Fin l_n]` oracle.

**Query cost and scope.** `secondSumcheckEvalFromOracles` is a correct reference reconstruction,
not a constant-cost oracle read. Each evaluation makes three matrix queries and folds over all
`2 ^ l_n` Boolean column indices, making a witness query for every non-public column (`2 ^ l_w`
witness queries per evaluation). The lifted `Sumcheck.Spec.oracleReduction` round verifiers read
only the prover messages (three message queries per Boolean round) and make no query to `M`
themselves. The reconstruction cost is paid on every query that reaches `M`, for example a final
evaluation check. A succinct-verifier claim must account for that cost.
-/

open MvPolynomial Matrix

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The second sum-check virtual polynomial has degree `<= 2` per variable. -/
theorem secondSCVP_mem_restrictDegree
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    secondSumCheckVirtualPolynomial R pp stmt oStmt ∈ R⦃≤ 2⦄[X Fin pp.ℓ_n] :=
  Spartan.secondSCVP_mem_restrictDegree pp stmt oStmt

/-- The value-level oracle-statement lens for the second sum-check. -/
noncomputable def secondSumcheckStmtLens :
    OracleStatement.Lens
      (R × Statement.AfterLinearCombination R pp) (Statement.AfterSecondSumcheck R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n))
      (OracleStatement.AfterLinearCombination R pp) (OracleStatement.AfterSecondSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) where
  toFunA := fun ⟨⟨t, stmt⟩, oStmt⟩ =>
    ⟨⟨t, Fin.elim0⟩,
     fun _ => ⟨secondSumCheckVirtualPolynomial R pp stmt oStmt,
               secondSCVP_mem_restrictDegree pp stmt oStmt⟩⟩
  toFunB := fun ⟨⟨_t, stmt⟩, oStmt⟩ ⟨⟨_t', r_y⟩, _innerO⟩ => ⟨(r_y, stmt), oStmt⟩

/-- Faithful reconstruction of `M.eval point` from the matrix/witness oracles (`simOStmt` core).

Query cost: three matrix queries, plus a fold over all `2 ^ ℓ_n` Boolean column indices that makes
one witness query per non-public column (`2 ^ ℓ_w` witness queries). The witness contraction
`Z(point)` is recomputed from every witness entry on every call. -/
noncomputable def secondSumcheckEvalFromOracles
    (stmt : Statement.AfterLinearCombination R pp) (point : Fin pp.ℓ_n → R) :
    OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R := do
  let r := stmt.1
  let r_x := stmt.2.1
  let x := stmt.2.2.2
  let a ← (OracleComp.lift <| OracleSpec.query
    (spec := [OracleStatement.AfterLinearCombination R pp]ₒ)
    (show [OracleStatement.AfterLinearCombination R pp]ₒ.Domain from ⟨.inr (.inl .A), (r_x, point)⟩) :
    OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
  let b ← (OracleComp.lift <| OracleSpec.query
    (spec := [OracleStatement.AfterLinearCombination R pp]ₒ)
    (show [OracleStatement.AfterLinearCombination R pp]ₒ.Domain from ⟨.inr (.inl .B), (r_x, point)⟩) :
    OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
  let c ← (OracleComp.lift <| OracleSpec.query
    (spec := [OracleStatement.AfterLinearCombination R pp]ₒ)
    (show [OracleStatement.AfterLinearCombination R pp]ₒ.Domain from ⟨.inr (.inl .C), (r_x, point)⟩) :
    OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
  let z ← (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldlM
    (fun (acc : R) (yEnum : Fin (2 ^ pp.ℓ_n)) => do
      let coeff : R := eval point (eqPolynomial (boolPoint R yEnum))
      let zVal : R ←
        if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then
          (pure (x ⟨(yEnum : ℕ), hy⟩) :
            OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
        else
          (OracleComp.lift <| OracleSpec.query
            (spec := [OracleStatement.AfterLinearCombination R pp]ₒ)
            (show [OracleStatement.AfterLinearCombination R pp]ₒ.Domain from
              ⟨.inr (.inr 0), boolPoint R ⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x, by
                have hlt := yEnum.isLt
                have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
                have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
                omega⟩⟩) :
            OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
      pure (acc + coeff * zVal))
    (0 : R)
  pure ((r .A * a + r .B * b + r .C * c) * z)

/-- The oracle-routing lens for the second sum-check. -/
noncomputable def secondSumcheckOracleLens :
    OracleStatement.OracleLens oSpec
      (R × Statement.AfterLinearCombination R pp) (Statement.AfterSecondSumcheck R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n))
      (OracleStatement.AfterLinearCombination R pp) (OracleStatement.AfterSecondSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2)
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) where
  toLens := secondSumcheckStmtLens pp
  projStmt := fun ⟨t, _stmt⟩ => ⟨t, Fin.elim0⟩
  liftStmt := fun ⟨_t, stmt⟩ ⟨_t', r_y⟩ => (r_y, stmt)
  simOStmt := fun q => match q with
    | ⟨_, point⟩ => ReaderT.mk fun ⟨_t, stmt⟩ => secondSumcheckEvalFromOracles pp oSpec stmt point
  embedOStmt := Function.Embedding.inl
  hEqOStmt := fun _ => rfl
  outputInterface_heq := fun _ => HEq.rfl

/-- The value-level oracle context lens for the second sum-check. -/
noncomputable def secondSumcheckContextLens :
    OracleContext.Lens
      (R × Statement.AfterLinearCombination R pp) (Statement.AfterSecondSumcheck R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n))
      (OracleStatement.AfterLinearCombination R pp) (OracleStatement.AfterSecondSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2)
      Unit Unit Unit Unit where
  stmt := secondSumcheckStmtLens pp
  wit := ⟨fun _ => (), fun _ _ => ()⟩

/-- **The Spartan second sum-check oracle reduction**, constructed by lifting the proven full
sum-check oracle reduction onto Spartan's virtual polynomial `M(Y)` (issue #114). -/
noncomputable def secondSumcheckReduction :
    OracleReduction oSpec
      (R × Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheck R pp) (OracleStatement.AfterSecondSumcheck R pp) Unit
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) :=
  (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContextLegacy
    (secondSumcheckContextLens pp) (secondSumcheckOracleLens pp oSpec)

#print axioms secondSumcheckReduction

end Spartan.Spec
