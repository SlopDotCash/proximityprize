/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Sumcheck.Domain
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# The Spartan second sum-check oracle reduction (issue #114)

Constructs Spartan's second sum-check oracle reduction by lifting the proven full sum-check oracle
reduction (`Sumcheck.Spec.oracleReduction`) onto Spartan's virtual polynomial
`M(Y) = sum_idx r_idx * M_idx(r_x, Y) * Z(Y)` (`secondSumCheckVirtualPolynomial`), via
`OracleReduction.liftContext` -- the pattern `oracleReduction.firstChallenge` uses for `RandomQuery`.

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
-/

open MvPolynomial Matrix

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
private theorem eqPoly_evalC_eq_C_eval {m n : ℕ} (xBits : Fin m → Fin 2) (r_x : Fin m → R) :
    eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x)
        (eqPolynomial (fun i => ((xBits i : Fin 2) : MvPolynomial (Fin n) R)))
      = C (eval r_x (eqPolynomial (fun i => ((xBits i : Fin 2) : R)))) := by
  classical
  simp only [eqPolynomial, map_prod, singleEqPolynomial, Function.comp_apply, map_add, map_mul,
    map_sub, map_one, eval_X, map_natCast]

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
private theorem toMLE_evalC_eq_sum {m n : ℕ} (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) :
    eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) M.toMLE
      = ∑ xBits : Fin m → Fin 2,
          C (eval r_x (eqPolynomial (fun i => ((xBits i : Fin 2) : R)))) *
            MLE' (M (finFunctionFinEquiv xBits)) := by
  classical
  show eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) (MLE ((MLE' ∘ M) ∘ finFunctionFinEquiv)) = _
  rw [MLE, map_sum]; refine Finset.sum_congr rfl fun xBits _ => ?_
  rw [eval_mul, eval_C, eqPoly_evalC_eq_C_eval]; rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
private theorem toMLE_evalC_mem_restrictDegree {m n : ℕ} (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) :
    eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) M.toMLE ∈ R⦃≤ 1⦄[X Fin n] := by
  classical
  rw [toMLE_evalC_eq_sum, mem_restrictDegree_iff_degreeOf_le]; intro j
  refine le_trans (degreeOf_sum_le j _ _) (Finset.sup_le fun xBits _ => ?_)
  refine le_trans (degreeOf_mul_le j _ _) ?_
  rw [degreeOf_C]
  have h1 : degreeOf j (MLE' (M (finFunctionFinEquiv xBits))) ≤ 1 :=
    (mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j
  omega

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The second sum-check virtual polynomial has degree `<= 2` per variable. -/
theorem secondSCVP_mem_restrictDegree
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    secondSumCheckVirtualPolynomial R pp stmt oStmt ∈ R⦃≤ 2⦄[X Fin pp.ℓ_n] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]; intro j
  have hM : ∀ idx : R1CS.MatrixIdx,
      degreeOf j (eval (fun i => (C : R →+* MvPolynomial (Fin pp.ℓ_n) R) (stmt.2.1 i))
        (oStmt (.inr (.inl idx))).toMLE) ≤ 1 :=
    fun idx => (mem_restrictDegree_iff_degreeOf_le _ _).mp
      (toMLE_evalC_mem_restrictDegree _ stmt.2.1) j
  simp only [secondSumCheckVirtualPolynomial, Function.comp_def, Fin.cast_eq_self]
  refine le_trans (degreeOf_add_le j _ _)
    (max_le (le_trans (degreeOf_add_le j _ _) (max_le ?_ ?_)) ?_)
  · refine le_trans (degreeOf_mul_le j _ _) (le_trans (add_le_add (degreeOf_mul_le j _ _) le_rfl) ?_)
    rw [degreeOf_C]
    exact Nat.add_le_add (Nat.add_le_add (le_refl 0) (hM .A))
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j)
  · refine le_trans (degreeOf_mul_le j _ _) (le_trans (add_le_add (degreeOf_mul_le j _ _) le_rfl) ?_)
    rw [degreeOf_C]
    exact Nat.add_le_add (Nat.add_le_add (le_refl 0) (hM .B))
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j)
  · refine le_trans (degreeOf_mul_le j _ _) (le_trans (add_le_add (degreeOf_mul_le j _ _) le_rfl) ?_)
    rw [degreeOf_C]
    exact Nat.add_le_add (Nat.add_le_add (le_refl 0) (hM .C))
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j)

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

/-- Faithful reconstruction of `M.eval point` from the matrix/witness oracles (`simOStmt` core). -/
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
  (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContext
    (secondSumcheckContextLens pp) (secondSumcheckOracleLens pp oSpec)

instance instSecondSumcheckVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (secondSumcheckReduction (R := R) pp oSpec).verifier where
  hCohInl i k h := by
    simp only [secondSumcheckReduction, OracleVerifier.liftContext, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [secondSumcheckReduction, OracleVerifier.liftContext, Function.Embedding.inl_apply] at h
    cases h

#print axioms secondSumcheckReduction

end Spartan.Spec
