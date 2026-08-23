/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic
import ArkLib.OracleReduction.LiftContext.Coherence

/-!
# First-phase (zero-check) oracle reconstruction faithfulness (issue #114)

The Spartan first phase (`firstChallenge`) routes the virtual zero-check polynomial's evaluation
through `zeroCheckEvalFromOracles`, which reconstructs `𝒢.eval pt` from the matrix and witness
oracles via a nested fold (outer over the `x`-cube, inner over the `y`-cube). This module proves the
per-summand building block of that reconstruction's faithfulness, the first-phase analogue of the
second-phase `hq` matrix step.

`matVecSummandFromOracles_simOracle`: under the honest single-family oracle, one matrix-vector
summand reconstructs the matrix entry (bivariate `toMLE` evaluation at the boolean point) times the
`𝕫`-coordinate value (public input or witness-MLE evaluation).
-/

open OracleComp OracleSpec OracleInterface MvPolynomial

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- **Per-summand faithfulness for the first-phase matrix-vector reconstruction.** Under the honest
single-family oracle, `matVecSummandFromOracles` returns the matrix entry (bivariate `toMLE`
evaluation at the boolean point) times the `𝕫`-coordinate value. -/
theorem matVecSummandFromOracles_simOracle
    (oos : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (𝕩 : Statement.AfterFirstMessage R pp) (idx : R1CS.MatrixIdx)
    (xBits : Fin pp.ℓ_m → R) (yEnum : Fin (2 ^ pp.ℓ_n)) :
    simulateQ (simOracle oSpec oos) (matVecSummandFromOracles R pp oSpec 𝕩 idx xBits yEnum)
      = pure (eval (boolPoint R yEnum)
            (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ xBits) (oos (.inl idx)).toMLE)
          * (if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then 𝕩 ⟨(yEnum : ℕ), hy⟩
             else eval (boolPoint R (⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x, by
                 have hlt := yEnum.isLt
                 have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
                 have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
                 omega⟩ : Fin (2 ^ pp.ℓ_w)))
               (MLE ((oos (.inr 0)) ∘ finFunctionFinEquiv)))) := by
  unfold matVecSummandFromOracles
  by_cases hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x <;>
    simp only [hy, dif_pos, simulateQ_bind, simulateQ_query, simulateQ_pure,
      OracleComp.liftComp_query, OracleComp.lift, simOracle, QueryImpl.addLift, QueryImpl.add,
      QueryImpl.liftTarget, OracleInterface.simOracle0, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, pure_bind] <;>
    rfl

end Spartan.Spec
