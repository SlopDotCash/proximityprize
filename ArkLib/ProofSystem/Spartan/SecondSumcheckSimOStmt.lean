/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.SpartanBricks

/-!
# Faithfulness of the Spartan second sum-check `simOStmt` reconstruction (issue #114)

The second sum-check oracle reduction's virtual-oracle routing (`simOStmt`) must *faithfully*
reconstruct the evaluation of `ℳ(Y)` from the matrix/witness oracles. This module proves exactly
that faithfulness — the mathematical core of the `OracleVerifier.LiftContextCoherent` condition
(design note #433) needed to transfer the proven sum-check completeness through `liftContext`.

`secondSCEvalPure_simOracle0`: interpreting the oracle reconstruction `secondSCEvalPure` under the
honest oracle implementation (`OracleInterface.simOracle0`) returns exactly
`eval point (secondSumCheckVirtualPolynomial …)`.

The two halves:
* matrix queries at `(r_x, point)` answer with `eval point (eval (C ∘ r_x) M.toMLE)` (the matrix
  oracle interface *is* the bivariate `toMLE` evaluation) — captured by the per-query lemma `hq`;
* the `Z(point)` reconstruction reuses the landed S1 `zEvalFromFinalOracles_simOracle0_eq_mle_z`
  (viewing the query `point` as the `FinalStatement` second-sum-check challenge).
-/

open MvPolynomial OracleComp OracleInterface

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] (pp : Spartan.PublicParams)

/-- Oracle-only reconstruction of `ℳ.eval point`: query the matrix oracles at `(r_x, point)` and
reconstruct `Z(point)` via the landed `zEvalFromFinalOracles` (with `point` as the second-sum-check
challenge of the `FinalStatement`). -/
noncomputable def secondSCEvalPure
    (stmt : Statement.AfterLinearCombination R pp) (point : Fin pp.ℓ_n → R) :
    OracleComp [FinalOracleStatement R pp]ₒ R := do
  let r := stmt.1
  let r_x := stmt.2.1
  let a ← (OracleComp.lift <| OracleSpec.query (spec := [FinalOracleStatement R pp]ₒ)
    (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inr (.inl .A), (r_x, point)⟩) :
    OracleComp [FinalOracleStatement R pp]ₒ R)
  let b ← (OracleComp.lift <| OracleSpec.query (spec := [FinalOracleStatement R pp]ₒ)
    (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inr (.inl .B), (r_x, point)⟩) :
    OracleComp [FinalOracleStatement R pp]ₒ R)
  let c ← (OracleComp.lift <| OracleSpec.query (spec := [FinalOracleStatement R pp]ₒ)
    (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inr (.inl .C), (r_x, point)⟩) :
    OracleComp [FinalOracleStatement R pp]ₒ R)
  let z ← zEvalFromFinalOracles R pp ⟨point, stmt⟩
  pure ((r .A * a + r .B * b + r .C * c) * z)

-- This proof's `simp` needs `DecidableEq R` (the `variable` block carries `[Fintype R]` but not
-- `[DecidableEq R]`). Upstream instance-search drift made synthesizing it from the proof-local
-- `classical` too expensive (timing out both the `synthInstance` and `isDefEq` heartbeat budgets),
-- so we supply it as an explicit hypothesis instead. Callers already have `[DecidableEq R]`.
omit [IsDomain R] [Fintype R] in
/-- **`simOStmt` faithfulness.** The honest interpretation of the oracle reconstruction of `ℳ`
equals `eval point ℳ`. This is the mathematical core of `OracleVerifier.LiftContextCoherent` for the
Spartan second sum-check lift, hence of its completeness transfer. -/
theorem secondSCEvalPure_simOracle0 [DecidableEq R]
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) (point : Fin pp.ℓ_n → R) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement R pp) oStmt)
        (secondSCEvalPure pp stmt point)
      = eval point (secondSumCheckVirtualPolynomial R pp stmt oStmt) := by
  classical
  have hq : ∀ idx : R1CS.MatrixIdx,
      simulateQ (OracleInterface.simOracle0 (FinalOracleStatement R pp) oStmt)
          (OracleComp.lift <| OracleSpec.query (spec := [FinalOracleStatement R pp]ₒ)
            (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inr (.inl idx), (stmt.2.1, point)⟩) :
          OracleComp [FinalOracleStatement R pp]ₒ R)
        = eval point (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ stmt.2.1)
            (oStmt (.inr (.inl idx))).toMLE) := by
    intro idx
    simp only [simulateQ_query, OracleInterface.simOracle0, OracleQuery.cont_query,
      OracleQuery.input_query]
    rfl
  unfold secondSCEvalPure
  simp only [simulateQ_bind, hq, zEvalFromFinalOracles_simOracle0_eq_mle_z, simulateQ_pure]
  show (stmt.1 .A * eval point (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ stmt.2.1)
          (oStmt (.inr (.inl .A))).toMLE)
      + stmt.1 .B * eval point (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ stmt.2.1)
          (oStmt (.inr (.inl .B))).toMLE)
      + stmt.1 .C * eval point (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ stmt.2.1)
          (oStmt (.inr (.inl .C))).toMLE))
      * eval point (MLE (R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv))
      = eval point (secondSumCheckVirtualPolynomial R pp stmt oStmt)
  simp only [secondSumCheckVirtualPolynomial, eval_add, eval_mul, eval_C, Function.comp_def,
    Fin.cast_eq_self]
  ring

end Spartan.Spec.Bricks
