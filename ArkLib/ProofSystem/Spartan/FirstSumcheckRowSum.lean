/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckFaithful
import ArkLib.OracleReduction.SimOracleFoldlM
import ArkLib.Data.Matrix.Basic

/-!
# First-phase inner matrix-vector fold reconstruction (issue #114)

The first-phase (zero-check) oracle reconstruction `zeroCheckEvalFromOracles` computes each
`(M *ᵥ 𝕫)(x)` as an inner `foldlM` over the `y`-cube of `matVecSummandFromOracles`. This module
proves that inner fold simulates (under the honest single-family oracle) to the pure `foldl` whose
matrix factor is the genuine boolean matrix entry `M x y` — combining the per-summand faithfulness
(`matVecSummandFromOracles_simOracle`), the generic fold collapse
(`simulateQ_simOracle_foldlM`), and the matrix `toMLE` boolean collapse
(`Matrix.toMLE_eval_boolPoint`). This is the inner-fold ingredient of the full
`zeroCheckEvalFromOracles` faithfulness.
-/

open OracleComp OracleSpec OracleInterface MvPolynomial

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- **First-phase inner matrix-vector fold reconstruction.** The honest simulation of the inner
`y`-cube fold returns the pure `foldl` whose matrix factor is the boolean matrix entry. -/
theorem matVecInnerFold_simOracle
    (oos : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (𝕩 : Statement.AfterFirstMessage R pp) (idx : R1CS.MatrixIdx) (xEnum : Fin (2 ^ pp.ℓ_m)) :
    simulateQ (simOracle oSpec oos)
        ((Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldlM
          (fun (a : R) (yEnum : Fin (2 ^ pp.ℓ_n)) => do
            let term ← matVecSummandFromOracles R pp oSpec 𝕩 idx (boolPoint R xEnum) yEnum
            pure (a + term)) (0 : R))
      = pure ((Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldl
          (fun (a : R) (yEnum : Fin (2 ^ pp.ℓ_n)) =>
            a + (oos (.inl idx)) xEnum yEnum
              * (if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then 𝕩 ⟨(yEnum : ℕ), hy⟩
                 else eval (boolPoint R (⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x, by
                   have hlt := yEnum.isLt
                   have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
                   have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
                   omega⟩ : Fin (2 ^ pp.ℓ_w)))
                   (MLE ((oos (.inr 0)) ∘ finFunctionFinEquiv)))) (0 : R)) := by
  rw [simulateQ_simOracle_foldlM]
  intro a y
  rw [simulateQ_bind, matVecSummandFromOracles_simOracle]
  simp only [pure_bind]
  rw [show (boolPoint R xEnum : Fin pp.ℓ_m → R)
        = ((finFunctionFinEquiv.symm xEnum : Fin pp.ℓ_m → Fin 2) : Fin pp.ℓ_m → R) from rfl,
     show (boolPoint R y : Fin pp.ℓ_n → R)
        = ((finFunctionFinEquiv.symm y : Fin pp.ℓ_n → Fin 2) : Fin pp.ℓ_n → R) from rfl,
     Matrix.toMLE_eval_boolPoint]
  simp

end Spartan.Spec
