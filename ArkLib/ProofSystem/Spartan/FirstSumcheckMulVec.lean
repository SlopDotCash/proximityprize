/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckRowSum
import ArkLib.Data.MvPolynomial.Multilinear

/-!
# First-phase inner fold reconstructs the matrix-vector product (issue #114)

Building on `matVecInnerFold_simOracle` (which shows the inner `y`-cube `foldlM` simulates, under the
honest single-family oracle, to a pure `foldl` whose matrix factor is the genuine boolean matrix
entry `M x y`), this module collapses that pure `foldl` into the actual matrix-vector product entry
`(M *ᵥ 𝕫)(x)`, where `𝕫 = R1CS.𝕫 𝕩 (oos (.inr 0))` is the public-input/witness concatenation.

The collapse has two ingredients:
* the witness/public split of `R1CS.𝕫` is matched index-by-index — on the public block via the
  `Fin.append`/`Fin.addCases` left case, and on the witness block via the multilinear-extension
  boolean collapse (`MvPolynomial.MLE_eval_zeroOne`);
* the resulting `foldl` of partial sums is reassembled into a `Finset.sum`, which is exactly
  `dotProduct (M x) 𝕫 = (M *ᵥ 𝕫)(x)`.

This is the inner-fold step of the full `zeroCheckEvalFromOracles` faithfulness.
-/

open OracleComp OracleSpec OracleInterface MvPolynomial

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`. -/
private theorem foldl_add_eq_sum {S : Type} [AddCommMonoid S] {β : Type} (g : β → S) :
    ∀ (l : List β) (acc : S),
      l.foldl (fun a y => a + g y) acc = acc + (l.map g).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons y ys ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]; abel

/-- **First-phase inner fold reconstructs the matrix-vector product.** The honest simulation of the
inner `y`-cube fold equals the `(M *ᵥ 𝕫)(x)` entry. -/
theorem matVecRowSum_simOracle
    (oos : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (𝕩 : Statement.AfterFirstMessage R pp) (idx : R1CS.MatrixIdx) (xEnum : Fin (2 ^ pp.ℓ_m)) :
    simulateQ (simOracle oSpec oos)
        ((Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldlM
          (fun (a : R) (yEnum : Fin (2 ^ pp.ℓ_n)) => do
            let term ← matVecSummandFromOracles R pp oSpec 𝕩 idx (boolPoint R xEnum) yEnum
            pure (a + term)) (0 : R))
      = pure ((Matrix.mulVec (oos (.inl idx)) (R1CS.𝕫 𝕩 (oos (.inr 0)))) xEnum) := by
  classical
  rw [matVecInnerFold_simOracle]
  congr 1
  have hz : ∀ yEnum : Fin (2 ^ pp.ℓ_n),
      (oos (.inl idx)) xEnum yEnum
        * (if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then 𝕩 ⟨(yEnum : ℕ), hy⟩
           else eval (boolPoint R (⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x, by
             have hlt := yEnum.isLt
             have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
             have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
             omega⟩ : Fin (2 ^ pp.ℓ_w)))
             (MLE ((oos (.inr 0)) ∘ finFunctionFinEquiv)))
        = (oos (.inl idx)) xEnum yEnum * R1CS.𝕫 𝕩 (oos (.inr 0)) yEnum := by
    intro yEnum
    congr 1
    unfold R1CS.𝕫
    by_cases hy : (yEnum : ℕ) < 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w
    · simp [hy, PublicParams.toSizeR1CS, R1CS.Size.n_x, Fin.append, Fin.addCases]
      congr 1
    · let e : Fin (2 ^ pp.ℓ_w) := ⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x, by
        have hlt := yEnum.isLt
        have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
        have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
        omega⟩
      have hcollapse :
          eval (boolPoint R e) (MLE ((oos (.inr 0)) ∘ finFunctionFinEquiv)) = (oos (.inr 0)) e := by
        simpa [boolPoint, Function.comp_apply] using
          (MvPolynomial.MLE_eval_zeroOne (R := R) (σ := Fin pp.ℓ_w)
            (x := finFunctionFinEquiv.symm e) (evals := (oos (.inr 0)) ∘ finFunctionFinEquiv))
      rw [dif_neg (show ¬((yEnum : ℕ) < pp.toSizeR1CS.n_x) from hy), hcollapse]
      simp [hy, PublicParams.toSizeR1CS, R1CS.Size.n_x, Fin.append, Fin.addCases, Fin.subNat, e]
  simp only [hz]
  have hsum : (Matrix.mulVec (oos (.inl idx)) (R1CS.𝕫 𝕩 (oos (.inr 0)))) xEnum
      = ((Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.map
          (fun y => (oos (.inl idx)) xEnum y * R1CS.𝕫 𝕩 (oos (.inr 0)) y)).sum := by
    rw [show (Matrix.mulVec (oos (.inl idx)) (R1CS.𝕫 𝕩 (oos (.inr 0)))) xEnum
          = ∑ y, (oos (.inl idx)) xEnum y * R1CS.𝕫 𝕩 (oos (.inr 0)) y from rfl]
    exact (Finset.sum_map_toList Finset.univ
      (fun y => (oos (.inl idx)) xEnum y * R1CS.𝕫 𝕩 (oos (.inr 0)) y)).symm
  rw [hsum]
  exact (foldl_add_eq_sum (fun y => (oos (.inl idx)) xEnum y * R1CS.𝕫 𝕩 (oos (.inr 0)) y)
    Finset.univ.toList 0).trans (zero_add _)

end Spartan.Spec
