/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckMulVec

/-!
# Zero-check evaluation reconstruction is faithful (issue #114)

`zeroCheckEval_simOracle`: the verifier-side oracle reconstruction of the Spartan first sum-check's
zero-check polynomial value, `zeroCheckEvalFromOracles`, simulates — under the honest single-family
oracle — to the genuine evaluation `eval pt (zeroCheckVirtualPolynomial 𝕩 oos)` of the virtual
zero-check polynomial `𝒢`.

This is the keystone faithfulness statement for the `firstChallenge` virtual-oracle routing: it
shows that reading `𝒢.eval pt` by reconstructing each `(M *ᵥ 𝕫)(x)` from the matrix/witness oracles
(an outer `x`-cube fold of inner `y`-cube folds) agrees exactly with evaluating the closed-form
`𝒢 = ∑_x eq(x) · C(A𝕫 x · B𝕫 x − C𝕫 x)`.

The proof composes:
* the outer-fold collapse `simulateQ_simOracle_foldlM` (each step is deterministic under the honest
  oracle);
* the inner-fold matrix-vector reconstruction `matVecRowSum_simOracle` (each `rowSum idx`
  simulates to `(M *ᵥ 𝕫)(x)`);
* the partial-sum `foldl`-to-`Finset.sum` reassembly and the ring-hom distribution of `eval` over
  the sum/product/`C` structure of `𝒢`.
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

/-- **Zero-check evaluation reconstruction is faithful.** The honest simulation of the verifier-side
reconstruction `zeroCheckEvalFromOracles` equals the genuine evaluation of the virtual zero-check
polynomial `𝒢 = zeroCheckVirtualPolynomial`. -/
theorem zeroCheckEval_simOracle
    (oos : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (𝕩 : Statement.AfterFirstMessage R pp) (pt : Fin pp.ℓ_m → R) :
    simulateQ (simOracle oSpec oos) (zeroCheckEvalFromOracles R pp oSpec 𝕩 pt)
      = pure (MvPolynomial.eval pt (zeroCheckVirtualPolynomial R pp 𝕩 oos)) := by
  classical
  unfold zeroCheckEvalFromOracles
  rw [simulateQ_simOracle_foldlM oos _
    (fun (acc : R) (xEnum : Fin (2 ^ pp.ℓ_m)) =>
      acc + MvPolynomial.eval pt (MvPolynomial.eqPolynomial (boolPoint R xEnum)) *
        ((Matrix.mulVec (oos (.inl .A)) (R1CS.𝕫 𝕩 (oos (.inr 0)))) xEnum *
         (Matrix.mulVec (oos (.inl .B)) (R1CS.𝕫 𝕩 (oos (.inr 0)))) xEnum -
         (Matrix.mulVec (oos (.inl .C)) (R1CS.𝕫 𝕩 (oos (.inr 0)))) xEnum))]
  · -- collapse the outer `foldl` to a `Finset.sum`, then match `eval pt 𝒢` term-by-term
    congr 1
    rw [foldl_add_eq_sum, zero_add, Finset.sum_map_toList]
    unfold zeroCheckVirtualPolynomial
    rw [map_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_mul, eval_C]
  · -- each outer step is deterministic: the three `rowSum`s reconstruct `(M *ᵥ 𝕫)(x)`
    intro acc xEnum
    simp only [simulateQ_bind, matVecRowSum_simOracle, pure_bind, simulateQ_pure]

end Spartan.Spec
