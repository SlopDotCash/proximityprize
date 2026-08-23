/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HasseWronskianPoly
import ArkLib.Data.CodingTheory.ProximityGap.WronskianGeneral

/-!
# The hard direction of the general Wronskian criterion: distinct degrees ⟹ nonzero (#389)

`WronskianGeneral.lean` builds the ordinary-derivative Stepanov Wronskian `wronskianDet P =
det[derivative^[a] (P j)]` and the *easy* direction `wronskianDet P ≠ 0 ⟹ LinearIndependent P`.
The Stepanov argument needs the **converse** — a certificate that the auxiliary (itself a Wronskian)
is *nonzero* — which is `LinearIndependent P ⟹ wronskianDet P ≠ 0`.

This file supplies that converse for **distinct-degree** families (the case that matters after the
degree-echelon recombination `GK16Finish.exists_distinctDegree_recombination`). The bridge is
`derivative^[a] = a! · hasseDeriv a` (`Polynomial.factorial_smul_hasseDeriv`), so
`wronskianDet P = (∏ₐ a!) · det[hasseDeriv a (P j)]`; the Hasse determinant is nonzero by
`hasseWronskian_distinctDeg_ne_zero` (distinct degrees) and `∏ₐ a! ≠ 0` in characteristic `0` or
`> l−1`. The Hasse form is the characteristic-`p`-correct one (ordinary `derivative^[a]` vanishes for
`a ≥ p`); the `∏a! ≠ 0` hypothesis is exactly the regime where the two agree.

This is the classical-Wronskian analogue of `GK16.foldedWronskian_ne_zero_of_linearIndependent`, now
plugging into the in-tree ordinary-derivative Stepanov framework. Axiom-clean.
-/

open Matrix Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- Bridge: the ordinary iterated derivative is the factorial multiple of the Hasse derivative. -/
lemma iterate_derivative_eq_factorial_mul_hasseDeriv (a : ℕ) (p : F[X]) :
    (Polynomial.derivative^[a]) p = ((a.factorial : F[X])) * hasseDeriv a p := by
  rw [← Polynomial.factorial_smul_hasseDeriv (k := a), LinearMap.smul_apply, nsmul_eq_mul]

/-- **The hard direction of the general (ordinary-derivative) Wronskian criterion, for
distinct-degree families.** If `F` has characteristic `0` or `> l−1` (every `a! ≠ 0` for `a < l`),
the polynomials `P` are nonzero, and their degrees are distinct in `F`, then the Stepanov Wronskian
`wronskianDet P ≠ 0`. This is the converse missing from `WronskianGeneral` (which only proves
`wronskianDet ≠ 0 ⟹ independent`); it is what certifies the Stepanov auxiliary nonzero. -/
theorem wronskianDet_ne_zero_of_distinctDeg {l : ℕ} (P : Fin l → F[X])
    (hchar : ∀ a : Fin l, ((a : ℕ).factorial : F) ≠ 0)
    (hP : ∀ j, P j ≠ 0)
    (hinj : Function.Injective (fun j => ((P j).natDegree : F))) :
    ArkLib.ProximityGap.Wronskian.wronskianDet P ≠ 0 := by
  have hdet_eq : ArkLib.ProximityGap.Wronskian.wronskianDet P
      = (∏ a : Fin l, ((a : ℕ).factorial : F[X]))
          * (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) (P j))).det := by
    rw [ArkLib.ProximityGap.Wronskian.wronskianDet]
    rw [show ArkLib.ProximityGap.Wronskian.wronskianMatrix P
        = Matrix.of (fun a j : Fin l => ((a : ℕ).factorial : F[X])
            * (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) (P j))) a j) from by
      refine Matrix.ext (fun a j => ?_)
      rw [ArkLib.ProximityGap.Wronskian.wronskianMatrix_apply]
      simp only [Matrix.of_apply]
      exact iterate_derivative_eq_factorial_mul_hasseDeriv (a : ℕ) (P j)]
    rw [Matrix.det_mul_column]
  rw [hdet_eq]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro a _
    rw [show ((a : ℕ).factorial : F[X]) = Polynomial.C ((a : ℕ).factorial : F) by
      rw [Polynomial.C_eq_natCast]]
    rw [Ne, Polynomial.C_eq_zero]
    exact hchar a
  · exact hasseWronskian_distinctDeg_ne_zero P hP hinj

end ProximityGap.BinomialDet


-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.wronskianDet_ne_zero_of_distinctDeg
