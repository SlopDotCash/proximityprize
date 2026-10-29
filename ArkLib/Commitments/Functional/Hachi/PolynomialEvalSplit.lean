/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.Commitments.Functional.Hachi.EvalSplit

/-!
# Compatibility and linearity for the former polynomial split module

`EvalSplit` owns the split implementation. The coefficient-linearity lemmas below are
retained downstream additions and reuse that implementation.
-/

open CompPoly
namespace ArkLib.Lattices.Hachi
variable {R : Type*} {nl nh : Nat} [CommSemiring R]
open CMlPolynomial

/-- Coefficientwise additivity of `CMlPolynomial` (the `+` is `Vector.zipWith (·+·)`). -/
private theorem coeff_add (p q : CMlPolynomial R (nl + nh)) (k : Fin (2 ^ (nl + nh))) :
    (p + q).get k = p.get k + q.get k := by
  change (Vector.zipWith (· + ·) p q).get k = p.get k + q.get k
  simp only [Vector.get_eq_getElem, Vector.getElem_zipWith]

/-- Coefficientwise scalar multiplication of `CMlPolynomial` (the `•` is `Vector.map (r * ·)`). -/
private theorem coeff_smul (r : R) (p : CMlPolynomial R (nl + nh)) (k : Fin (2 ^ (nl + nh))) :
    (r • p).get k = r * p.get k := by
  change (Vector.map (fun a => r * a) p).get k = r * p.get k
  simp only [Vector.get_eq_getElem, Vector.getElem_map]

/-- The reshape `toMatrix` is additive in the coefficient vector. -/
theorem toMatrix_add (p q : CMlPolynomial R (nl + nh)) :
    toMatrix (p + q) = toMatrix p + toMatrix q := by
  funext i j; simp only [toMatrix, Matrix.add_apply]; exact coeff_add p q _

/-- The reshape `toMatrix` pulls out a scalar from the coefficient vector. -/
theorem toMatrix_smul (r : R) (p : CMlPolynomial R (nl + nh)) :
    toMatrix (r • p) = r • toMatrix p := by
  funext i j; simp only [toMatrix, Matrix.smul_apply, smul_eq_mul]; exact coeff_smul r p _

/-- **Coefficient `R`-linearity (additive).** A corollary of `splitForm_matrix_add` and
`toMatrix_add`: useful for the random-linear-combination/batching steps. -/
theorem evalSplit_add (p q : CMlPolynomial R (nl + nh)) (xl : Vector R nl) (xh : Vector R nh) :
    evalSplit (p + q) xl xh = evalSplit p xl xh + evalSplit q xl xh := by
  simp only [evalSplit, toMatrix_add, splitForm_matrix_add]

/-- **Coefficient `R`-linearity (scalar).** A corollary of `splitForm_matrix_smul` and
`toMatrix_smul`. -/
theorem evalSplit_smul (r : R) (p : CMlPolynomial R (nl + nh)) (xl : Vector R nl)
    (xh : Vector R nh) : evalSplit (r • p) xl xh = r * evalSplit p xl xh := by
  simp only [evalSplit, toMatrix_smul, splitForm_matrix_smul]


end ArkLib.Lattices.Hachi
