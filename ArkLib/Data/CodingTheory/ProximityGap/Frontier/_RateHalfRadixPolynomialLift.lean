/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TowerDescentNoSaving

/-!
# The polynomial radix lift used by the rate-half three-core construction

For `m > 0`, the map

```text
(Q_b)_(b<m) |-> sum_(b<m) X^b Q_b(X^m)
```

sends degree-`<32` slices to a polynomial of degree `<32m`.  Evaluation is
the expected tensor formula `sum_b x^b Q_b(x^m)`.  These elementary facts are
the algebraic engine of the 64-to-`2^30` core lift.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped Polynomial BigOperators

namespace ArkLib.ProximityGap.Frontier.RateHalfRadixPolynomialLift

variable {F : Type} [Field F]

/-- Assemble `m` base polynomials into one radix-`m` polynomial. -/
noncomputable def radixLift (m : Nat) (Q : Fin m -> F[X]) : F[X] :=
  ∑ b : Fin m, X ^ (b : Nat) * (Q b).comp (X ^ m)

/-- Evaluation of the radix lift is the tensor/Vandermonde formula. -/
theorem eval_radixLift (m : Nat) (Q : Fin m -> F[X]) (x : F) :
    (radixLift m Q).eval x = ∑ b : Fin m, x ^ (b : Nat) * (Q b).eval (x ^ m) := by
  rw [radixLift, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eval_mul, eval_pow, eval_X, eval_comp]

/-- Degree-`<32` slices assemble to degree `<32m`. -/
theorem natDegree_radixLift_lt (m : Nat) (hm : 0 < m) (Q : Fin m -> F[X])
    (hQ : forall b, (Q b).natDegree < 32) :
    (radixLift m Q).natDegree < 32 * m := by
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le
      (s := Finset.univ) (f := fun b : Fin m => X ^ (b : Nat) * (Q b).comp (X ^ m))
      (n := 32 * m - 1) ?_)
  · omega
  · intro b _
    have hb : (b : Nat) < m := b.isLt
    have hQb := hQ b
    have hQle : (Q b).natDegree ≤ 31 := by omega
    have hcomp : ((Q b).comp (X ^ m)).natDegree ≤ (Q b).natDegree * m := by
      calc
        ((Q b).comp (X ^ m)).natDegree
            ≤ (Q b).natDegree * (X ^ m : F[X]).natDegree :=
          Polynomial.natDegree_comp_le
        _ = (Q b).natDegree * m := by rw [Polynomial.natDegree_X_pow]
    have hterm :
        (X ^ (b : Nat) * (Q b).comp (X ^ m)).natDegree
          ≤ (b : Nat) + (Q b).natDegree * m := by
      calc
        (X ^ (b : Nat) * (Q b).comp (X ^ m)).natDegree
            ≤ (X ^ (b : Nat) : F[X]).natDegree +
                ((Q b).comp (X ^ m)).natDegree := Polynomial.natDegree_mul_le
        _ ≤ (b : Nat) + (Q b).natDegree * m := by
          rw [Polynomial.natDegree_X_pow]
          exact Nat.add_le_add_left hcomp _
    have hmul : (Q b).natDegree * m ≤ 31 * m :=
      Nat.mul_le_mul_right m hQle
    calc
      (X ^ (b : Nat) * (Q b).comp (X ^ m)).natDegree
          ≤ (b : Nat) + (Q b).natDegree * m := hterm
      _ ≤ (m - 1) + 31 * m :=
        Nat.add_le_add (Nat.le_pred_of_lt hb) hmul
      _ = 32 * m - 1 := by omega

/-- The radix lift is additive in its slices. -/
theorem radixLift_add (m : Nat) (Q R : Fin m -> F[X]) :
    radixLift m (fun b => Q b + R b) = radixLift m Q + radixLift m R := by
  simp only [radixLift, Polynomial.add_comp, mul_add, Finset.sum_add_distrib]

/-- Scalar multiplication commutes with the radix lift. -/
theorem radixLift_smul (m : Nat) (gamma : F) (Q : Fin m -> F[X]) :
    radixLift m (fun b => C gamma * Q b) = C gamma * radixLift m Q := by
  simp only [radixLift, Polynomial.mul_comp, Polynomial.C_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end ArkLib.ProximityGap.Frontier.RateHalfRadixPolynomialLift

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateHalfRadixPolynomialLift
#print axioms eval_radixLift
#print axioms natDegree_radixLift_lt
#print axioms radixLift_add
#print axioms radixLift_smul
