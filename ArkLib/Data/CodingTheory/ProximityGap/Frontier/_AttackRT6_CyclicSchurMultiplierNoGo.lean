/-
RT6 attack: Drinfeld-twist / quantum-group deformation of the dilation circulant.

CLAIM (machine): deform the dilation circulant T_b by a Drinfeld/Jimbo twist
(U_qbar(sl_2)); the spectral radius rho(qbar) is entire in qbar, rho(1)=M, and at a
special root of unity qbar_0 (quantum dim = n) the operator is a fusion-category object
whose Frobenius-Perron dimension bounds rho(1) <= C sqrt(n log(q/n)) via Verlinde.

WHY IT COLLAPSES: the Drinfeld twist of the GROUP ALGEBRA of a cyclic group Z_n is a
2-cocycle, but H^2(Z_n, C^*) = 0 (cyclic groups have trivial Schur multiplier). So every
twist is a COBOUNDARY = gauge transformation, implemented on matrices as conjugation
T |-> U * T * U^{-1} by an invertible U. Conjugation preserves the characteristic
polynomial, hence the eigenvalue multiset, hence the spectral radius. Therefore rho(qbar)
is CONSTANT = rho(1) = M for all qbar: the deformation transports zero information.
(Numerics: rho(qbar) - rho(1) ~ 1e-15 across a path of qbar.) The Verlinde/FPdim quantity
for Vec_Z_n is p-INDEPENDENT (FPdim = n trivial, or Plancherel sqrt(n) = 2nd moment = the
wall), so it can only reproduce the trivial bound n or the average sqrt(n), never the sup
sqrt(n log). Frobenius-Perron is moreover inapplicable: T_b has complex unit-modulus
entries e_p(b x), not non-negative integers.
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- The Drinfeld twist, after gauge-fixing the coboundary (valid since
`H^2(Z_n, C^*) = 0`), is conjugation by a unit `U`: the deformed operator
`U * T * U⁻¹` and the original `T` have the SAME characteristic polynomial. -/
theorem twist_preserves_charpoly
    (U : (Matrix n n R)ˣ) (T : Matrix n n R) :
    (U.val * T * U⁻¹.val).charpoly = T.charpoly :=
  charpoly_units_conj U T

/-- ANY functional `Φ` of the char poly -- in particular the spectral radius
`M = ρ(1)` -- is EQUAL on `T` and its Drinfeld twist `U * T * U⁻¹`. Hence
`ρ(q̄) ≡ ρ(1) = M`: the deformation is the identity on the spectrum. -/
theorem twist_invariant_of_charpoly_functional
    {β : Type*} (Φ : Polynomial R → β)
    (U : (Matrix n n R)ˣ) (T : Matrix n n R) :
    Φ (U.val * T * U⁻¹.val).charpoly = Φ T.charpoly := by
  rw [twist_preserves_charpoly U T]

/-- Symmetric (other-side) form: same invariance, two-sided obstruction. -/
theorem twist_invariant_of_charpoly_functional'
    {β : Type*} (Φ : Polynomial R → β)
    (U : (Matrix n n R)ˣ) (T : Matrix n n R) :
    Φ (U⁻¹.val * T * U.val).charpoly = Φ T.charpoly := by
  rw [charpoly_units_conj' U T]

#print axioms twist_preserves_charpoly
#print axioms twist_invariant_of_charpoly_functional
#print axioms twist_invariant_of_charpoly_functional'
