/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Tensor-row span criterion for block-Vandermonde maximal recoverability

After gauging two labels, a support-divided-difference row is a local label-parity functional
`ell : D → F` tensored with a Vandermonde row `v x : K → F`.  Full rank is exactly the statement
that these tensor rows span the full dual coefficient space on `D × K`.

This criterion respects dense Vandermonde blocks.  It is deliberately stated as a sufficient
maximal-recoverability hypothesis; Hall dimension budgets alone are not asserted to imply it.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.TensorRowSpanCriterion

variable {F X D K : Type} [Field F] [Fintype D] [Fintype K]
  [DecidableEq D] [DecidableEq K]

/-- A local label functional tensored with one Vandermonde evaluation row. -/
def tensorRow (ell : D → F) (v : K → F) : D × K → F :=
  fun dk => ell dk.1 * v dk.2

/-- All tensor rows supplied by the coordinate-indexed local parity subspaces. -/
def tensorRowSet (parity : X → Submodule F (D → F)) (v : X → K → F) :
    Set (D × K → F) :=
  {w | ∃ x ell, ell ∈ parity x ∧ w = tensorRow ell (v x)}

/-- The measurement pairing of a tensor row with a coefficient array. -/
def tensorMeasurement (ell : D → F) (v : K → F) (q : D × K → F) : F :=
  ∑ dk, tensorRow ell v dk * q dk

/-- **Block maximal-recoverability consumer.**  If the local-parity/Vandermonde tensor rows span
the entire coefficient dual, then vanishing of all corresponding measurements forces every
coefficient to vanish. -/
theorem eq_zero_of_tensorRowSpan_eq_top
    (parity : X → Submodule F (D → F)) (v : X → K → F)
    (hspan : Submodule.span F (tensorRowSet parity v) = ⊤)
    (q : D × K → F)
    (hzero : ∀ x ell, ell ∈ parity x → tensorMeasurement ell (v x) q = 0) :
    q = 0 := by
  let pairing : (D × K → F) →ₗ[F] F := (dotProductBilin F F) q
  have hsetKer : tensorRowSet parity v ⊆ LinearMap.ker pairing := by
    intro w hw
    obtain ⟨x, ell, hell, rfl⟩ := hw
    change pairing (tensorRow ell (v x)) = 0
    simpa [pairing, tensorMeasurement, dotProduct, mul_comm] using hzero x ell hell
  have htopKer : (⊤ : Submodule F (D × K → F)) ≤ LinearMap.ker pairing := by
    rw [← hspan]
    exact Submodule.span_le.mpr hsetKer
  funext dk
  let basisVec : D × K → F := Pi.single dk 1
  have hbasis : basisVec ∈ LinearMap.ker pairing := htopKer (by simp)
  have hz := LinearMap.mem_ker.mp hbasis
  simpa [pairing, basisVec, dotProduct, Pi.single_apply, mul_comm] using hz

/-- Injectivity form for two coefficient arrays with identical tensor measurements. -/
theorem eq_of_tensorMeasurements_eq_of_span_eq_top
    (parity : X → Submodule F (D → F)) (v : X → K → F)
    (hspan : Submodule.span F (tensorRowSet parity v) = ⊤)
    (q r : D × K → F)
    (heq : ∀ x ell, ell ∈ parity x →
      tensorMeasurement ell (v x) q = tensorMeasurement ell (v x) r) :
    q = r := by
  rw [← sub_eq_zero]
  apply eq_zero_of_tensorRowSpan_eq_top parity v hspan (q - r)
  intro x ell hell
  simp only [tensorMeasurement, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (heq x ell hell)

end ArkLib.ProximityGap.Frontier.TensorRowSpanCriterion

#print axioms ArkLib.ProximityGap.Frontier.TensorRowSpanCriterion.eq_zero_of_tensorRowSpan_eq_top
#print axioms ArkLib.ProximityGap.Frontier.TensorRowSpanCriterion.eq_of_tensorMeasurements_eq_of_span_eq_top
