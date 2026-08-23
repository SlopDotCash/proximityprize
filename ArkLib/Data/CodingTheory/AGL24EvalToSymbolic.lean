/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24SymbolicRank
import ArkLib.Data.CodingTheory.AGL24Submatrix

/-!
# [AGL24] Appendix A, the reduction step: evaluated ⟹ symbolic full rank
# (issue #346, brick 18)

The opening reduction of the paper's proof of Theorem 2.11: *it suffices to prove that
`RIM_H` has full column rank for some evaluation* — because a nonzero evaluated minor
determinant forces the corresponding polynomial minor determinant to be nonzero, and a
square symbolic matrix with nonzero determinant has trivial kernel over the (integral)
polynomial ring by Cramer.

* `symbolic_kernel_trivial_of_evaluated` — **the reduction**: one evaluation point with
  trivial evaluated kernel makes the polynomial kernel trivial (brick 15's submatrix
  extraction at the evaluated level + `RingHom.map_det` + the adjugate identity).

This refines the campaign's deep residual one final step: the Theorem 2.11 interface
(`SymbolicFullRankResidual`) now follows from an **evaluated witness** — exactly the object
the GM-MDS machinery of Theorem A.2/Corollary A.4 constructs. The remaining mathematics is
purely the witness construction.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- **The Appendix A reduction**: if some evaluation of the reduced intersection matrix has
trivial kernel over `F`, then the symbolic matrix has trivial kernel over the polynomial
ring. (A nonzero evaluated minor lifts to a nonzero polynomial minor; Cramer finishes.) -/
theorem symbolic_kernel_trivial_of_evaluated {t k : ℕ}
    (e : ι → Finset (Fin (t + 1))) (α : ι → F)
    (h : ∀ w : Fin t × Fin k → F,
      ((RIM F e).map (MvPolynomial.eval α)).mulVec w = 0 → w = 0)
    (v : Fin t × Fin k → MvPolynomial ι F)
    (hker : (RIM F e).mulVec v = 0) : v = 0 := by
  classical
  -- Brick 15 at the evaluated level: a nonsingular square submatrix.
  obtain ⟨rows, hrows_inj, hdet⟩ :=
    exists_square_submatrix_det_ne_zero ((RIM F e).map (MvPolynomial.eval α)) h
  -- The polynomial minor's determinant is nonzero (it evaluates to the nonzero one).
  have hdet_poly : ((RIM F e).submatrix rows id).det ≠ 0 := by
    intro hzero
    apply hdet
    have hmap : ((RIM F e).map (MvPolynomial.eval α)).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)
        = ((RIM F e).submatrix rows
            (id : Fin t × Fin k → Fin t × Fin k)).map (MvPolynomial.eval α) := rfl
    rw [hmap]
    rw [show (((RIM F e).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)).map (MvPolynomial.eval α)).det
        = MvPolynomial.eval α (((RIM F e).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)).det) from by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]]
    rw [hzero]
    exact map_zero _
  -- The kernel vector lies in the square minor's kernel.
  have hker_sq : ((RIM F e).submatrix rows id).mulVec v = 0 := by
    funext c
    have := congrFun hker (rows c)
    exact this
  -- Cramer: adjugate · (M · v) = det • v.
  have hcramer : ((RIM F e).submatrix rows id).det • v = 0 := by
    have hadj : (((RIM F e).submatrix rows id).adjugate
        * ((RIM F e).submatrix rows id)).mulVec v
        = ((RIM F e).submatrix rows id).adjugate.mulVec
            (((RIM F e).submatrix rows id).mulVec v) := by
      rw [Matrix.mulVec_mulVec]
    rw [Matrix.adjugate_mul] at hadj
    rw [hker_sq] at hadj
    rw [Matrix.mulVec_zero] at hadj
    rw [show (((RIM F e).submatrix rows id).det • (1 : Matrix (Fin t × Fin k)
        (Fin t × Fin k) (MvPolynomial ι F))).mulVec v
        = ((RIM F e).submatrix rows id).det • v from by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]] at hadj
    exact hadj
  -- An integral domain: det ≠ 0 kills the vector.
  funext c
  have := congrFun hcramer c
  rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rcases mul_eq_zero.mp this with hd | hv
  · exact absurd hd hdet_poly
  · exact hv

/-- **The residual refinement**: an evaluated full-rank witness for every weakly-partition-
connected hypergraph discharges the Theorem 2.11 interface. The witness is exactly what the
GM-MDS machinery (Theorem A.2 + Corollary A.4) constructs. -/
theorem symbolicFullRankResidual_of_evaluated_witness {k : ℕ}
    (hwitness : ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∃ α : ι → F, ∀ w : Fin t × Fin k → F,
        ((RIM F e).map (MvPolynomial.eval α)).mulVec w = 0 → w = 0) :
    SymbolicFullRankResidual (ι := ι) F k := by
  intro t ht e hwpc v hker
  obtain ⟨α, hα⟩ := hwitness ht e hwpc
  exact symbolic_kernel_trivial_of_evaluated e α hα v hker

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.symbolic_kernel_trivial_of_evaluated
#print axioms AGL24.symbolicFullRankResidual_of_evaluated_witness
