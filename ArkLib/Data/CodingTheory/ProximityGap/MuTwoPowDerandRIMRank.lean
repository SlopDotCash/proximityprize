/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MuTwoPowDerandRefutation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Column-rank drop and kernel ↔ certificate bridge for the μ_{2^t} RIM counterexample

`MuTwoPowDerandRefutation` refutes the μ_{2^t} derandomization property at the certificate
level and exhibits the explicit reduced intersection matrix `rimMatrix` with vanishing
determinant (`rimMatrix_det_eq_zero`).  This file completes the matrix-level picture of
the refutation:

* `MuTwoPowDerandRefutation.rimMatrix_rank_lt_six` — the **column-rank drop**
  `rank (rimMatrix ω) < 6` whenever `ω⁴ = -1`; *full column rank* is precisely the form
  in which the AGL24/Guo–Zhang capacity machinery consumes the property.
* `MuTwoPowDerandRefutation.rimMatrix_mulVec_eq_certDiff` — the formal **kernel ↔
  certificate bridge**: row `r` of `rimMatrix ω *ᵥ rimKernelVec ω` *is* the certificate
  evaluation difference across the edge of `badHypergraph` at coordinate `coord r`.  This
  is an identity in `ω` (no hypothesis needed) and discharges the prose claim that
  `rimMatrix` is the RIM of `badHypergraph` and `rimKernelVec` encodes the certificate.
* `MuTwoPowDerandRefutation.rimKernelVec_poly₀` / `rimKernelVec_poly₁` — the two column
  blocks of the kernel vector are exactly the coefficient vectors of `p₀` and `p₁`.
* `MuTwoPowDerandRefutation.badHypergraph_coord_eq` — the six rows exhaust exactly the
  nonempty edges of `badHypergraph`.
* `MuTwoPowDerandRefutation.badHypergraph_weight_tight` — the k-wpc weight is *tight*
  (`Σᵢ (|Eᵢ| - 1) = 6 = k(s-1)`): even minimal 3-wpc hypergraphs fail.
* `MuTwoPowDerandRefutation.rimMatrix_rank_drop` — the packaged matrix-level refutation:
  a 3-wpc hypergraph whose RIM at the geometric point is singular and
  column-rank-deficient.
* Fully numeric `F₁₇` instantiations (`ω = 9`, of order 8) matching the mod-`p` run of
  `research/proximity-prize/conj3-proof/pmpair_counterexample.py`: the numeral matrix
  `rimMatrix_zmod17_eq`, the kernel certificate `(5, 0, 14, 1, 0, 1)`
  (`rimKernelVec_zmod17_eq`), and the rank drop `rimMatrix_rank_lt_six_zmod17`. -/

namespace MuTwoPowDerandRefutation

open Polynomial Finset

variable {F : Type*} [Field F] (ω : F)

/-! ## Row ↔ edge correspondence -/

/-- The coordinate (in `Fin 8`) of the edge represented by each row of `rimMatrix`. -/
def coord : Fin 6 → Fin 8 := ![0, 1, 2, 4, 5, 6]

/-- The first vertex of the edge represented by each row of `rimMatrix`. -/
def edgeFst : Fin 6 → Fin 3 := ![0, 0, 1, 0, 0, 1]

/-- The second vertex of the edge represented by each row of `rimMatrix`. -/
def edgeSnd : Fin 6 → Fin 3 := ![1, 2, 2, 1, 2, 2]

/-- The rows of `rimMatrix` exhaust exactly the nonempty edges of `badHypergraph`. -/
theorem badHypergraph_coord_eq : ∀ r : Fin 6,
    badHypergraph (coord r) = {edgeFst r, edgeSnd r} := by decide

theorem edgeFst_mem : ∀ r : Fin 6, edgeFst r ∈ badHypergraph (coord r) := by decide

theorem edgeSnd_mem : ∀ r : Fin 6, edgeSnd r ∈ badHypergraph (coord r) := by decide

/-- The k-wpc weight of `badHypergraph` is *tight*: under the discrete (identity)
labeling the weight is `Σᵢ (|Eᵢ| - 1) = 6 = k(s - 1)` with `k = 3`, `s = 3` — even
minimal 3-wpc hypergraphs fail the derandomization property. -/
theorem badHypergraph_weight_tight : labelWeight badHypergraph id = 6 := by decide

/-! ## Kernel vector ↔ certificate coefficients -/

/-- The first block of `rimKernelVec` is the coefficient vector of the certificate
polynomial `p₀ = (1 + ω²)·(X² - ω²)`. -/
theorem rimKernelVec_poly₀ :
    C (rimKernelVec ω 0) + C (rimKernelVec ω 1) * X + C (rimKernelVec ω 2) * X ^ 2 =
      p₀ ω := by
  simp only [rimKernelVec, p₀, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_mul, map_add, map_neg,
    map_one, map_pow, map_zero]
  ring

/-- The second block of `rimKernelVec` is the coefficient vector of the certificate
polynomial `p₁ = X² + 1`. -/
theorem rimKernelVec_poly₁ :
    C (rimKernelVec ω 3) + C (rimKernelVec ω 4) * X + C (rimKernelVec ω 5) * X ^ 2 =
      (p₁ : F[X]) := by
  simp [rimKernelVec, p₁]
  ring

/-- **Kernel ↔ certificate bridge.**  Row `r` of `rimMatrix ω` dotted with
`rimKernelVec ω` computes exactly the difference of certificate evaluations across the
edge represented by that row, at the geometric point `ω^(coord r)`.  This is an identity
in `ω` (no hypothesis on `ω` is needed): it states that `rimMatrix` *is* the reduced
intersection matrix of `badHypergraph` and `rimKernelVec` *is* the coefficient encoding
of the certificate `cert`. -/
theorem rimMatrix_mulVec_eq_certDiff (r : Fin 6) :
    (rimMatrix ω).mulVec (rimKernelVec ω) r =
      ((cert ω) (edgeFst r)).eval (ω ^ ((coord r : Fin 8) : ℕ)) -
        ((cert ω) (edgeSnd r)).eval (ω ^ ((coord r : Fin 8) : ℕ)) := by
  fin_cases r <;>
    simp [rimMatrix, rimKernelVec, cert, p₀, p₁, coord, edgeFst, edgeSnd,
      Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;>
    ring

/-! ## The column-rank drop -/

/-- **Column-rank drop.**  The RIM of the ±-pair hypergraph at the geometric point has
column rank `< 6` whenever `ω⁴ = -1` — full column rank is precisely the property
consumed by the AGL24/GZ capacity machinery. -/
theorem rimMatrix_rank_lt_six (hω : ω ^ 4 = -1) : (rimMatrix ω).rank < 6 := by
  have hker : rimKernelVec ω ∈ LinearMap.ker (rimMatrix ω).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact rimMatrix_mulVec_eq_zero ω hω
  have hpos : 0 < Module.finrank F (LinearMap.ker (rimMatrix ω).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨rimKernelVec ω, hker⟩, by
        simpa [Submodule.mk_eq_zero] using rimKernelVec_ne_zero ω⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker (rimMatrix ω).mulVecLin
  rw [Module.finrank_fin_fun] at hsum
  have hrank : (rimMatrix ω).rank = Module.finrank F (LinearMap.range
    (rimMatrix ω).mulVecLin) := rfl
  rw [hrank]
  omega

/-- **The packaged matrix-level refutation**: there is a 3-weakly-partition-connected
agreement hypergraph on the 8 geometric coordinates `ω⁰, …, ω⁷` whose reduced
intersection matrix at the geometric point is singular and column-rank-deficient.  The
universal μ_{2^t} RIM full-rank derandomization target is therefore false over every
field with an element `ω` satisfying `ω⁴ = -1` (e.g. any `ω` of order 8). -/
theorem rimMatrix_rank_drop (hω : ω ^ 4 = -1) :
    IsWeaklyPartitionConnected badHypergraph 3 ∧
      (rimMatrix ω).det = 0 ∧ (rimMatrix ω).rank < 6 :=
  ⟨badHypergraph_kwpc, rimMatrix_det_eq_zero ω hω, rimMatrix_rank_lt_six ω hω⟩

/-! ## Concrete first certificate over `F₁₇`

`ω = 9` has order 8 in `ZMod 17` (`9⁴ = 6561 ≡ -1`), matching the mod-`p` run of
`pmpair_counterexample.py`: rank 5 < 6 with kernel certificate `(5, 0, 14, 1, 0, 1)`. -/

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The fully numeric RIM over `F₁₇` at `ω = 9`. -/
theorem rimMatrix_zmod17_eq :
    rimMatrix (9 : ZMod 17) =
      !![1, 1, 1, 16, 16, 16;
         1, 9, 13, 0, 0, 0;
         0, 0, 0, 1, 13, 16;
         1, 16, 1, 16, 1, 16;
         1, 8, 13, 0, 0, 0;
         0, 0, 0, 1, 4, 16] := by
  decide

/-- The fully numeric kernel certificate over `F₁₇`, as found by the mod-`p` search. -/
theorem rimKernelVec_zmod17_eq :
    rimKernelVec (9 : ZMod 17) = ![5, 0, 14, 1, 0, 1] := by
  decide

/-- `F₁₇` instantiation of the column-rank drop (`ω = 9`, an element of order 8). -/
theorem rimMatrix_rank_lt_six_zmod17 : (rimMatrix (9 : ZMod 17)).rank < 6 :=
  rimMatrix_rank_lt_six (9 : ZMod 17) (by decide)

end MuTwoPowDerandRefutation
