/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.MvPolynomial.SchwartzZippelExists
import ArkLib.Data.CodingTheory.AGL24NonzeroMinor

/-!
# Schwartz–Zippel specialization of a symbolic matrix minor (#389)

This file carries out the **Schwartz–Zippel step** of the Lovett ⟶ AGL24 GM-MDS bridge
(arXiv:1803.02523, p. 3): a symbolic (polynomial) `k × k` minor that is *not identically zero*
is specialized to **distinct field points** `φ : ι ↪ F` at which the *evaluated* minor is
nonzero, provided the field is large enough (`|F| > totalDegree + C(|ι|,2)`, the `n + k − 1`
regime).

The engine is `MvPolynomial.exists_embedding_eval_ne_zero_fintype` (the distinct-coordinate
existence form built in `ArkLib/ToMathlib/MvPolynomial/SchwartzZippelExists.lean`): apply it to
the determinant polynomial `det M`, which is nonzero by hypothesis.

## Main results

* `exists_embedding_det_eval_ne_zero`: given a square matrix `M` over `MvPolynomial ι F` with
  `(M.det) ≠ 0` and `|F|` large enough, there is an injection `φ : ι ↪ F` such that the
  entrywise-evaluated matrix `M.map (eval (φ ·))` has nonzero determinant — i.e. is nonsingular
  over `F`.
* `exists_embedding_RIM_minor_eval_ne_zero`: the AGL24-specific instantiation at a nonzero RIM
  submatrix minor (the output of `AGL24.exists_nonzero_poly_minor`): the same minor evaluated at
  distinct field points stays nonzero.

These are the concrete, fully-proven realizations of the bridge's "Schwartz–Zippel
specialization" move (paper p. 3); they are field-quantitative (`|F| > deg + C(|ι|,2)`) and
genuinely consume the symbolic non-vanishing, not vacuous.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F]

/-- **Schwartz–Zippel specialization of a nonzero symbolic determinant.**  Let `M` be a square
matrix (index type `n`) over `MvPolynomial ι F` whose determinant is a nonzero polynomial.  If
the field is large enough — `M.det.totalDegree + (|ι|)·(|ι|−1)/2 < |F|` — then there is an
injection `φ : ι ↪ F` (distinct evaluation points) at which the entrywise evaluation
`M.map (eval (φ ·))` has nonzero determinant.

This is the bridge's Schwartz–Zippel move: a nonzero symbolic minor stays nonzero at distinct
field points. -/
theorem exists_embedding_det_eval_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial ι F)) (hdet : M.det ≠ 0)
    (hcard : M.det.totalDegree + Fintype.card ι * (Fintype.card ι - 1) / 2
      < Fintype.card F) :
    ∃ φ : ι ↪ F, (M.map (MvPolynomial.eval (φ ·))).det ≠ 0 := by
  classical
  -- Apply the distinct-coordinate SZ existence form to the determinant polynomial.
  obtain ⟨φ, _hφS, hφ⟩ :=
    MvPolynomial.exists_embedding_eval_ne_zero_fintype (P := M.det) hdet
      (S := (Finset.univ : Finset F)) (by simpa [Finset.card_univ] using hcard)
  refine ⟨φ, ?_⟩
  -- `det (M.map (eval (φ·))) = eval (φ·) (det M)` since `eval (φ·)` is a ring hom.
  have hmap : (M.map (MvPolynomial.eval (φ ·))).det
      = (MvPolynomial.eval (φ ·)) M.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [hmap]
  exact hφ

/-- **Schwartz–Zippel specialization at an AGL24 RIM minor.**  Given a nonzero polynomial minor
of the reduced intersection matrix (the output of `AGL24.exists_nonzero_poly_minor`) and a large
enough field, there are distinct evaluation points `φ : ι ↪ F` keeping the evaluated minor
nonzero — a nonsingular evaluated submatrix realizing the zero pattern.

This is the concrete instantiation of the bridge's Schwartz–Zippel move on the very matrix the
AGL24 cone uses. -/
theorem exists_embedding_RIM_minor_eval_ne_zero {k t : ℕ}
    (e : ι → Finset (Fin (t + 1)))
    (rows : Fin t × Fin k → AGL24.RIMRowIdx e)
    (hdet : ((AGL24.RIM F e).submatrix rows id).det ≠ 0)
    (hcard : ((AGL24.RIM F e).submatrix rows id).det.totalDegree
        + Fintype.card ι * (Fintype.card ι - 1) / 2 < Fintype.card F) :
    ∃ φ : ι ↪ F,
      (((AGL24.RIM F e).submatrix rows id).map (MvPolynomial.eval (φ ·))).det ≠ 0 :=
  exists_embedding_det_eval_ne_zero _ hdet hcard

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.exists_embedding_det_eval_ne_zero
#print axioms ArkLib.GMMDS.exists_embedding_RIM_minor_eval_ne_zero
