/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Nonsingular square submatrices of full-column-rank matrices (issue #346, brick 15)

The generic linear algebra behind Line 13 of [AGL24]'s `GetMatrixSequence` ("the
lexicographically smallest nonsingular `(t−1)k × (t−1)k` submatrix"): a matrix with trivial
`mulVec` kernel (full column rank) over a field admits an injective row selection whose
square submatrix has nonzero determinant.

* `rows_span_top_of_mulVec_injective` — trivial kernel ⟹ the rows span the full space
  (dual separation through the `Pi.basisFun` self-duality);
* `exists_square_submatrix_det_ne_zero` — **the extraction**: a row-subset of size `|C|`
  forming a basis of the row space gives a square submatrix with independent rows, hence a
  unit, hence nonzero determinant.

(Also a Mathlib-gap candidate — the statement is fully generic.)
-/

open Finset

namespace AGL24

variable {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq R] [Field K]

/-- Trivial `mulVec` kernel forces the rows to span the whole space: a vector orthogonal to
every row would be a nonzero kernel element. -/
theorem rows_span_top_of_mulVec_injective (M : Matrix R C K)
    (h : ∀ v : C → K, M.mulVec v = 0 → v = 0) :
    Submodule.span K (Set.range (fun r => M r)) = ⊤ := by
  by_contra hne
  -- A proper subspace admits a nonzero annihilating functional; functionals on C → K are
  -- dot products.
  obtain ⟨φ, hφne, hφvan⟩ : ∃ φ : (C → K) →ₗ[K] K, φ ≠ 0 ∧
      ∀ x ∈ Submodule.span K (Set.range (fun r => M r)), φ x = 0 := by
    have hlt : Submodule.span K (Set.range (fun r => M r)) < ⊤ :=
      lt_of_le_of_ne le_top hne
    obtain ⟨x, hx⟩ := SetLike.exists_of_lt hlt
    -- The quotient by the span is nontrivial; compose a nonzero functional on it.
    set Q := (C → K) ⧸ Submodule.span K (Set.range (fun r => M r)) with hQ
    have hxQ : (Submodule.Quotient.mk x : Q) ≠ 0 := by
      intro hzero
      exact hx.2 ((Submodule.Quotient.mk_eq_zero _).mp hzero)
    obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero K hxQ
    refine ⟨ψ.comp (Submodule.mkQ _), ?_, ?_⟩
    · intro hzero
      apply hψ
      have := congrFun (congrArg (fun f => f.toFun) hzero) x
      exact this
    · intro y hy
      show ψ (Submodule.Quotient.mk y) = 0
      rw [show (Submodule.Quotient.mk y : Q) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hy]
      exact map_zero ψ
  -- The functional is a dot product with v := φ ∘ basis.
  set v : C → K := fun c => φ (Pi.single c 1) with hv
  have hφdot : ∀ x : C → K, φ x = ∑ c, x c * v c := by
    intro x
    have hx_expand : x = ∑ c, x c • (Pi.single c 1 : C → K) := by
      funext c'
      rw [Finset.sum_apply]
      simp [Pi.single_apply, eq_comm]
    conv_lhs => rw [hx_expand]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [map_smul, smul_eq_mul, hv]
  -- v is a nonzero kernel element: contradiction.
  have hvker : M.mulVec v = 0 := by
    funext r
    show (fun c => M r c) ⬝ᵥ v = 0
    have := hφvan (M r) (Submodule.subset_span ⟨r, rfl⟩)
    rw [hφdot (M r)] at this
    exact this
  have hvne : v ≠ 0 := by
    intro hzero
    apply hφne
    apply LinearMap.ext
    intro y
    rw [hφdot y, hzero]
    simp
  exact hvne (h v hvker)

/-- **The nonsingular-submatrix extraction**: a matrix with trivial `mulVec` kernel over a
field admits an injective row selection whose square submatrix has nonzero determinant —
the generic fact behind [AGL24] Algorithm 1's Line 13. -/
theorem exists_square_submatrix_det_ne_zero (M : Matrix R C K)
    (h : ∀ v : C → K, M.mulVec v = 0 → v = 0) :
    ∃ rows : C → R, Function.Injective rows ∧ (M.submatrix rows id).det ≠ 0 := by
  classical
  -- The rows span; extract an independent spanning subfamily (a basis inside the rows).
  have hspan := rows_span_top_of_mulVec_injective M h
  obtain ⟨s, hs_sub, hs_span, hs_indep⟩ :=
    exists_linearIndependent K (Set.range (fun r => M r))
  rw [hspan] at hs_span
  -- The basis structure on s.
  have hbasis : Submodule.span K s = ⊤ := hs_span
  set b : Module.Basis s K (C → K) := Module.Basis.mk hs_indep (by
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hbasis]) with hb
  -- |s| = |C|.
  haveI : Fintype s := Set.Finite.fintype (Set.Finite.subset (Set.finite_range _) hs_sub)
  have hcard : Fintype.card s = Fintype.card C := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_pi]
  -- Choose row preimages for the basis elements (injective: distinct vectors).
  have hpre : ∀ x : s, ∃ r : R, M r = x.val := fun x => hs_sub x.property
  choose pre hpre_eq using hpre
  have hpre_inj : Function.Injective pre := by
    intro x x' hxx'
    apply Subtype.ext
    rw [← hpre_eq x, ← hpre_eq x', hxx']
  -- Reindex s by C.
  obtain ⟨e⟩ : Nonempty (C ≃ s) := by
    rw [← Fintype.card_eq]
    exact hcard.symm
  refine ⟨fun c => pre (e c), hpre_inj.comp e.injective, ?_⟩
  -- The square submatrix's rows are the basis vectors: independent ⟹ unit ⟹ det ≠ 0.
  have hrows_indep : LinearIndependent K
      (fun c => (M.submatrix (fun c => pre (e c)) id) c) := by
    have heq : (fun c => (M.submatrix (fun c => pre (e c)) id) c)
        = (fun c => ((e c : s) : C → K)) := by
      funext c
      show M (pre (e c)) = (e c).val
      exact hpre_eq (e c)
    rw [heq]
    exact hs_indep.comp (fun c => e c) e.injective
  have hunit : IsUnit (M.submatrix (fun c => pre (e c)) id) :=
    (Matrix.linearIndependent_rows_iff_isUnit).mp hrows_indep
  have hdet : IsUnit (M.submatrix (fun c => pre (e c)) id).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  exact hdet.ne_zero

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.rows_span_top_of_mulVec_injective
#print axioms AGL24.exists_square_submatrix_det_ne_zero
