/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.LinearAlgebra.Lagrange

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# Reed–Solomon vanishing-set dimension (MDS weight-enumerator foundation)

For an RS code `RS[F, α, deg]` and a coordinate set `S` with `|S| ≤ deg`, the degree-`<deg`
polynomials vanishing on the points `{α i : i ∈ S}` form a subspace of dimension `deg - |S|`.
Equivalently the evaluation map `degreeLT F deg → (S → F)` is **surjective** (Lagrange
interpolation, since `|S| ≤ deg` distinct nodes), so by rank–nullity its kernel — the vanishing
polynomials — has dimension `deg - |S|`, hence `q^{deg - |S|}` codewords.

This is the MDS information-set fact: any `s ≤ deg` coordinates can be prescribed freely.  It is
the combinatorial foundation of the **MDS weight enumerator** `A_d` (inclusion–exclusion over the
support set), which in turn feeds the CS25 #82 second moment `E[N²] = |C| · ∑_d A_d · I(d)`.
-/

open Polynomial

namespace ArkLib.CS25

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]

/-- Evaluation of a degree-`<deg` polynomial at the points indexed by a coordinate set `S`. -/
noncomputable def evalOnS (α : ι ↪ F) (deg : ℕ) (S : Finset ι) :
    Polynomial.degreeLT F deg →ₗ[F] (S → F) where
  toFun p := fun i => (p : F[X]).eval (α (i : ι))
  map_add' p q := by ext i; simp [Submodule.coe_add, Polynomial.eval_add]
  map_smul' c p := by ext i; simp [Polynomial.eval_smul]

/-- **Lagrange surjectivity.** For `|S| ≤ deg`, every prescription of values on the points
`{α i : i ∈ S}` is realised by some degree-`<deg` polynomial. -/
theorem evalOnS_surjective (α : ι ↪ F) (deg : ℕ) (S : Finset ι) (hS : S.card ≤ deg) :
    Function.Surjective (evalOnS α deg S) := by
  classical
  intro v
  -- interpolate `v` over the distinct nodes `α i`, `i ∈ S`
  set r : ι → F := fun i => if h : i ∈ S then v ⟨i, h⟩ else 0 with hr
  have hinj : Set.InjOn (fun i => α i) (S : Set ι) := α.injective.injOn
  set p : F[X] := Lagrange.interpolate S (fun i => α i) r with hp
  have hdeg : p.degree < (deg : WithBot ℕ) := by
    calc p.degree < (S.card : WithBot ℕ) := Lagrange.degree_interpolate_lt r hinj
      _ ≤ (deg : WithBot ℕ) := by exact_mod_cast hS
  refine ⟨⟨p, Polynomial.mem_degreeLT.mpr hdeg⟩, ?_⟩
  ext i
  change (p : F[X]).eval (α (i : ι)) = v i
  rw [hp, Lagrange.eval_interpolate_at_node r hinj i.2]
  simp [hr, i.2]

/-- **Vanishing-subspace dimension.** The degree-`<deg` polynomials vanishing on `S` (with
`|S| ≤ deg`) form a subspace of dimension `deg - |S|`. -/
theorem finrank_ker_evalOnS (α : ι ↪ F) (deg : ℕ) (S : Finset ι) (hS : S.card ≤ deg) :
    Module.finrank F (LinearMap.ker (evalOnS α deg S)) = deg - S.card := by
  classical
  have hsurj := evalOnS_surjective α deg S hS
  have hrank : Module.finrank F (LinearMap.range (evalOnS α deg S)) = S.card := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi, Fintype.card_coe]
  have hdom : Module.finrank F (Polynomial.degreeLT F deg) = deg :=
    Polynomial.finrank_degreeLT_n deg
  haveI : FiniteDimensional F (Polynomial.degreeLT F deg) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F deg).toLinearMap
      (Polynomial.degreeLTEquiv F deg).injective
  have hrn := LinearMap.finrank_range_add_finrank_ker (evalOnS α deg S)
  rw [hrank, hdom] at hrn
  omega

end ArkLib.CS25
