/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Data.CodingTheory.AGL24Submatrix
import Mathlib.RingTheory.Localization.FractionRing

/-! # Dimension of the production jet space over the scalar function field -/

set_option autoImplicit false
open Polynomial Finset Matrix
namespace ArkLib.ProximityGap.Frontier.HalfSuccessorJetRank
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- A finite-dimensional subspace of functions is determined by a set of coordinates
whose size is its dimension. -/
theorem separating_coordinates {K J : Type*} [Field K] [Fintype J] (W : Submodule K (J → K)) :
    ∃ rows : Fin (Module.finrank K W) → J,
      Function.Injective (fun w : W => fun i => w.val (rows i)) := by
  classical
  let e := (Module.finBasis K W).equivFun
  let P := W.subtype.comp e.symm.toLinearMap
  let M := LinearMap.toMatrix' P
  have hM (v) : M *ᵥ v = P v := LinearMap.toMatrix'_mulVec _ _
  have hi : Function.Injective P := Subtype.val_injective.comp e.symm.injective
  obtain ⟨rows,_,hd⟩ := AGL24.exists_square_submatrix_det_ne_zero M (fun v hv =>
    hi ((hM v).symm.trans (hv.trans P.map_zero.symm)))
  have hminor : IsUnit (M.submatrix rows id) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  refine ⟨rows,fun a b hab => e.injective (Matrix.mulVec_injective_of_isUnit hminor ?_)⟩
  funext i
  change (M *ᵥ e a) (rows i) = (M *ᵥ e b) (rows i)
  rw [hM,hM]
  simpa only [P,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,Submodule.subtype_apply] using congrFun hab i

/-- Each selected coordinate is represented by an element of a bounded-dimensional
space over the smaller field. No scalar-extension dimension identity is assumed. -/
theorem bounded_coordinate_rank {F K U V J : Type*} [Field F] [Field K] [Fintype J]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A : V →ₗ[F] (J → U)) (hA : Function.Injective A) (φ : U → K) (hφ : Function.Injective φ)
    (W : Submodule K (J → K)) (hw : ∀ v, (fun i => φ (A v i)) ∈ W) :
    Module.finrank F V ≤ Module.finrank K W * Module.finrank F U := by
  classical
  obtain ⟨rows,hi⟩ := separating_coordinates W
  let L : V →ₗ[F] (Fin (Module.finrank K W) → U) := LinearMap.pi fun i => (LinearMap.proj (rows i)).comp A
  have hL : Function.Injective L := by
    intro a b hab
    let va : W := ⟨_,hw a⟩
    let vb : W := ⟨_,hw b⟩
    have h : va = vb := hi (by funext i; exact congrArg φ (congrFun hab i))
    apply hA
    funext j
    exact hφ (congrArg (fun z : W => z.val j) h)
  simpa [Module.finrank_pi_fintype] using LinearMap.finrank_le_finrank_of_injective hL

variable {F : Type} [Field F] {ι : Type*} [Fintype ι]

/-- A coordinate slot indexes the value and evaluation-coordinate exponents, leaving
one polynomial in the scalar variable in every slot. -/
abbrev Slots (v d T : ℕ) := (j : Fin (v+1)) × Fin (T-j.val*d)

noncomputable def parameterCoeffs (s v d T : ℕ) :
    (Monomials s v d T → F) →ₗ[F] (Slots v d T → Fin (s+1) → F) where
  toFun c k i := if hi : i.val < s+1-k.1.val then c ⟨k.1,⟨i.val,hi⟩,k.2⟩ else 0
  map_add' a b := by funext k i; by_cases hi : i.val < s+1-k.1.val <;> simp [hi]
  map_smul' g a := by funext k i; by_cases hi : i.val < s+1-k.1.val <;> simp [hi]

private theorem parameterCoeffs_injective (s v d T : ℕ) : Function.Injective (parameterCoeffs (F:=F) s v d T) := by
  intro a b h
  funext m
  obtain ⟨j,i,k⟩ := m
  have hi := i.isLt
  have H := congrFun (congrFun h (⟨j,k⟩ : Slots v d T)) (⟨i,by omega⟩ : Fin (s+1))
  simpa [parameterCoeffs,hi] using H

/-- Interpret bounded scalar coefficients in the rational function field. -/
noncomputable def scalarEntry {s : ℕ} (v : Fin (s+1) → F) : FractionRing F[X] :=
  algebraMap F[X] (FractionRing F[X]) (∑ i, monomial i.val (v i))

private theorem scalarEntry_injective (s : ℕ) : Function.Injective (scalarEntry (F:=F) (s:=s)) := by
  intro a b h
  have hh := IsFractionRing.injective F[X] (FractionRing F[X]) h
  funext i
  simpa [finsetSum_coeff,coeff_monomial,Fin.val_inj] using congrArg (fun p : F[X] => p.coeff i.val) hh

/-- The space of actual jet interpolants after changing to the scalar function field. -/
noncomputable def scalarSpan (dom : ι ↪ F) (u v₁ : ι → F) (s v d t r : ℕ) :
    Submodule (FractionRing F[X]) (Slots v d (r*t) → FractionRing F[X]) :=
  Submodule.span _ (Set.range fun c : LinearMap.ker (jetMatrix dom u v₁ s v d t r).mulVecLin =>
    fun j => scalarEntry (parameterCoeffs s v d (r*t) c.val j))

theorem production_rank (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = 1073741824) :
    247782756 ≤ Module.finrank (FractionRing F[X]) (scalarSpan dom u v 1000000 4 536870911 803929776 3) := by
  classical
  let V := LinearMap.ker (jetMatrix dom u v 1000000 4 536870911 803929776 3).mulVecLin
  let A := (parameterCoeffs 1000000 4 536870911 (3*803929776)).comp V.subtype
  have h := bounded_coordinate_rank A ((parameterCoeffs_injective ..).comp Subtype.val_injective)
    scalarEntry (scalarEntry_injective _) (scalarSpan dom u v 1000000 4 536870911 803929776 3)
    (fun c => Submodule.subset_span ⟨c,rfl⟩)
  have hr := (production_dim dom u v hn).trans h
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hr
  omega

#print axioms production_rank
end ArkLib.ProximityGap.Frontier.HalfSuccessorJetRank
