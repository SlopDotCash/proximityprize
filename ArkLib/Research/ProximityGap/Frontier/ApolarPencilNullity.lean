/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Total nullity of an affine matrix pencil

A regular specialization identifies the kernels at distinct scalar parameters
with subspaces of different eigenspaces of a common endomorphism.
-/

set_option autoImplicit false
open Finset Module Polynomial
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.ApolarPencilNullity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The sum of the nullities of a regular affine pencil on a finite scalar set
is at most the ambient dimension, including when the anchor is in the set. -/
theorem sum_nullity_le (A B : End K V) (S : Finset K) (u : K)
    (U : V ≃ₗ[K] V) (hU : (U : End K V) = A + u • B) :
    ∑ t ∈ S, finrank K (LinearMap.ker (A+t • B)) ≤ finrank K V := by
  classical
  let N : End K V := U.symm.toLinearMap.comp B
  let p (t : S) := N.eigenspace ((u-t.val)⁻¹)
  have hind : iSupIndep p := N.eigenspaces_iSupIndep.comp (by
    intro t s h
    apply Subtype.ext
    exact sub_right_inj.mp (inv_injective h))
  have hbound := LinearMap.finrank_le_finrank_of_injective hind.dfinsupp_lsum_injective
  have hsum : ∑ t : S, finrank K (p t) ≤ finrank K V := by
    rw [← Module.finrank_directSum (R := K) (fun t : S => ↥(p t))]
    exact hbound
  rw [← S.sum_attach (fun t => finrank K (LinearMap.ker (A+t • B)))]
  refine (Finset.sum_le_sum fun t _ => Submodule.finrank_mono ?_).trans hsum
  intro x hx
  apply Module.End.mem_eigenspace_iff.mpr
  have hz := LinearMap.mem_ker.mp hx
  change A x + t.val • B x = 0 at hz
  have hux : U x = A x + u • B x := by
    change (U : End K V) x = _
    rw [hU]
    rfl
  have he : (u-t.val) • B x = U x := by
    rw [sub_smul,hux]
    have ha : A x = -(t.val • B x) := eq_neg_of_add_eq_zero_left hz
    rw [ha]
    abel
  by_cases ht : u = t.val
  · rw [ht,sub_self,zero_smul] at he
    have hx0 : x = 0 := U.injective (by simpa using he.symm)
    simp [hx0]
  · have hb : B x = (u-t.val)⁻¹ • U x := by
      rw [← he,inv_smul_smul₀ (sub_ne_zero.mpr ht)]
    simp [N,hb]

/-- The same rank budget in the native square-matrix representation. -/
theorem sum_matrix_nullity_le {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I K) (S : Finset K) (u : K) (hu : (A+u • B).det ≠ 0) :
    ∑ t ∈ S, finrank K (LinearMap.ker (A+t • B).mulVecLin) ≤ Fintype.card I := by
  let U := (A+u • B).toLinearEquiv' ((A+u • B).invertibleOfIsUnitDet hu.isUnit)
  have hU : (U : End K (I → K)) = Matrix.toLin' A + u • Matrix.toLin' B := by
    simp [U]
  have hn := sum_nullity_le (Matrix.toLin' A) (Matrix.toLin' B) S u U hU
  have ha (t : K) : (A+t • B).mulVecLin = Matrix.toLin' A + t • Matrix.toLin' B := by
    rw [← Matrix.toLin'_apply',map_add,map_smul]
  calc
    _ = ∑ t ∈ S, finrank K (LinearMap.ker (Matrix.toLin' A + t • Matrix.toLin' B)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [ha t]
    _ ≤ _ := by simpa only [Module.finrank_pi] using hn

/-- A sum of scalar moments on a common support factors through its evaluation
space and therefore has matrix rank bounded by the support size. -/
theorem weighted_matrix_rank_le {I X : Type*} [Fintype I] (E : Finset X)
    (w : X → K) (a b : I → X → K) (D : Matrix I I K)
    (hD : ∀ i j, D i j = ∑ x ∈ E, w x * a i x * b j x) :
    D.rank ≤ E.card := by
  classical
  let L : Matrix I E K := fun i x => w x.val * a i x.val
  let R : Matrix E I K := fun x j => b j x.val
  have hf : D = L * R := by
    ext i j
    rw [hD,Matrix.mul_apply]
    exact (E.sum_attach (fun x => w x * a i x * b j x)).symm
  rw [hf]
  simpa using ((Matrix.rank_mul_le_left L R).trans L.rank_le_card_width)

/-- For any regular affine matrix pencil whose specialization ranks are
bounded by finite error supports, counting incidences at both ends bounds the
total number of parameters. Each site may carry its own parameter polynomial. -/
theorem support_incidence_bound {I X : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I K) (S : Finset K) (u : K) (hu : (A+u • B).det ≠ 0)
    (H : Finset X) (E : K → Finset X) (ℓ : ℕ) (m : X → K[X])
    (hs : ∀ t ∈ S, E t ⊆ H) (hr : ∀ t ∈ S, (A+t • B).rank ≤ (E t).card)
    (hm : ∀ x ∈ H, m x ≠ 0 ∧ (m x).natDegree ≤ ℓ)
    (hz : ∀ t ∈ S, ∀ x ∈ E t, (m x).eval t = 0) :
    S.card * Fintype.card I ≤ H.card * ℓ + Fintype.card I := by
  classical
  have hd (t : K) (ht : t ∈ S) : Fintype.card I ≤ (E t).card +
      finrank K (LinearMap.ker (A+t • B).mulVecLin) := by
    have he := (A+t • B).mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_pi] at he
    have hr' := hr t ht
    change finrank K (LinearMap.range _) ≤ _ at hr'
    omega
  have hdeg (x : X) (hx : x ∈ H) : (S.filter fun t => x ∈ E t).card ≤ ℓ := by
    let U := S.filter fun t => x ∈ E t
    have hsub : U ⊆ (m x).roots.toFinset := by
      intro t ht
      obtain ⟨htS,hxE⟩ := Finset.mem_filter.mp ht
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hm x hx).1).mpr (hz t htS x hxE))
    exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (hm x hx).2))
  have hcard (t : K) (ht : t ∈ S) : H.filter (· ∈ E t) = E t := by
    ext x
    exact ⟨(fun hx => (Finset.mem_filter.mp hx).2), fun hx => Finset.mem_filter.mpr ⟨hs t ht hx,hx⟩⟩
  have hpack : ∑ t ∈ S, (E t).card ≤ H.card * ℓ := by
    calc
      _ = ∑ t ∈ S, ∑ x ∈ H, if x ∈ E t then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.sum_boole,hcard t ht]
        simp
      _ = ∑ x ∈ H, ∑ t ∈ S, if x ∈ E t then 1 else 0 := Finset.sum_comm
      _ ≤ ∑ _ ∈ H, ℓ := Finset.sum_le_sum fun x hx => by simpa using hdeg x hx
      _ = _ := by simp
  have htot := Finset.sum_le_sum hd
  rw [Finset.sum_add_distrib] at htot
  simpa using (htot.trans (Nat.add_le_add hpack (sum_matrix_nullity_le A B S u hu)))

end ArkLib.ProximityGap.Frontier.ApolarPencilNullity

#print axioms ArkLib.ProximityGap.Frontier.ApolarPencilNullity.sum_nullity_le

#print axioms ArkLib.ProximityGap.Frontier.ApolarPencilNullity.support_incidence_bound
