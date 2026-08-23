/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HigherOrderMDSListGenPos
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Reed–Solomon frame is an MDS frame (#389, layer 5)

Grounds the abstract general-position list bound (layer 4) in the *actual* Reed–Solomon
code.  The RS generator presents its columns as the Vandermonde frame
`v i = (1, Dᵢ, Dᵢ², …, Dᵢ^{k-1}) ∈ Kᵏ` (`D` the evaluation points, a message functional
`m` evaluates to `m (v i) = p(Dᵢ)`).  Distinct evaluation points make every `≤ k` of these
columns linearly independent (the square Vandermonde determinant `∏(Dⱼ − Dᵢ) ≠ 0`), so the
frame is an `IsMDSFrame`.  Hence `mds_genpos_list_bound` applies verbatim: an
affinely-independent family of RS messages cannot all agree with a received word on more
than the capacity-radius fraction of coordinates.

* `rs_columns_linearIndependent` — `≤ k` Vandermonde columns at distinct points are
  linearly independent.
* `reedSolomonFrame` / `reedSolomonFrame_isMDS` — the RS frame and its MDS property.

Issue #389.
-/

open Finset Module Matrix ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Vandermonde column independence.**  At distinct points, any `≤ k` of the columns
`v i = (Dᵢʲ)_{j<k}` are linearly independent. -/
theorem rs_columns_linearIndependent {D : ι → K} (hD : Function.Injective D) {k : ℕ}
    {J : Finset ι} (hJ : J.card ≤ k) :
    LinearIndependent K (fun i : J => (fun j : Fin k => (D (i : ι)) ^ (j : ℕ))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- per-coordinate vanishing
  have hcoord : ∀ j : Fin k, ∑ i : J, g i * (D (i : ι)) ^ (j : ℕ) = 0 := by
    intro j
    have := congrFun hg j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  -- reindex J to Fin s
  set s := Fintype.card J with hs
  have hsk : s ≤ k := by rw [hs, Fintype.card_coe]; exact hJ
  set e : J ≃ Fin s := Fintype.equivFin J with he
  set w : Fin s → K := fun l => D ((e.symm l : J) : ι) with hw
  have hwinj : Function.Injective w := by
    intro a b hab
    exact e.symm.injective (Subtype.ext (hD hab))
  set M : Matrix (Fin s) (Fin s) K := Matrix.vandermonde w with hM
  have hdet : M.det ≠ 0 := (Matrix.det_vandermonde_ne_zero_iff).2 hwinj
  -- the reindexed coefficient vector
  set x : Fin s → K := fun l => g (e.symm l) with hx
  -- x is killed by Mᵀ.mulVec
  have hker : M.transpose.mulVec x = 0 := by
    funext l'
    have hcl : ∑ i : J, g i * (D (i : ι)) ^ (l' : ℕ) = 0 := by
      have h := hcoord (Fin.castLE hsk l')
      simpa [Fin.coe_castLE] using h
    show (M.transpose.mulVec x) l' = (0 : Fin s → K) l'
    calc (M.transpose.mulVec x) l'
        = ∑ l : Fin s, w l ^ (l' : ℕ) * x l := by
          simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hM,
            Matrix.vandermonde_apply]
      _ = ∑ l : Fin s, g (e.symm l) * (D ((e.symm l : J) : ι)) ^ (l' : ℕ) := by
          refine Finset.sum_congr rfl (fun l _ => ?_); rw [hw, hx]; ring
      _ = ∑ i : J, g i * (D (i : ι)) ^ (l' : ℕ) :=
          Equiv.sum_comp e.symm (fun i : J => g i * (D (i : ι)) ^ (l' : ℕ))
      _ = 0 := hcl
      _ = (0 : Fin s → K) l' := by simp
  -- nonsingular ⟹ x = 0
  have hxz : x = 0 := by
    have hunit : IsUnit M.transpose :=
      (Matrix.isUnit_iff_isUnit_det M.transpose).mpr
        (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hdet)
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := M.transpose)).2 hunit
    have heq : M.transpose.mulVec x = M.transpose.mulVec 0 := by
      rw [hker, Matrix.mulVec_zero]
    exact hinj heq
  intro i
  have := congrFun hxz (e i)
  simpa [hx, Equiv.symm_apply_apply] using this

/-- The Reed–Solomon Vandermonde frame in the `k`-dimensional message space `Fin k → K`. -/
noncomputable def reedSolomonFrame (D : ι → K) (k : ℕ) : ι → (Fin k → K) :=
  fun i j => (D i) ^ (j : ℕ)

/-- **The Reed–Solomon frame is an MDS frame** (distinct points, `2 ≤ k`). -/
theorem reedSolomonFrame_isMDS {D : ι → K} (hD : Function.Injective D) {k : ℕ}
    (hk : 2 ≤ k) : IsMDSFrame K (reedSolomonFrame D k) := by
  classical
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h1 := congrFun hab ⟨1, by omega⟩
    simp only [reedSolomonFrame, Fin.val_mk, pow_one] at h1
    exact hD h1
  · intro J hJ
    have hJk : J.card ≤ k := by simpa [Module.finrank_pi, Fintype.card_fin] using hJ
    exact rs_columns_linearIndependent hD hJk

/-- **The Reed–Solomon general-position list bound** (explicit RS codes).  For distinct
evaluation points `D` and `2 ≤ k`, an affinely-independent family of `L+1` RS messages
(`1 ≤ L < k`) cannot all agree with a received word `y` on more than the capacity-radius
fraction: `(L+1)·a ≤ L·n + (k − L)`.  This is genuine beyond-Johnson list decoding for
actual Reed–Solomon codes, in general position, from the Vandermonde MDS structure alone. -/
theorem reedSolomon_genpos_list_bound [DecidableEq K] {D : ι → K}
    (hD : Function.Injective D) {k : ℕ} (hk : 2 ≤ k) {L : ℕ} (hL1 : 1 ≤ L) (hLk : L < k)
    {m : Fin (L + 1) → Module.Dual K (Fin k → K)} {y : ι → K}
    (hindep : LinearIndependent K (fun j : Fin L => m j.succ - m 0))
    {a : ℕ} (hagree : ∀ i, a ≤ (agreeFinset (reedSolomonFrame D k) y (m i)).card) :
    (L + 1) * a ≤ L * Fintype.card ι + (k - L) := by
  have hfr : finrank K (Fin k → K) = k := by simp [Module.finrank_pi]
  have h := mds_genpos_list_bound hL1 (by rw [hfr]; exact hLk)
    (reedSolomonFrame_isMDS hD hk) hindep hagree
  rwa [hfr] at h

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.rs_columns_linearIndependent
#print axioms ArkLib.HigherOrderMDS.reedSolomonFrame_isMDS
#print axioms ArkLib.HigherOrderMDS.reedSolomon_genpos_list_bound
