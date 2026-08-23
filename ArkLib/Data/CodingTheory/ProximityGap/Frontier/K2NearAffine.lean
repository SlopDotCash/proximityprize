/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.K2Affine
import ArkLib.Data.CodingTheory.ProximityGap.SparseDirectionGeneralK
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The near-affine half of the k = 2 universal law (scratch)

When some pair `(i,j)` with `dom i ≠ dom j` has `≥ n−w` collinear completions,
`u₁` agrees with the affine codeword through that pair on `≥ n−w` points, so the
direction translates to one supported on `≤ w` positions; the general-`K` sparse
bound then gives `#bad · (n−2w−1)² ≤ n²·w`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap.MCAEquivariance

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The near-affine half**: if a pair `(i,j)` with distinct domain points owns
`≥ n−w` collinear completions, then at every radius `δ ≤ w/n`,
`#bad · ((n−2w)+1−2)² ≤ n²·w`. -/
theorem badScalars_card_mul_le_of_nearAffine (dom : Fin n ↪ F) {w : ℕ}
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) (h2w : 2 ≤ n - w - w)
    {u₀ u₁ : Fin n → F} {i j : Fin n} (hij : dom i ≠ dom j)
    (hcompl : n - w ≤
      (Finset.univ.filter (fun c => residual dom 2 ![i, j, c] u₁ = 0)).card) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * ((n - w - w) + 1 - 2) ^ 2 ≤ n ^ 2 * w := by
  -- the affine codeword through (i,j) and the translated direction
  set b := (u₁ j - u₁ i) / (dom j - dom i) with hb
  set a := u₁ i - b * dom i with ha
  set ε : Fin n → F := u₁ - (fun c => a + b * dom c) with hε
  -- ε vanishes on the completion set, so its support has `≤ w` points
  have hsupp : (Finset.univ.filter (fun i => ε i ≠ 0)).card ≤ w := by
    have hsub : Finset.univ.filter (fun c => ε c ≠ 0)
        ⊆ Finset.univ.filter (fun c => ¬ residual dom 2 ![i, j, c] u₁ = 0) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      intro hcon
      apply hc
      have hP := residual_two_zero_affine dom u₁ hij hcon
      simp only [hε, Pi.sub_apply, ha, hb]
      linear_combination hP
    have hcompl2 : (Finset.univ.filter
        (fun c => ¬ residual dom 2 ![i, j, c] u₁ = 0)).card ≤ w := by
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun c => residual dom 2 ![i, j, c] u₁ = 0)
      have huniv : (Finset.univ : Finset (Fin n)).card = n := by
        rw [Finset.card_univ, Fintype.card_fin]
      omega
    exact le_trans (Finset.card_le_card hsub) hcompl2
  -- translation equivariance: the bad set of `u₁` equals that of `ε`
  have htrans : ∀ γ : F, mcaEvent (F := F)
      ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ ↔
      mcaEvent (F := F)
      ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ := by
    intro γ
    have h := mcaEvent_translate (rsCode dom 2 : Submodule F (Fin n → F)) (δ := δ)
      (u₀ := u₀) (u₁ := ε) (c₀ := 0) (c₁ := fun c => a + b * dom c)
      (rsCode dom 2 : Submodule F (Fin n → F)).zero_mem
      (affine_mem_rsCode_two dom a b) γ
    have he0 : u₀ + 0 = u₀ := by funext i; simp
    have he1 : ε + (fun c => a + b * dom c) = u₁ := by funext i; simp [hε]
    rw [he0, he1] at h
    exact h
  have hfilter : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
      = (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)) := by
    refine Finset.filter_congr fun γ _ => ?_
    rw [htrans γ]
  rw [hfilter]
  have hsparse := sparse_direction_badScalars_card_le_generalK dom (k := 2)
    (w := w) (e := w) hδn h2w (u₀ := u₀) (ε := ε) hsupp
  exact hsparse

end ProximityGap.Ownership

#print axioms ProximityGap.Ownership.badScalars_card_mul_le_of_nearAffine
