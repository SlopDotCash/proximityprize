/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GenericFarPin
import ArkLib.Data.CodingTheory.ProximityGap.UniversalAlignmentLaw

/-!
# Exact boundary-band MCA value from the generic-far pin (#371)

`GenericFarPin.lean` proves that, when `C(n,k+1)^2 ≤ |F|`, some stack attains
`C(n,k+1)` bad scalars at the boundary band.  The universal alignment law gives the
matching all-stack upper bound at the same band: every bad scalar owns a `(k+1)`-set.
Together these pin the boundary-band value of `epsMCA` exactly.
-/

open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.Ownership

open Code
open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- At the boundary band, every stack has at most `C(n,k+1)` bad scalars. -/
theorem boundary_badScalars_card_le_choose (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n.choose (k + 1) := by
  letI := Classical.decEq F
  have hlo' : (((k + 1 - 1 : ℕ) : ℝ≥0)
      < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) := by
    have hk' : k + 1 - 1 = k := by omega
    simpa [hk'] using hlo
  calc
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
            (fun S : Finset (Fin n) =>
              ∃ γ : F, Aligned dom k u₀ u₁ γ S ∧
                ∃ t : Fin (k + 1) → Fin n,
                  Function.Injective t ∧ (∀ b, t b ∈ S) ∧
                    ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))).card := by
          exact badScalars_card_le_alignable dom hk le_rfl hlo' hhi u₀ u₁
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
    _ = n.choose (k + 1) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- Boundary-band all-stack upper bound in `epsMCA` form. -/
theorem epsMCA_le_boundary_choose (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ)) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n.choose (k + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  letI := Classical.decEq F
  exact epsMCA_le_of_badCount_le
    (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ
    (n.choose (k + 1))
    (fun u => boundary_badScalars_card_le_choose dom hk hlo hhi (u 0) (u 1))

open Classical in
/-- **Exact boundary-band value.**  If `C(n,k+1)^2 ≤ |F|`, the generic-far stack
from `exists_genericFar_badSet_card` attains the universal boundary upper bound, so
`epsMCA = C(n,k+1)/|F|`. -/
theorem epsMCA_eq_boundary_choose_of_genericFar (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hsmall : (n.choose (k + 1)) ^ 2 ≤ Fintype.card F) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      = ((n.choose (k + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  letI := Classical.decEq F
  refine le_antisymm (epsMCA_le_boundary_choose dom hk hlo hhi) ?_
  obtain ⟨Q₀, hQ₀⟩ := exists_genericFar_badSet_card dom hk hlo hhi hsmall
  let u₀ : Fin n → F := fun i => Q₀.eval (dom i)
  let u₁ : Fin n → F := fun i => (dom i) ^ k
  let u : WordStack F (Fin 2) (Fin n) := Code.finMapTwoWords u₀ u₁
  have hu0 : u 0 = u₀ := rfl
  have hu1 : u 1 = u₁ := rfl
  calc
    ((n.choose (k + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (u 0) (u 1) γ] := by
          rw [prob_uniform_eq_card_filter_div_card, hu0, hu1, hQ₀]
          norm_num
    _ ≤ epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ :=
          mcaEvent_prob_le_epsMCA
            (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ u

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.boundary_badScalars_card_le_choose
#print axioms ProximityGap.Ownership.epsMCA_le_boundary_choose
#print axioms ProximityGap.Ownership.epsMCA_eq_boundary_choose_of_genericFar
