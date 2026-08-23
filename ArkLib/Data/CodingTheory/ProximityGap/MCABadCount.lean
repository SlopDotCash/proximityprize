/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.Probability.Instances

/-!
# The Grand MCA Challenge as a finite extremal count

The mutual-correlated-agreement error of a code over a finite field is, at every radius,
*exactly* a normalised count of bad scalars:

  `ε_mca(C, δ) = (⨆ u, mcaBadCount C δ (u 0) (u 1)) / q`,

where `mcaBadCount C δ u₀ u₁ := #{γ : F | mcaEvent C δ u₀ u₁ γ}`.

All previously proved bounds are bounds on this count: the spike floor
(`MCAEndpointLower`) gives `min(n-k, q)` bad scalars, the subset-sum adversary gives
`|Σ_{k+1}(L)|`, the pinning bound (`MCAEndpointUpper`) caps it at `2ⁿ`, the `(k+1)`-subset
functional analysis (`GrandChallengeRadiusOne(Exact)`) caps it at `C(n, k+1)` and attains
that cap for `q > C(C(n,k+1), 2)`. Determining `⨆ u, mcaBadCount` exactly in the
remaining middle band of field sizes is the residual open content of the formalized
challenge. See `[ABF26]` §1.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- The number of bad scalars `γ : F` realising the MCA event for the pair `(u₀, u₁)` at
radius `δ`. -/
noncomputable def mcaBadCount (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ :=
  (Finset.univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)).card

/-- If no scalar realizes the MCA bad event, the finite bad-scalar count is zero. -/
theorem mcaBadCount_eq_zero_of_forall_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (h : ∀ γ : F, ¬ mcaEvent C δ u₀ u₁ γ) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 := by
  classical
  rw [mcaBadCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro γ _ hγ
  exact h γ hγ

/-- The full code has no bad scalars in the finite MCA bad-count model. -/
theorem mcaBadCount_univ_eq_zero
    (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    mcaBadCount (F := F) (A := A) (Set.univ : Set (ι → A)) δ u₀ u₁ = 0 := by
  refine mcaBadCount_eq_zero_of_forall_not_mcaEvent
    (F := F) (A := A) (Set.univ : Set (ι → A)) δ u₀ u₁ ?_
  intro γ
  rintro ⟨S, hS, hw, hno⟩
  exact hno ⟨u₀, Set.mem_univ _, u₁, Set.mem_univ _, fun i _ => ⟨rfl, rfl⟩⟩

/-- The top/full linear code has no bad scalars in the finite MCA bad-count model. This is
the linear-code form of `mcaBadCount_univ_eq_zero`, avoiding caller-side `Set.univ` rewrites. -/
theorem mcaBadCount_top_eq_zero
    (δ : ℝ≥0) (u₀ u₁ : ι → F) :
    mcaBadCount (F := F) (((⊤ : LinearCode ι F) : Set (ι → F))) δ u₀ u₁ = 0 := by
  rw [show (((⊤ : LinearCode ι F) : Set (ι → F)) = Set.univ) by
    ext x
    simp]
  exact mcaBadCount_univ_eq_zero (F := F) (A := F) δ u₀ u₁

/-- The finite bad-scalar count vanishes exactly when no scalar realizes the MCA bad event. -/
theorem mcaBadCount_eq_zero_iff_forall_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 ↔
      ∀ γ : F, ¬ mcaEvent C δ u₀ u₁ γ := by
  classical
  constructor
  · intro hzero γ hγ
    rw [mcaBadCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
    exact hzero (Finset.mem_univ γ) hγ
  · exact mcaBadCount_eq_zero_of_forall_not_mcaEvent C δ u₀ u₁

/-- The probability of the MCA event is exactly the normalised bad-scalar count. -/
theorem pr_mcaEvent_eq_mcaBadCount_div (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{ let γ ←$ᵖ F }[ mcaEvent C δ u₀ u₁ γ ] =
      (mcaBadCount (F := F) C δ u₀ u₁ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  rw [mcaBadCount]
  push_cast
  rfl

/-- **Exact extremal form of the MCA error.** Over a finite field, `ε_mca(C, δ)` *is* the
maximal normalised bad-scalar count. -/
theorem epsMCA_eq_iSup_mcaBadCount (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ =
      (⨆ u : WordStack A (Fin 2) ι,
        (mcaBadCount (F := F) C δ (u 0) (u 1) : ℝ≥0∞)) / (Fintype.card F : ℝ≥0∞) := by
  classical
  unfold epsMCA
  rw [ENNReal.iSup_div]
  exact iSup_congr fun u => pr_mcaEvent_eq_mcaBadCount_div C δ (u 0) (u 1)

/-- If every stack has zero bad scalars, then the MCA error vanishes. -/
theorem epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero (C : Set (ι → A)) (δ : ℝ≥0)
    (h : ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    epsMCA (F := F) C δ = 0 := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  have hzero : ∀ u : WordStack A (Fin 2) ι,
      (mcaBadCount (F := F) C δ (u 0) (u 1) : ℝ≥0∞) = 0 := by
    intro u
    rw [h u]
    simp
  rw [iSup_congr hzero]
  simp

/-- The top/full linear code has zero MCA error at every radius. -/
theorem epsMCA_top_eq_zero (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (((⊤ : LinearCode ι F) : Set (ι → F))) δ = 0 :=
  epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero
    (((⊤ : LinearCode ι F) : Set (ι → F))) δ
    (fun u => mcaBadCount_top_eq_zero δ (u 0) (u 1))

/-- If the MCA error vanishes, every stack has zero bad scalars. -/
theorem forall_mcaBadCount_eq_zero_of_epsMCA_eq_zero (C : Set (ι → A)) (δ : ℝ≥0)
    (heps : epsMCA (F := F) C δ = 0) :
    ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0 := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount] at heps
  have hsup :
      (⨆ u : WordStack A (Fin 2) ι,
        (mcaBadCount (F := F) C δ (u 0) (u 1) : ℝ≥0∞)) = 0 := by
    rcases (ENNReal.div_eq_zero_iff.mp heps) with hzero | htop
    · exact hzero
    · exact False.elim ((ENNReal.natCast_ne_top (Fintype.card F)) htop)
  have hzero := (ENNReal.iSup_eq_zero.mp hsup)
  intro u
  have hcount :
      (mcaBadCount (F := F) C δ (u 0) (u 1) : ℝ≥0∞) = 0 := hzero u
  exact_mod_cast hcount

/-- Vanishing MCA error is equivalent to zero bad-scalar counts for every stack. -/
theorem epsMCA_eq_zero_iff_forall_mcaBadCount_eq_zero (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ = 0 ↔
      ∀ u : WordStack A (Fin 2) ι,
        mcaBadCount (F := F) C δ (u 0) (u 1) = 0 := by
  constructor
  · exact forall_mcaBadCount_eq_zero_of_epsMCA_eq_zero C δ
  · exact epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero C δ

/-- If no stack/scalar pair realizes the MCA bad event, then the MCA error vanishes. -/
theorem epsMCA_eq_zero_of_forall_not_mcaEvent (C : Set (ι → A)) (δ : ℝ≥0)
    (h : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      ¬ mcaEvent C δ (u 0) (u 1) γ) :
    epsMCA (F := F) C δ = 0 :=
  epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero C δ fun u =>
    mcaBadCount_eq_zero_of_forall_not_mcaEvent C δ (u 0) (u 1) (h u)

#print axioms ProximityGap.mcaBadCount_eq_zero_of_forall_not_mcaEvent
#print axioms ProximityGap.mcaBadCount_univ_eq_zero
#print axioms ProximityGap.mcaBadCount_top_eq_zero
#print axioms ProximityGap.mcaBadCount_eq_zero_iff_forall_not_mcaEvent
#print axioms ProximityGap.epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero
#print axioms ProximityGap.epsMCA_top_eq_zero
#print axioms ProximityGap.forall_mcaBadCount_eq_zero_of_epsMCA_eq_zero
#print axioms ProximityGap.epsMCA_eq_zero_iff_forall_mcaBadCount_eq_zero
#print axioms ProximityGap.epsMCA_eq_zero_of_forall_not_mcaEvent

end ProximityGap
