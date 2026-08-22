/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.EtaPointwiseAutocorr

/-!
# _PhaseCorrelationOrbitCollapse

Module docstring for `_PhaseCorrelationOrbitCollapse.lean`.
-/


set_option linter.style.longLine false
set_option autoImplicit false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.PhaseCorrelationOrbitCollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem dilate_period {ψ : AddChar F ℂ} {G : Finset F} (b d₀ : F) :
    (∑ x ∈ G, ψ (b * (d₀ * x))) = eta ψ G (b * d₀) := by
  rw [eta]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1; ring

theorem eta_normSq_eq_card_add_dilatePeriods {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun z => u * z) = G) (h0 : (0 : F) ∉ G) (h1 : (1 : F) ∈ G)
    (b : F) (reps : Finset F) (mult : F → ℕ)
    (hcollapse :
      (∑ ζ ∈ G.erase 1, eta ψ G (b * (ζ - 1)))
        = ∑ d₀ ∈ reps, (mult d₀ : ℂ) * eta ψ G (b * d₀)) :
    ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = (G.card : ℂ) + ∑ d₀ ∈ reps, (mult d₀ : ℂ) * eta ψ G (b * d₀) := by
  rw [ArkLib.ProximityGap.EtaPointwiseAutocorr.eta_normSq_eq_card_add_nontrivial hbij h0 h1 b]
  rw [hcollapse]

theorem orbitCollapse_reduces_to_sup {ψ : AddChar F ℂ} {G : Finset F}
    (b : F) (reps : Finset F) (mult : F → ℕ) (M : ℝ)
    (hM : ∀ d₀ ∈ reps, ‖eta ψ G (b * d₀)‖ ≤ M) (hMnonneg : 0 ≤ M)
    (hform : ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = (G.card : ℂ) + ∑ d₀ ∈ reps, (mult d₀ : ℂ) * eta ψ G (b * d₀)) :
    (‖eta ψ G b‖ ^ 2 : ℝ) ≤ (G.card : ℝ) + (∑ d₀ ∈ reps, (mult d₀ : ℝ)) * M := by
  have hnorm : (‖eta ψ G b‖ ^ 2 : ℝ)
      = ‖(G.card : ℂ) + ∑ d₀ ∈ reps, (mult d₀ : ℂ) * eta ψ G (b * d₀)‖ := by
    rw [← hform]
    simp
  rw [hnorm]
  calc ‖(G.card : ℂ) + ∑ d₀ ∈ reps, (mult d₀ : ℂ) * eta ψ G (b * d₀)‖
      ≤ ‖(G.card : ℂ)‖ + ‖∑ d₀ ∈ reps, (mult d₀ : ℂ) * eta ψ G (b * d₀)‖ :=
        norm_add_le _ _
    _ ≤ (G.card : ℝ) + ∑ d₀ ∈ reps, ‖(mult d₀ : ℂ) * eta ψ G (b * d₀)‖ := by
        gcongr
        · simp
        · exact norm_sum_le _ _
    _ ≤ (G.card : ℝ) + ∑ d₀ ∈ reps, (mult d₀ : ℝ) * M := by
        gcongr with d₀ hd₀
        rw [norm_mul]
        have : ‖(mult d₀ : ℂ)‖ = (mult d₀ : ℝ) := by simp
        rw [this]
        exact mul_le_mul_of_nonneg_left (hM d₀ hd₀) (by positivity)
    _ = (G.card : ℝ) + (∑ d₀ ∈ reps, (mult d₀ : ℝ)) * M := by
        rw [Finset.sum_mul]

#print axioms dilate_period
#print axioms eta_normSq_eq_card_add_dilatePeriods
#print axioms orbitCollapse_reduces_to_sup

end ArkLib.ProximityGap.PhaseCorrelationOrbitCollapse
