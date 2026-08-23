/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R236 top-trimmed survival MGF socket)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_survival_to_mgf

/-!
# R236 (#466): top-trimmed survival accounting to MGF

R231-R235 suggest the live analytic shape is no longer a plain survival
envelope.  Instead:

* pay a small exceptional/top set `T` exactly;
* prove a residual survival envelope for `s \ T`;
* combine the exact top payment and residual weighted envelope.

This file packages that accounting at the abstract finite-carrier level.  It is
intended as the reusable socket for the top-five quotient-orbit route.
-/

open Finset
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R236TopTrimmedSurvivalMGF

open ArkLib.ProximityGap.Frontier.WFS11

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- The exact top-set staircase payment plus a residual count envelope. -/
def TopTrimmedBound (s T : Finset ι) (t : ι → ℝ) (Bres : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (((T ∩ s).filter (fun b => θ ≤ t b)).card : ℝ) + Bres θ

/-- Pointwise form of the top-trimmed survival-count bound. -/
theorem survival_count_le_topTrimmedBound_at
    (s T : Finset ι) (t : ι → ℝ) (Bres : ℝ → ℝ)
    (θ : ℝ)
    (hres : (((s \ T).filter (fun b => θ ≤ t b)).card : ℝ) ≤ Bres θ) :
    (((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤
      TopTrimmedBound s T t Bres θ) := by
  let A : Finset ι := s.filter (fun b => θ ≤ t b)
  let AT : Finset ι := (T ∩ s).filter (fun b => θ ≤ t b)
  let AR : Finset ι := (s \ T).filter (fun b => θ ≤ t b)
  have hsubset : A ⊆ AT ∪ AR := by
    intro b hb
    have hbs : b ∈ s := (Finset.mem_filter.mp hb).1
    have hbt : θ ≤ t b := (Finset.mem_filter.mp hb).2
    by_cases hbT : b ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hbT, hbs⟩, hbt⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hbs, hbT⟩, hbt⟩)
  have hcardA : A.card ≤ (AT ∪ AR).card := Finset.card_le_card hsubset
  have hcardUnion : (AT ∪ AR).card ≤ AT.card + AR.card :=
    Finset.card_union_le AT AR
  have hnat : A.card ≤ AT.card + AR.card := le_trans hcardA hcardUnion
  have hreal : (A.card : ℝ) ≤ (AT.card : ℝ) + (AR.card : ℝ) := by
    exact_mod_cast hnat
  calc
    (((s.filter (fun b => θ ≤ t b)).card : ℝ) = (A.card : ℝ)) := rfl
    _ ≤ (AT.card : ℝ) + (AR.card : ℝ) := hreal
    _ ≤ (AT.card : ℝ) + Bres θ := by
      simpa [AR] using add_le_add_left hres (AT.card : ℝ)
    _ = TopTrimmedBound s T t Bres θ := by
      rfl

/-- If `T` pays its own survivors exactly and `Bres` bounds the residual
survivors on `s \ T`, then `TopTrimmedBound` bounds all survivors on `s`. -/
theorem survival_count_le_topTrimmedBound
    (s T : Finset ι) (t : ι → ℝ) (Bres : ℝ → ℝ)
    (hres : ∀ θ,
      (((s \ T).filter (fun b => θ ≤ t b)).card : ℝ) ≤ Bres θ)
    (θ : ℝ) :
    (((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤
      TopTrimmedBound s T t Bres θ) :=
  survival_count_le_topTrimmedBound_at s T t Bres θ (hres θ)

/-- Top-trimmed survival-count ceilings imply an abstract MGF bound. -/
theorem mgfBound_of_topTrimmed_survival_count_ceiling
    (s T : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ Bres : ℝ → ℝ) {A c : ℝ}
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp (c * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hres : ∀ θ ∈ Θ,
      (((s \ T).filter (fun b => θ ≤ t b)).card : ℝ) ≤ Bres θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * TopTrimmedBound s T t Bres θ) ≤ A * (s.card : ℝ)) :
    MGFBound s t A c := by
  refine mgfBound_of_survival_count_ceiling s t Θ δ (TopTrimmedBound s T t Bres) hδ hstair ?_ hweighted
  intro θ hθ
  exact survival_count_le_topTrimmedBound_at s T t Bres θ (hres θ hθ)

/-- Quarter-MGF specialization used by the top-five route. -/
theorem two_mgfBound_of_topTrimmed_survival_count_ceiling
    (s T : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ Bres : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hres : ∀ θ ∈ Θ,
      (((s \ T).filter (fun b => θ ≤ t b)).card : ℝ) ≤ Bres θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * TopTrimmedBound s T t Bres θ) ≤ 2 * (s.card : ℝ)) :
    MGFBound s t 2 (1 / 4 : ℝ) := by
  exact mgfBound_of_topTrimmed_survival_count_ceiling
    s T t Θ δ Bres hδ hstair hres hweighted

end

end ArkLib.ProximityGap.Frontier.R236TopTrimmedSurvivalMGF

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R236TopTrimmedSurvivalMGF.survival_count_le_topTrimmedBound
#print axioms
  ArkLib.ProximityGap.Frontier.R236TopTrimmedSurvivalMGF.mgfBound_of_topTrimmed_survival_count_ceiling
#print axioms
  ArkLib.ProximityGap.Frontier.R236TopTrimmedSurvivalMGF.two_mgfBound_of_topTrimmed_survival_count_ceiling
