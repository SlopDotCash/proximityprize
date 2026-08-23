/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaw, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ProximityGap.AHIV22
import ArkLib.Data.Probability.Instances

/-!
# AHIV17 affine-line probability bridge (issue #88)

The AHIV17/AHIV22 tighter `d/q = ‖RS‖₀/q` correlated-agreement bound is consumed at the
affine-line layer through the predicate `δ_ε_correlatedAgreementAffineLines`, whose `epsCA`
body is the *single-variable* uniform probability

  `Pr_{γ ← F}[δᵣ(u₀ + γ • u₁, RScodeSet α deg) ≤ δ]`.

This file proves the genuine per-line core of the AHIV17 argument: that this affine-line
probability is at most `‖RScodeSet α deg‖₀ / |F|` under the AHIV regime hypotheses.

The key observation (correcting the naive "specialize the 2-row row-span" route) is that the
affine-line predicate samples the *1-dimensional* line `{u₀ + γ • u₁ : γ ∈ F}` (|F| points), not
the 2-dimensional `Matrix.rowSpan` (|F|² points). The right bridge is therefore the *per-line
fiber count* that `prob_of_bad_pts` itself uses internally, namely
`numberOfClosePts u₀ u₁ deg α e ≤ ‖RS‖₀`, supplied by the mutual-exclusion corollary
`e_le_dist_over_3`.

## Main results

* `ProximityToRS.affineLine_close_count_eq_numberOfClosePts` — the count of field elements `γ`
  with `u₀ + γ • u₁` close to the code equals `numberOfClosePts`, when `u₁ ≠ 0`.
* `ProximityToRS.affineLine_prob_le_dOverQ` — the affine-line probability is at most
  `‖RS‖₀ / |F|` under the AHIV regime hypotheses.
-/

noncomputable section

open Code ProbabilityTheory NNReal

namespace ProximityToRS

open ReedSolomon

variable {F : Type} [Field F] [Finite F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

local instance : Fintype F := Fintype.ofFinite F

/-- The map `γ ↦ u₀ + γ • u₁` is injective whenever `u₁ ≠ 0`. -/
lemma affineLine_param_injective {u₀ u₁ : ι → F} (hu₁ : u₁ ≠ 0) :
    Function.Injective (fun γ : F => u₀ + γ • u₁) := by
  -- pick a coordinate where `u₁` is nonzero and cancel.
  obtain ⟨j, hj⟩ : ∃ j, u₁ j ≠ 0 := by
    by_contra h
    apply hu₁
    funext j
    by_contra hjj
    exact h ⟨j, hjj⟩
  intro a b hab
  have hval := congrArg (fun f : ι → F => f j) hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at hval
  exact mul_right_cancel₀ hj hval

/-- The number of field elements `γ` for which `u₀ + γ • u₁` is `e`-close to the Reed–Solomon
code equals the number of close points on the affine line, when the direction `u₁ ≠ 0`.

This is the bridge between the *parameter* count (over `γ ∈ F`, the form appearing in the
affine-line probability) and the *point* count `numberOfClosePts` (over the line itself, the form
bounded by AHIV's mutual-exclusion corollary). -/
lemma affineLine_close_count_eq_numberOfClosePts
    {deg : ℕ} {α : ι ↪ F} {e : ℕ} {u₀ u₁ : ι → F} (hu₁ : u₁ ≠ 0) :
    (Finset.filter (fun γ : F => Δ₀(u₀ + γ • u₁, ReedSolomon.code α deg) ≤ e)
        Finset.univ).card
      = numberOfClosePts (F := F) (ι := ι) u₀ u₁ deg α e := by
  classical
  rw [number_of_close_pts_eq_nat_card]
  -- `closePtsOnAffineLine` is finite; use `Nat.card` of the subtype.
  letI : Fintype
      (closePtsOnAffineLine (F := F) (u := u₀) (v := u₁) (deg := deg) (α := α) (e := e)) :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  -- Build the bijection `γ ↦ ⟨u₀ + γ • u₁, ...⟩`.
  apply Finset.card_bij
    (i := fun γ (hγ : γ ∈ Finset.filter
        (fun γ : F => Δ₀(u₀ + γ • u₁, ReedSolomon.code α deg) ≤ e) Finset.univ) =>
      (⟨u₀ + γ • u₁, by
        refine ⟨?_, ?_⟩
        · exact (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u₀) (direction := u₁)
            _).2 ⟨γ, rfl⟩
        · exact (Finset.mem_filter.mp hγ).2⟩ :
        closePtsOnAffineLine (F := F) (u := u₀) (v := u₁) (deg := deg) (α := α) (e := e)))
  · -- maps into the target finset (`univ`)
    intro γ hγ; exact Finset.mem_univ _
  · -- injective
    intro a ha b hb hab
    have hval : u₀ + a • u₁ = u₀ + b • u₁ := by
      simpa using congrArg (Subtype.val) hab
    exact affineLine_param_injective (u₀ := u₀) hu₁ hval
  · -- surjective
    intro x hx
    obtain ⟨γ, hγ⟩ := (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u₀)
      (direction := u₁) (x : ι → F)).1 x.2.1
    refine ⟨γ, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hγ]; exact x.2.2
    · apply Subtype.ext
      exact hγ.symm

/-- **AHIV17 per-line `d/q` probability bound (issue #88 core).**

Under the AHIV regime hypotheses (`e = ⌊δ·n⌋` with `e < ‖RS‖₀/3`, direction `u₁ ≠ 0`,
`‖RS‖₀ < |F|`, and not all points on the line being `e`-close), the affine-line probability is
at most `‖RScodeSet α deg‖₀ / |F|`.

This is the genuine `d/q` content the AHIV17 affine-line correlated-agreement bound rests on:
the count of close field elements is the per-line close-point count, bounded by `‖RS‖₀` through
the mutual-exclusion corollary `e_le_dist_over_3`. -/
lemma affineLine_prob_le_dOverQ
    {deg : ℕ} {α : ι ↪ F} {δ : ℝ≥0} {u₀ u₁ : ι → F}
    (he : ((Nat.floor (δ * Fintype.card ι) : ℕ) : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3)
    (hu₁ : u₁ ≠ 0)
    (hFd : ‖(RScodeSet α deg)‖₀ < Fintype.card F)
    (hNotAll : ¬ (∀ x ∈ Affine.affineLineAtOrigin (F := F) u₀ u₁,
        Δ₀(x, ReedSolomon.code α deg) ≤ (Nat.floor (δ * Fintype.card ι) : ℕ))) :
    Pr_{let γ ←$ᵖ F}[δᵣ(u₀ + γ • u₁, RScodeSet α deg) ≤ δ]
      ≤ (((‖(RScodeSet α deg)‖₀ : ℝ≥0) / (Fintype.card F : ℝ≥0)) : ENNReal) := by
  classical
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he_def
  -- Step 1: rewrite the probability as a count over `|F|`.
  have hPr :
      Pr_{let γ ←$ᵖ F}[δᵣ(u₀ + γ • u₁, RScodeSet α deg) ≤ δ]
        = (((Finset.filter
              (fun γ : F => δᵣ(u₀ + γ • u₁, RScodeSet α deg) ≤ δ) Finset.univ).card : ℝ≥0)
            / (Fintype.card F : ℝ≥0) : ENNReal) :=
    prob_uniform_eq_card_filter_div_card
      (P := fun γ : F => δᵣ(u₀ + γ • u₁, RScodeSet α deg) ≤ δ)
  rw [hPr]
  -- Step 2+3: the `δᵣ ≤ δ` count equals the `Δ₀ ≤ e` count, which is `numberOfClosePts`.
  have hcount :
      (Finset.filter
          (fun γ : F => δᵣ(u₀ + γ • u₁, RScodeSet α deg) ≤ δ) Finset.univ).card
        = numberOfClosePts (F := F) (ι := ι) u₀ u₁ deg α e := by
    rw [← affineLine_close_count_eq_numberOfClosePts (u₀ := u₀) (u₁ := u₁) (e := e) hu₁]
    congr 1
    apply Finset.filter_congr
    intro γ _
    rw [Code.relDistFromCode_le_iff_distFromCode_le (u := u₀ + γ • u₁) (δ := δ)]
  rw [hcount]
  -- Step 4: `numberOfClosePts ≤ ‖RS‖₀` from AHIV mutual exclusion.
  have hxor :=
    e_le_dist_over_3 (F := F) (ι := ι) (deg := deg) (α := α) (e := e)
      (u := u₀) (v := u₁) (by simpa [he_def] using he) hu₁ hFd
  have hfew : numberOfClosePts (F := F) (ι := ι) u₀ u₁ deg α e ≤ ‖(RScodeSet α deg)‖₀ := by
    rcases hxor with ⟨hall, _⟩ | ⟨hfew, _⟩
    · exact absurd hall hNotAll
    · exact hfew
  -- Step 5: conclude the division inequality (monotone in the numerator).
  have hnum :
      ((numberOfClosePts (F := F) (ι := ι) u₀ u₁ deg α e : ℝ≥0)
          / (Fintype.card F : ℝ≥0))
        ≤ ((‖(RScodeSet α deg)‖₀ : ℝ≥0) / (Fintype.card F : ℝ≥0)) := by
    have : (numberOfClosePts (F := F) (ι := ι) u₀ u₁ deg α e : ℝ≥0)
        ≤ (‖(RScodeSet α deg)‖₀ : ℝ≥0) := by exact_mod_cast hfew
    gcongr
  exact_mod_cast hnum

end ProximityToRS

#print axioms ProximityToRS.affineLine_param_injective
#print axioms ProximityToRS.affineLine_close_count_eq_numberOfClosePts
#print axioms ProximityToRS.affineLine_prob_le_dOverQ
