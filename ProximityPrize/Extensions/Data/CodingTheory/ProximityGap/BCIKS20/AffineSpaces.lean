/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main
import ProximityPrize.Compatibility.UniformProbability
import Mathlib.LinearAlgebra.Dimension.Free
import ArkLib.Data.CodingTheory.GuruswamiSudan
import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.Basic
import ProximityPrize.Extensions.Data.CodingTheory.DivergenceOfSets
import ProximityPrize.Extensions.Data.Polynomial.RationalFunctions
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.Polynomial.Trivariate
import ArkLib.Data.CodingTheory.Basic.DecodingRadius

/-!
# BCIKS20 §6 — from affine lines to affine/linear subspaces

This file lifts the affine-line correlated-agreement results to higher-dimensional affine and
linear subspaces. It records the probabilistic averaging tools (`exists_of_weighted_avg_gt`,
`prob_uniform_congr_equiv`, `prob_uniform_shift_invariant`), the basepoint-selection lemmas
(`exists_basepoint_with_large_line_prob_aux`, `exists_basepoint_with_large_line_prob`), and the
joint-agreement-to-proximity steps (`jointAgreement_implies_second_proximity`,
`jointAgreement_implies_linSpan_proximity`), culminating in
`average_proximity_implies_proximity_of_linear_subspace`.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory ReedSolomon Code
open scoped BigOperators LinearCode ProbabilityTheory

section BCIKS20ProximityGapSection6

open scoped ReedSolomon

variable {l : ℕ} [NeZero l]
variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem exists_of_weighted_avg_gt {α : Type} (p : PMF α) (f : α → ENNReal) (ε : ENNReal) :
    (∑' a, p a * f a) > ε → ∃ a, f a > ε := by
  intro hgt
  by_contra hno
  have hle : ∀ a, f a ≤ ε := by
    intro a
    have : ¬ f a > ε := by
      intro ha
      exact hno ⟨a, ha⟩
    exact le_of_not_gt this
  have hmul : ∀ a, p a * f a ≤ p a * ε := by
    intro a
    exact mul_le_mul_of_nonneg_left (hle a) (bot_le : (0 : ENNReal) ≤ p a)
  have htsum : (∑' a, p a * f a) ≤ ∑' a, p a * ε := by
    exact ENNReal.tsum_le_tsum hmul
  have htsum' : (∑' a, p a * f a) ≤ ε := by
    refine le_trans htsum ?_
    simp [ENNReal.tsum_mul_right, p.tsum_coe]
  exact (not_lt_of_ge htsum') hgt

theorem prob_uniform_congr_equiv {α : Type} [Fintype α] [Nonempty α]
    (e : α ≃ α) (P : α → Prop) :
    Pr_{let x ←$ᵖ α}[P (e x)] = Pr_{let x ←$ᵖ α}[P x] := by
  classical
  rw [ProximityPrize.Compatibility.pmf_uniform_probability_eq_card (α := α) (p := fun x => P (e x))]
  rw [ProximityPrize.Compatibility.pmf_uniform_probability_eq_card (α := α) (p := P)]
  have hcard : (Finset.filter (fun x : α => P (e x)) Finset.univ).card =
      (Finset.filter (fun x : α => P x) Finset.univ).card := by
    classical
    refine Finset.card_bij (s := Finset.filter (fun x : α => P (e x)) Finset.univ)
      (t := Finset.filter (fun x : α => P x) Finset.univ)
      (i := fun a ha => e a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp [Finset.mem_filter, ha]
    · intro a1 ha1 a2 ha2 h
      exact e.injective h
    · intro b hb
      refine ⟨e.symm b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        simp [Finset.mem_filter, hb]
      · simp
  simp [hcard]

end BCIKS20ProximityGapSection6

section AffineFinsetBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- The AffineSubspace and Finset.image representations of an affine subspace
have the same membership. -/
private theorem affine_mem_iff_finset_mem {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) (x : ι → F) :
    x ∈ (Affine.affineSubspaceAtOrigin (F := F) u0 dirs : Set (ι → F)) ↔
    x ∈ (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)).toFinset.image
      (fun d => u0 + d) := by
  classical
  simp only [Affine.affineSubspaceAtOrigin,
    Finset.mem_image, Set.mem_toFinset]
  constructor
  · intro h; exact ⟨x - u0, h, by abel⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

private noncomputable abbrev affineFinset {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) : Finset (ι → F) :=
  (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)).toFinset.image
    (fun d => u0 + d)

private noncomputable def affineFinsetEquiv {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) :
    (Affine.affineSubspaceAtOrigin (F := F) u0 dirs) ≃ (affineFinset u0 dirs) :=
  Equiv.subtypeEquiv (Equiv.refl _) (affine_mem_iff_finset_mem u0 dirs)

end AffineFinsetBridge

section ScalingInvariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

end ScalingInvariance

section AllClose

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- When `u₀ ∉ U'`, `span(range u) = span {u₀} ⊔ U'`. -/
private lemma spanU_eq_sup {k : ℕ} (u : Fin (k + 1) → ι → F)
    (U' : Submodule F (ι → F))
    (hU' : U' = Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)))
    (hU'_le : U' ≤ Submodule.span F (Set.range u)) :
    Submodule.span F (Set.range u) = Submodule.span F {u 0} ⊔ U' := by
  apply le_antisymm
  · apply Submodule.span_le.mpr; rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Submodule.mem_sup_left (Submodule.subset_span rfl)
    · exact Submodule.mem_sup_right (hU' ▸ Submodule.subset_span
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  · exact sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (Submodule.subset_span ⟨0, rfl⟩))) hU'_le

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Every element of `span(range u)` decomposes as `c • u₀ + d` with `d ∈ U'`. -/
private lemma mem_spanU_decomp {k : ℕ} (u : Fin (k + 1) → ι → F)
    (U' : Submodule F (ι → F))
    (hU' : U' = Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)))
    (hU'_le : U' ≤ Submodule.span F (Set.range u))
    {x : ι → F} (hx : x ∈ Submodule.span F (Set.range u)) :
    ∃ c : F, ∃ d ∈ U', x = c • u 0 + d := by
  rw [spanU_eq_sup u U' hU' hU'_le, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  exact ⟨c, b, hb, rfl⟩

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- If `u₀ ∉ U'` and `a • u₀ + d₁ = b • u₀ + d₂` with `d₁ d₂ ∈ U'`, then `a = b`. -/
private lemma coset_scalar_eq {u₀ : ι → F} {U' : Submodule F (ι → F)}
    (hu0 : u₀ ∉ U') {a b : F} {d₁ d₂ : ι → F} (hd₁ : d₁ ∈ U') (hd₂ : d₂ ∈ U')
    (h : a • u₀ + d₁ = b • u₀ + d₂) : a = b := by
  by_contra hab
  apply hu0
  have h1 : (a - b) • u₀ = d₂ - d₁ := by
    rw [sub_smul]
    calc a • u₀ - b • u₀
        = (a • u₀ + d₁) - d₁ - b • u₀ := by abel
      _ = (b • u₀ + d₂) - d₁ - b • u₀ := by rw [h]
      _ = d₂ - d₁ := by abel
  rw [show u₀ = (a - b)⁻¹ • ((a - b) • u₀) from by
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul], h1]
  exact U'.smul_mem _ (U'.sub_mem hd₂ hd₁)



end AllClose

private theorem exists_large_of_finset_cover' {α : Type}
    {U : Finset α} {L : ℕ} {buckets : Fin L → Finset α}
    (hcover : ∀ x ∈ U, ∃ i, x ∈ buckets i)
    {B : ℕ} (hLB : L * B < U.card) :
    ∃ i, B < (buckets i).card := by
  classical
  by_contra hall
  push Not at hall
  have hle : U.card ≤ L * B := by
    calc U.card
        ≤ (Finset.univ.biUnion buckets).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, hi⟩ := hcover x hx
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
      _ ≤ ∑ i : Fin L, (buckets i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin L, B := Finset.sum_le_sum (fun i _ => hall i)
      _ = L * B := by simp [Finset.sum_const]
  exact absurd hle (not_le.mpr hLB)


section Bucketing

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

end Bucketing

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Degree-bound numerator step: `(m + 1/2) * s * n / (deg - 1) ≤ 5 / (4 * μ)`.
Extracted from `exists_gs_multiplicity` to reduce heartbeat pressure. -/
private lemma gs_degree_bound_le_inv_mu
    {s η : ℝ} {m deg : ℕ} {n : ℕ}
    (hs_pos : 0 < s) (hη_pos : 0 < η)
    (hs_sq : s ^ 2 = (deg : ℝ) / n) (hn_pos : (0 : ℝ) < n)
    (hdeg : 1 < deg)
    (hm_bound : (m : ℝ) + 1 / 2 ≤ s / (2 * η) + 5 / 2)
    (μ : ℝ) (hμ_pos : 0 < μ) (hμ_le_η : μ ≤ η) (hμ_le_s20 : μ ≤ s / 20) :
    (↑m + 1/2) * s * (n : ℝ) / (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / (4 * μ) := by
  have hdeg1 : 0 < deg - 1 := by omega
  have hdeg_pos : (0 : ℝ) < deg := by exact_mod_cast (show 0 < deg by omega)
  have hdeg1_cast_eq : (↑(deg - 1 : ℕ) : ℝ) = (deg : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ deg), Nat.cast_one]
  have hdeg1_ge : (↑(deg - 1 : ℕ) : ℝ) ≥ (deg : ℝ) / 2 := by
    rw [hdeg1_cast_eq]; linarith [show (2 : ℝ) ≤ deg from by exact_mod_cast hdeg]
  have h_num : (↑m + 1/2) * s * (n : ℝ) ≤
      (deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s) := by
    have h1 : (↑m + 1/2) * s * (n : ℝ) ≤
        (s / (2 * η) + 5/2) * s * (n : ℝ) := by
        have : (0 : ℝ) ≤ s * n := mul_nonneg hs_pos.le hn_pos.le
        nlinarith [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hm_bound hs_pos.le) hn_pos.le]
    have hsqn : s ^ 2 * (n : ℝ) = (deg : ℝ) := by
      have := hs_sq; field_simp at this; linarith
    have h2 : (s / (2 * η) + 5/2) * s * (n : ℝ) =
        (deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s) := by
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hη_ne : η ≠ 0 := ne_of_gt hη_pos
      field_simp
      nlinarith [hsqn, mul_comm s (n : ℝ)]
    linarith
  have hdeg_le_2d1 : (deg : ℝ) ≤ 2 * ↑(deg - 1 : ℕ) := by linarith [hdeg1_ge]
  have h3 : (deg : ℝ) / (2 * η) / (↑(deg - 1 : ℕ) : ℝ) ≤ 1 / η := by
    have hd1_pos : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
    rw [div_div, div_le_div_iff₀ (mul_pos (by positivity) hd1_pos) hη_pos, one_mul]
    nlinarith
  have h4 : 5 * (deg : ℝ) / (2 * s) / (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / s := by
    have hd1_pos : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
    rw [div_div, div_le_div_iff₀ (mul_pos (by positivity) hd1_pos) hs_pos]
    nlinarith
  have h5 : 1 / η ≤ 1 / μ := by
    rw [div_le_div_iff₀ hη_pos hμ_pos]; linarith [hμ_le_η]
  have h6 : 5 / s ≤ 1 / (4 * μ) := by
    rw [div_le_div_iff₀ hs_pos (by positivity : (0:ℝ) < 4 * μ)]
    linarith [hμ_le_s20]
  calc (↑m + 1/2) * s * (n : ℝ) / (↑(deg - 1 : ℕ) : ℝ)
      ≤ ((deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s)) / (↑(deg - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right h_num (by positivity)
    _ = (deg : ℝ) / (2 * η) / (↑(deg - 1 : ℕ) : ℝ) +
        5 * (deg : ℝ) / (2 * s) / (↑(deg - 1 : ℕ) : ℝ) := add_div _ _ _
    _ ≤ 1 / η + 5 / s := add_le_add h3 h4
    _ ≤ 1 / μ + 1 / (4 * μ) := add_le_add h5 h6
    _ = 5 / (4 * μ) := by ring

/-- Theorem 1.7 front door with the affine-line Johnson residual supplied by the verified
`betaRec` capsule at every radius `δ' ≤ δ` used internally by the affine-space proof. -/
theorem correlatedAgreement_affine_spaces_johnson_of_betaRec [SampleableType F] {k : ℕ} [NeZero k]
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hδ_pos : 0 < δ)
    (hInput : ∀ δ' : ℝ≥0, δ' ≤ δ →
      ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ'] >
            (((1 : ℕ) : ENNReal) * (errorBound δ' deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ' →
        δ' < 1 - ReedSolomon.sqrtRate deg domain →
        ArkLib.KeystoneStrictResidual.BetaCurveInput
          (k := 1) (deg := deg) (domain := domain) (δ := δ') u)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1) :
    δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  -- The canonical theorem is stronger; the retained legacy residual input is unused.
  correlatedAgreement_affine_spaces (ι := ι) (F := F) (k := k) (deg := deg)
    (domain := domain) (δ := δ) hdeg hδ_pos hδ hRS hε

/-- Theorem 1.7 front door with the strict Johnson residual split at the boundary.

The affine-space proof needs the line-level strict coefficient residual for every
`δ' ≤ δ`: strict subradii come from the verified `betaRec` capsule, while the
exact boundary radius is kept as the single explicit residual.  This avoids
asking callers to produce the strict-interior `betaRec` input at the endpoint
where boundary-card/lattice phenomena are handled separately. -/
theorem correlatedAgreement_affine_spaces_johnson_of_betaRec_strict_boundary [SampleableType F]
    {k : ℕ} [NeZero k] {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hδ_pos : 0 < δ)
    (hInputStrict : ∀ δ' : ℝ≥0, δ' < δ →
      ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ'] >
            (((1 : ℕ) : ENNReal) * (errorBound δ' deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ' →
        δ' < 1 - ReedSolomon.sqrtRate deg domain →
        ArkLib.KeystoneStrictResidual.BetaCurveInput
          (k := 1) (deg := deg) (domain := domain) (δ := δ') u)
    (hBoundaryStrict :
      ProximityGap.StrictCoeffPolysResidual (k := 1) (deg := deg)
        (domain := domain) (δ := δ))
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1) :
    δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  -- The canonical theorem is stronger; the retained legacy residual input is unused.
  correlatedAgreement_affine_spaces (ι := ι) (F := F) (k := k) (deg := deg)
    (domain := domain) (δ := δ) hdeg hδ_pos hδ hRS hε

/-- Theorem 1.7 front door with the affine-line Johnson residual supplied by the finite-range
verified `betaRec` capsule at every radius `δ' ≤ δ` used internally by the affine-space proof. -/
theorem correlatedAgreement_affine_spaces_johnson_of_betaRecFin [SampleableType F] {k : ℕ} [NeZero k]
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hδ_pos : 0 < δ)
    (hInput : ∀ δ' : ℝ≥0, δ' ≤ δ →
      ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ'] >
            (((1 : ℕ) : ENNReal) * (errorBound δ' deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ' →
        δ' < 1 - ReedSolomon.sqrtRate deg domain →
        ArkLib.KeystoneStrictResidual.BetaCurveInputFin
          (k := 1) (deg := deg) (domain := domain) (δ := δ') u)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1) :
    δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  -- The canonical theorem is stronger; the retained legacy residual input is unused.
  correlatedAgreement_affine_spaces (ι := ι) (F := F) (k := k) (deg := deg)
    (domain := domain) (δ := δ) hdeg hδ_pos hδ hRS hε

/-- Theorem 1.7 front door with the finite-range strict Johnson residual split at the boundary.

Strict subradii come from the verified `BetaCurveInputFin` capsule; the exact boundary radius stays
as the single explicit strict-coefficient residual. -/
theorem correlatedAgreement_affine_spaces_johnson_of_betaRecFin_strict_boundary [SampleableType F]
    {k : ℕ} [NeZero k] {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hδ_pos : 0 < δ)
    (hInputStrict : ∀ δ' : ℝ≥0, δ' < δ →
      ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ'] >
            (((1 : ℕ) : ENNReal) * (errorBound δ' deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ' →
        δ' < 1 - ReedSolomon.sqrtRate deg domain →
        ArkLib.KeystoneStrictResidual.BetaCurveInputFin
          (k := 1) (deg := deg) (domain := domain) (δ := δ') u)
    (hBoundaryStrict :
      ProximityGap.StrictCoeffPolysResidual (k := 1) (deg := deg)
        (domain := domain) (δ := δ))
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1) :
    δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  -- The canonical theorem is stronger; the retained legacy residual input is unused.
  correlatedAgreement_affine_spaces (ι := ι) (F := F) (k := k) (deg := deg)
    (domain := domain) (δ := δ) hdeg hδ_pos hδ hRS hε

end CoreResults

end ProximityGap

set_option linter.style.longFile 2500

#print axioms ProximityGap.correlatedAgreement_affine_spaces_johnson_of_betaRec

#print axioms ProximityGap.correlatedAgreement_affine_spaces_johnson_of_betaRec_strict_boundary

#print axioms ProximityGap.correlatedAgreement_affine_spaces_johnson_of_betaRecFin

#print axioms ProximityGap.correlatedAgreement_affine_spaces_johnson_of_betaRecFin_strict_boundary
