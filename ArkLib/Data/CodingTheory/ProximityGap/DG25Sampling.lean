/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.ToMathlib.UniformTranslationAverage
import ArkLib.Data.CodingTheory.InterleavedRowDistance

/-!
# DG25 L4.19 covering-radius sampling lower bound (issue #77)

This discharges the external `Prop` `CodingTheory.linear_epsCA_ge_sampling_dg25`
(ABF26 Lemma 4.19 / DG25 Theorem 2.5): for a linear code `C ⊆ Fⁿ` with covering radius
`δ' = ⨆_u δᵣ(u, C)` and `0 < δ < δ'`,

  `((|F|-1)/|F|) · Pr_{u}[δᵣ(u, C) ≤ δ]  ≤  ε_ca(C, δ)`.

## Proof

Pick a word `w` with `δ < δᵣ(w, C)` (`lt_iSup_iff`, since `δ < δ' = ⨆_u δᵣ(u,C)`). Then
`relDistFromCode_snd_le_of_jointProximity` shows no base word `u₀` makes `(u₀, w)` jointly
`δ`-close, so the `ε_ca` body at the pair `finMapTwoWords u₀ w` is the bare line probability
`Pr_γ[δᵣ(u₀ + γ·w, C) ≤ δ]` (never zeroed). Therefore

  `Pr_u[δᵣ(u,C) ≤ δ]  =  ∑_{u₀} |Fⁿ|⁻¹ · Pr_γ[δᵣ(u₀+γ·w,C) ≤ δ]`   (`sum_uniform_line_indicator_eq`)
                       `≤  ⨆_{u₀} Pr_γ[…]`                            (`sum_uniform_mul_le_iSup`)
                       `=  ⨆_{u₀} body(finMapTwoWords u₀ w)  ≤  ε_ca`  (`le_iSup`).

Finally `((|F|-1)/|F|) ≤ 1` gives the stated mass bound.
-/

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open ProximityGap ProbabilityTheory

namespace CodingTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The uniform-word covering probability is dominated by `ε_ca`. -/
theorem pr_relDist_le_epsCA_of_lt_covering
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_lt : δ < δ') :
    Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ]
      ≤ epsCA (F := F) (A := F) ((C : Set (ι → F))) δ δ := by
  classical
  -- a word beyond the covering radius
  have hlt : (δ : ENNReal) < ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))) := by
    rw [← h_δ']; exact_mod_cast hδ_lt
  obtain ⟨w, hw⟩ := lt_iSup_iff.mp hlt
  -- no base word forms a jointly-δ-close pair with w
  have hnojoint : ∀ u₀ : ι → F, ¬ Code.jointProximity (C : Set (ι → F)) (Code.finMapTwoWords u₀ w) δ :=
    fun u₀ hj => absurd (ArkLib.relDistFromCode_snd_le_of_jointProximity hj) (not_le.mpr hw)
  -- rewrite Pr_u as the uniform average of line probabilities
  have hPr_eq :
      Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ]
        = ∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
            Pr_{let γ ← $ᵖ F}[δᵣ(u₀ + γ • w, (C : Set (ι → F))) ≤ δ] := by
    simp_rw [ProbabilityTheory.Pr_eq_tsum_indicator, tsum_fintype, PMF.uniformOfFintype_apply]
    exact (ArkLib.sum_uniform_line_indicator_eq
      (fun u => Code.relDistFromCode u (C : Set (ι → F)) ≤ (δ : ENNReal)) w).symm
  rw [hPr_eq]
  refine le_trans (ArkLib.sum_uniform_mul_le_iSup _) (iSup_le (fun u₀ => ?_))
  have e0 : (Code.finMapTwoWords u₀ w) (0 : Fin 2) = u₀ := rfl
  have e1 : (Code.finMapTwoWords u₀ w) (1 : Fin 2) = w := rfl
  refine le_trans (le_of_eq ?_)
    (le_iSup (fun (u : Code.WordStack F (Fin 2) ι) =>
      if Code.jointProximity (C : Set (ι → F)) u δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, (C : Set (ι → F))) ≤ δ])
      (Code.finMapTwoWords u₀ w))
  rw [if_neg (hnojoint u₀), e0, e1]

/-- **ABF26 Lemma 4.19 / DG25 Theorem 2.5.** The covering-radius sampling lower bound for `ε_ca`. -/
theorem linear_epsCA_sampling_dg25_mass_le_epsCA
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_lt : δ < δ') :
    linear_epsCA_sampling_dg25_mass C δ
      ≤ epsCA (F := F) (A := F) ((C : Set (ι → F))) δ δ := by
  classical
  haveI : Nonempty F := ⟨0⟩
  refine le_trans ?_ (pr_relDist_le_epsCA_of_lt_covering C δ δ' h_δ' hδ_lt)
  unfold linear_epsCA_sampling_dg25_mass
  have hcardF : (0 : ℝ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcoeff : ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal) ≤ 1 := by
    have hrat : ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F) ≤ 1 := by
      rw [div_le_one hcardF]; exact tsub_le_self
    exact_mod_cast hrat
  calc ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ]
      ≤ 1 * Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ] := by gcongr
    _ = Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ] := one_mul _

/-- Discharge the external `Prop` front door for ABF26 L4.19 / DG25 Thm 2.5. -/
theorem linear_epsCA_ge_sampling_dg25_proof
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_pos : 0 < δ) (hδ_lt : δ < δ') :
    linear_epsCA_ge_sampling_dg25 C δ δ' h_δ' hδ_pos hδ_lt :=
  linear_epsCA_ge_sampling_dg25_of_mass_bound C δ δ' h_δ' hδ_pos hδ_lt
    (linear_epsCA_sampling_dg25_mass_le_epsCA C δ δ' h_δ' hδ_lt)

#print axioms CodingTheory.pr_relDist_le_epsCA_of_lt_covering
#print axioms CodingTheory.linear_epsCA_sampling_dg25_mass_le_epsCA
#print axioms CodingTheory.linear_epsCA_ge_sampling_dg25_proof

end CodingTheory
