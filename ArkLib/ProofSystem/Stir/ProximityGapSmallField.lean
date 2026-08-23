/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.ProximityGapProof
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CorrelatedAgreementSmallField

namespace STIR

open ReedSolomon ProximityGap Code NNReal ProbabilityTheory
open scoped BigOperators ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {φ : ι ↪ F}

/-- **STIR proximity-gap theorem (Theorem 4.1), UNCONDITIONAL in the small-field regime
`q ≤ (m−1)·n`.** The residual-free counterpart of `proximity_gap_of_residuals`: the
BCIKS20 list-decoding residuals are replaced by the landed vacuous-regime curve theorem
`correlatedAgreement_affine_curves_of_card_le`. -/
theorem proximity_gap_of_card_le
    {degree m : ℕ} [NeZero degree] {δ : ℝ≥0} {f : Fin m → ι → F} {GenFun : F → Fin m → F}
    (hm : 1 ≤ m)
    (hGen : ∀ r j, GenFun r j = r ^ (j : ℕ))
    (hδLt : δ < 1 - ReedSolomon.sqrtRate degree φ)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m - 1 : ℕ) : ℝ≥0) * (Fintype.card ι : ℝ≥0))
    (hProb :
      Pr_{ let r ← $ᵖ F}[δᵣ((fun x => ∑ j : Fin m, (GenFun r j) * f j x), code φ degree) ≤ δ] >
        ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) :
    ∃ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι) ∧
      ∀ i : Fin m, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  rw [Nat.add_sub_cancel] at hq
  have hJA : jointAgreement (F := F) (κ := Fin (k + 1)) (ι := ι)
      (C := (↑(code φ degree) : Set (ι → F))) (δ := δ) (W := f) := by
    refine correlatedAgreement_affine_curves_of_card_le
      (k := k) (deg := degree) (domain := φ) (δ := δ) hδLt hq f ?_
    have hword : ∀ r : F, (fun x => ∑ j : Fin (k + 1), GenFun r j * f j x)
        = (∑ j : Fin (k + 1), (r ^ (j : ℕ)) • f j) := by
      intro r; funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ => by rw [hGen])
    have hPr :
        Pr_{ let r ← $ᵖ F}[δᵣ(∑ j : Fin (k + 1), (r ^ (j : ℕ)) • f j, code φ degree) ≤ δ]
          = Pr_{ let r ← $ᵖ F}[δᵣ((fun x => ∑ j : Fin (k + 1), GenFun r j * f j x),
              code φ degree) ≤ δ] := by
      simp_rw [hword]
    rw [hPr]
    refine lt_of_le_of_lt ?_ hProb
    rw [ENNReal.ofReal_coe_nnreal]
    have hbridge := STIR.mul_errorBound_le_proximityError
      (deg := degree) (m := k + 1) (domain := φ) (δ := δ)
    rw [show ((↑(k + 1) : ℝ≥0) - 1) = (↑k : ℝ≥0) from by
      rw [Nat.cast_add_one, add_tsub_cancel_right]] at hbridge
    calc ((k : ℕ) : ENNReal) * (↑(ProximityGap.errorBound δ degree φ) : ENNReal)
        = ↑((↑k : ℝ≥0) * ProximityGap.errorBound δ degree φ) := by
          rw [ENNReal.coe_mul, ENNReal.coe_natCast]
      _ ≤ ↑(proximityError F degree (LinearCode.rate (code φ degree)) δ (k + 1)) :=
          ENNReal.coe_le_coe.mpr hbridge
  rw [jointAgreement_iff_forall_exists] at hJA
  simpa only [SetLike.mem_coe] using hJA

end STIR

#print axioms STIR.proximity_gap_of_card_le
