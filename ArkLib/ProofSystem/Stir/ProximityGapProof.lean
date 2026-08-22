/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ProofSystem.Stir.ErrorBoundBridge
import ArkLib.ProofSystem.Stir.ProximityGap

/-!
# STIR proximity gap, proved from the BCIKS20 keystone

The STIR front-door `STIR.proximity_gap` (Theorem 4.1 [BCIKS20] as stated in STIR) was previously
an inert `Prop` statement. This file proves it (`STIR.proximity_gap_of_residuals`) from the
in-tree BCIKS keystone `ProximityGap.correlatedAgreement_affine_curves`, instantiated at the power
generator `GenFun r j = r^j`, with the proximity threshold bridged via
`STIR.mul_errorBound_le_proximityError`. It is therefore of the same "complete modulo the two
BCIKS Johnson-regime residuals (`StrictCoeffPolysResidual`, `BoundaryProbabilityResidual`)" status
as the rest of the STIR/WHIR formalization.
-/

open NNReal ProbabilityTheory ReedSolomon Code
open scoped ENNReal

namespace STIR

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}

/-- **STIR proximity-gap theorem (conditional on the BCIKS20 list-decoding residuals).** -/
theorem proximity_gap_of_residuals
    {degree m : ℕ} [NeZero degree] {δ : ℝ≥0} {f : Fin m → ι → F} {GenFun : F → Fin m → F}
    (hm : 1 ≤ m)
    (hGen : ∀ r j, GenFun r j = r ^ (j : ℕ))
    (hδLt : δ ≤ 1 - ReedSolomon.sqrtRate degree φ)
    (hStrict : ∀ k, ProximityGap.StrictCoeffPolysResidual
      (k := k) (deg := degree) (domain := φ) (δ := δ))
    (hBoundary : ∀ k, ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := degree) (domain := φ) (δ := δ))
    (hProb :
      Pr_{ let r ← $ᵖ F}[δᵣ((fun x => ∑ j : Fin m, (GenFun r j) * f j x), code φ degree) ≤ δ] >
        ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) :
    ∃ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι) ∧
      ∀ i : Fin m, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have hJA : jointAgreement (F := F) (κ := Fin (k + 1)) (ι := ι)
      (C := (↑(code φ degree) : Set (ι → F))) (δ := δ) (W := f) := by
    refine ProximityGap.correlatedAgreement_affine_curves
      (k := k) (deg := degree) (domain := φ) (δ := δ) (hStrict k) (hBoundary k) hδLt f ?_
    -- the curve word coincides with the keystone power-sum word
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
    -- ↑k * ↑errorBound ≤ ofReal(proximityError)
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
