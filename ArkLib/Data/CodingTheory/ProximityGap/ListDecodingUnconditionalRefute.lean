/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListDecodingConjectureRefutation
import ArkLib.Data.CodingTheory.ListDecoding.Bounds

set_option exponentiation.threshold 2000
set_option maxRecDepth 2000000

namespace ProximityGap.ListDecodingUnconditionalRefute

open scoped NNReal ENNReal
open CodingTheory ListDecodable

theorem rs_lambda_ge_elias_volume
    {ι F : Type} [Field F] [Fintype F] [Fintype ι] [Nonempty ι]
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hkcard : k ≤ Fintype.card ι) :
    ENNReal.ofReal (
      (hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℝ) /
      (Fintype.card F : ℝ) ^ (Fintype.card ι - k : ℕ)
    ) ≤ (Lambda (ReedSolomon.code α k : Set (ι → F)) δ : ENNReal) := by
  classical
  have hdim : Module.finrank F (ReedSolomon.code α k) = k :=
    ReedSolomon.dim_eq_deg_of_le' hkcard
  have h := linear_lambda_ge_elias_volume_eli57 (ι := ι) (F := F) (ReedSolomon.code α k) δ hδ_pos hδ_lt
  rw [hdim] at h
  exact_mod_cast h

lemma floor_120 : ⌊(120 / 128 : ℝ) * (128 : ℕ)⌋₊ = 120 := by norm_num

/-- Unconditional refutation of the up-to-capacity list decoding bound.
There exists a field F of size 512, domain of size 128, k=7, and δ=120/128 < 1-7/128,
where the list size exceeds the prize threshold ε* |F|. -/
theorem rs_listDecoding_unconditional_refute
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 512)
    (α : Fin 128 ↪ F) :
    let C := (ReedSolomon.code α 7 : Set (Fin 128 → F))
    let δ : ℝ := 120 / 128
    let ε_star : ℝ≥0 := 1 / 2^128
    (δ < 1 - (7 : ℝ) / 128) ∧
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal) < (Lambda C δ : ENNReal)) := by
  classical
  intro C δ ε_star
  refine ⟨by norm_num, ?_⟩
  have hδ_pos : (0 : ℝ) < δ := by norm_num
  have hδ_lt : (δ : ℝ) < 1 := by norm_num
  have hkcard : 7 ≤ Fintype.card (Fin 128) := by rw [Fintype.card_fin]; norm_num
  have hl := rs_lambda_ge_elias_volume α 7 δ hδ_pos hδ_lt hkcard
  refine lt_of_lt_of_le ?_ hl

  have h_vol : hammingBallVolume 512 (120 / 128 : ℝ) 128 = 15038444377787151650375685174672066866184745648104990144801868042631311965349583186687113127436881863901183439685096266306134014845093896518687887500318643741231245706972137096355926069772282796303516592374232422397286597635243040152624139714724822095620997714592598555826889405216067258998463940758959084232627994908541115856290575725343 := by
    rw [hammingBallVolume, floor_120]
    decide

  have h_nat_ineq : (2^1098 : ℕ) < (15038444377787151650375685174672066866184745648104990144801868042631311965349583186687113127436881863901183439685096266306134014845093896518687887500318643741231245706972137096355926069772282796303516592374232422397286597635243040152624139714724822095620997714592598555826889405216067258998463940758959084232627994908541115856290575725343 : ℕ) * 2^128 := by norm_num

  have h_real_ineq : (2^1098 : ℝ) < (15038444377787151650375685174672066866184745648104990144801868042631311965349583186687113127436881863901183439685096266306134014845093896518687887500318643741231245706972137096355926069772282796303516592374232422397286597635243040152624139714724822095620997714592598555826889405216067258998463940758959084232627994908541115856290575725343 : ℝ) * 2^128 := by
    exact_mod_cast h_nat_ineq

  have h_frac_ineq : ((1:ℝ)/2^128) * 512 < (15038444377787151650375685174672066866184745648104990144801868042631311965349583186687113127436881863901183439685096266306134014845093896518687887500318643741231245706972137096355926069772282796303516592374232422397286597635243040152624139714724822095620997714592598555826889405216067258998463940758959084232627994908541115856290575725343 : ℝ) / (512:ℝ)^121 := by
    have h_pos1 : (0:ℝ) < 2^128 := by positivity
    have h_pos2 : (0:ℝ) < 512^121 := by positivity
    have h_rw : ((1:ℝ)/2^128) * 512 = 512 / 2^128 := by ring
    rw [h_rw]
    rw [div_lt_div_iff₀ h_pos1 h_pos2]
    have h_512 : (512:ℝ) * 512^121 = 2^1098 := by norm_num
    rwa [h_512]

  have h_lift : ENNReal.ofReal (((1:ℝ)/2^128) * 512) < ENNReal.ofReal ((15038444377787151650375685174672066866184745648104990144801868042631311965349583186687113127436881863901183439685096266306134014845093896518687887500318643741231245706972137096355926069772282796303516592374232422397286597635243040152624139714724822095620997714592598555826889405216067258998463940758959084232627994908541115856290575725343:ℝ) / (512:ℝ)^121) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact h_frac_ineq

  have h_lhs : (ε_star : ENNReal) * (Fintype.card F : ENNReal) = ENNReal.ofReal (((1:ℝ)/2^128) * 512) := by
    rw [hF]
    have h_star : (ε_star : ENNReal) = ENNReal.ofReal ((1:ℝ)/2^128) := by
      exact (ENNReal.ofReal_coe_nnreal).symm
    rw [h_star]
    have h_512 : (↑(512 : ℕ) : ENNReal) = ENNReal.ofReal 512 := by exact (ENNReal.ofReal_natCast 512).symm
    rw [h_512]
    exact (ENNReal.ofReal_mul (by positivity)).symm

  have h_rhs : ENNReal.ofReal ((15038444377787151650375685174672066866184745648104990144801868042631311965349583186687113127436881863901183439685096266306134014845093896518687887500318643741231245706972137096355926069772282796303516592374232422397286597635243040152624139714724822095620997714592598555826889405216067258998463940758959084232627994908541115856290575725343:ℝ) / (512:ℝ)^121) = ENNReal.ofReal (↑(hammingBallVolume 512 (120 / 128) 128) / (512 : ℝ) ^ (128 - 7 : ℕ)) := by
    rw [h_vol]
    have h_sub : (128 - 7 : ℕ) = 121 := rfl
    rw [h_sub]
    push_cast
    rfl
  have h_rhs2 : ENNReal.ofReal (↑(hammingBallVolume 512 (120 / 128) 128) / (512 : ℝ) ^ (128 - 7 : ℕ)) = ENNReal.ofReal (↑(hammingBallVolume (Fintype.card F) δ (Fintype.card (Fin 128))) / ↑(Fintype.card F) ^ (Fintype.card (Fin 128) - 7 : ℕ)) := by
    rw [hF]
    rfl

  rw [← h_lhs, h_rhs, h_rhs2] at h_lift
  exact h_lift

end ProximityGap.ListDecodingUnconditionalRefute
