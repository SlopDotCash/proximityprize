/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-! # Agreement between the canonical and final-step folding relations -/

namespace Binius.BinaryBasefold
noncomputable section
open AdditiveNTT

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical final relation and the final-step state differ only in index presentation. -/
lemma finalNonDoomedFoldingProp_eq_finalSumcheckStepFoldingStateProp
    (stmt : BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (os : ∀ j, BinaryBasefold.OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) :
    BinaryBasefold.finalNonDoomedFoldingProp 𝔽q β
      (h_le := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (stmt, os) =
    BinaryBasefold.finalSumcheckStepFoldingStateProp 𝔽q β
      (h_le := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (stmt, os) := by
  have hle : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
  have hj : mkLastOracleIndex ℓ ϑ (Fin.last ℓ) =
      getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) := by
    apply Fin.ext
    rw [mkLastOracleIndex_last, getLastOraclePositionIndex_last]
  have hk : (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
      Nat.div_mul_cancel hdiv.out, Nat.sub_add_cancel hle]
  unfold finalNonDoomedFoldingProp finalSumcheckStepFoldingStateProp
    finalSumcheckStepOracleConsistencyProp
  dsimp only
  simp only [id_eq, blockBadEventExistsProp, badEventExistsProp]
  congr 2; congr 1
  all_goals try simp only [hj, hk]
  · exact proof_irrel_heq _ _
  · exact proof_irrel_heq _ _
  · exact OracleStatement.oracle_heq_congr 𝔽q β os hj
  · apply Function.hfunext
    · exact congrArg (fun i : Fin r => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i))
        (Fin.ext hk.symm)
    · intro a b hab
      rfl
  · funext c
    unfold getFoldingChallenges
    congr 1
    apply Fin.ext
    simp only [hj]

end
end Binius.BinaryBasefold
