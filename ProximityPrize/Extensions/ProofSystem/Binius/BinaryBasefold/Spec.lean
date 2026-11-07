/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Basic

/-! ## Protocol Specs for Binary Basefold
This module contains the protocol specs, oracle index bounds,
instances of OracleInterface and SampleableType for the Binary Basefold protocol.
-/

namespace Binius.BinaryBasefold

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial AdditiveNTT
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section IndexBounds
-- Note: need a main lemma for bounds involving last bIdx = (ℓ / ϑ - 1)
omit [NeZero r] [NeZero 𝓡] in
lemma isNeCommitmentRound (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x < ϑ - 1} :
    ¬isCommitmentRound ℓ ϑ ⟨↑bIdx * ϑ + x, by
      conv_rhs => rw [←Nat.add_zero (n:=ℓ)]
      change bIdx.val * ϑ + (⟨x, by omega⟩: Fin ϑ).val < ℓ + 0
      apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=0)
    ⟩ := by
  exact not_isCommitmentRound_of_offset_lt (r := r) (𝓡 := 𝓡) (ℓ := ℓ) (ϑ := ϑ) bIdx x hx

lemma lastBlockIdx_isNeCommitmentRound (i : Fin ϑ) :
    ¬isCommitmentRound ℓ ϑ ⟨(ℓ / ϑ - 1) * ϑ + ↑i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ := by
  exact not_isCommitmentRound_lastBlock (ℓ := ℓ) (ϑ := ϑ) i

omit [NeZero r] [NeZero 𝓡] in
lemma isCommitmentRoundOfNonLastBlock (bIdx : Fin (ℓ / ϑ - 1)) :
    isCommitmentRound ℓ ϑ ⟨↑bIdx * ϑ + (ϑ - 1), by
      have hpos: ϑ > 0 := by exact Nat.pos_of_neZero ϑ
      conv_rhs => rw [←Nat.add_zero (n:=ℓ)]
      change bIdx.val * ϑ + (⟨ϑ - 1, by omega⟩: Fin ϑ).val < ℓ + 0
      apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=0)
    ⟩ := by
  exact isCommitmentRound_nonlastBlock (r := r) (𝓡 := 𝓡) (ℓ := ℓ) (ϑ := ϑ) bIdx

end IndexBounds

/- The canonical Spec owner supplies all message interfaces and native challenge samplers.
The former duplicate anonymous instances are removed. FinalSumcheckStep has no challenge index,
so the retired aggregate Fintype/Inhabited metadata was vacuous. -/

end
end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.isNeCommitmentRound
#print axioms Binius.BinaryBasefold.lastBlockIdx_isNeCommitmentRound
#print axioms Binius.BinaryBasefold.isCommitmentRoundOfNonLastBlock
