/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorHamming

/-!
## Pre-tensor unique-decoding radius arithmetic

This file isolates the numeric part of Lemma 4.22: the `fiberwiseClose` hypothesis places the
fiberwise distance below the destination code's unique-decoding radius.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}

/-- The destination half of `fiberwiseClose` is exactly the UDR inequality needed for the
interleaved-code proximity witness. -/
lemma fiberwiseDistance_le_uniqueDecodingRadius_of_fiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := by
        simpa using h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i ≤
      Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))) := by
  let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  have h_dist_pos : 0 <
      ‖(C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))‖₀ := by
    have h_pos : 0 <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
      simp [BBF_CodeDistance_eq (L := L) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)]
    simpa [C_dest, BBF_CodeDistance] using h_pos
  haveI : NeZero
      ‖(C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))‖₀ :=
    NeZero.of_pos h_dist_pos
  exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_dest)).2 (by
    simpa [C_dest, BBF_CodeDistance] using h_close.2)

end
end Binius.BinaryBasefold
