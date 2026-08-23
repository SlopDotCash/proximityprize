/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SuffixAlignCore

/-!
## Binary Basefold Query-Phase Suffix Helpers

This module isolates the challenge-suffix/fiber alignment layer from the heavier query-phase
soundness helper file.  It provides the small public surface needed by later query-phase proofs
and by the issue #317 suffix/fiber alignment audit.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

noncomputable section

namespace QueryPhase

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1
  [NeZero r] [NeZero 𝓡] in
/-- For a block index `k < ℓ / ϑ` (with `ϑ ∣ ℓ`), the block end `k * ϑ + ϑ`
is `≤ ℓ`. -/
lemma k_succ_mul_ϑ_le_ℓ_₂ (k : Fin (ℓ / ϑ)) : k.val * ϑ + ϑ ≤ ℓ := by
  have hk : k.val + 1 ≤ ℓ / ϑ := k.isLt
  have h_div_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_mul_le : (k.val + 1) * ϑ ≤ (ℓ / ϑ) * ϑ := Nat.mul_le_mul_right ϑ hk
  rw [h_div_mul] at h_mul_le
  have h_expand : (k.val + 1) * ϑ = k.val * ϑ + ϑ := by ring
  omega

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1
  [NeZero r] [NeZero 𝓡] in
/-- For a block index `k < ℓ / ϑ` (with `ϑ ∣ ℓ`), the block start `k * ϑ`
is `< ℓ`. -/
lemma k_mul_ϑ_lt_ℓ (k : Fin (ℓ / ϑ)) : k.val * ϑ < ℓ := by
  have hϑ : 0 < ϑ := Nat.pos_of_neZero ϑ
  have h := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  omega

/-- Number of oracle blocks at the end of the protocol. -/
abbrev nBlocks : ℕ := toOutCodewordsCount ℓ ϑ (Fin.last ℓ)

/-- Extract suffix starting at position `destIdx` from a full challenge. -/
def extractSuffixFromChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ) :
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  have h_bound : (⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val + destIdx.val ≤ ℓ := by
    change 0 + destIdx.val ≤ ℓ
    rw [Nat.zero_add]; exact h_destIdx_le
  have h_idx_eq :
      (⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val + destIdx.val, by omega⟩ : Fin r) =
        destIdx := by
    apply Fin.eq_of_val_eq
    change 0 + destIdx.val = destIdx.val
    rw [Nat.zero_add]
  cast (congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx_eq)
    (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
      (k := destIdx.val) (h_bound := h_bound) (x := v))

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
/-- Congruence lemma for challenge suffixes across equal destination indices. -/
lemma extractSuffixFromChallenge_congr_destIdx
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    {destIdx destIdx' : Fin r}
    (h_idx_eq : destIdx = destIdx')
    (h_le : destIdx ≤ ℓ)
    (h_le' : destIdx' ≤ ℓ) :
    extractSuffixFromChallenge 𝔽q β v destIdx h_le =
    cast (by rw [h_idx_eq]) (extractSuffixFromChallenge 𝔽q β v destIdx' h_le') := by
  subst h_idx_eq
  rw [cast_eq]

def getChallengeSuffix (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    let i := k.val * ϑ
    have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    let destIdx : Fin r := ⟨i + ϑ, by omega⟩
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  have h_i_add_ϑ_le_ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by omega)

def challengeSuffixToFin (k : Fin (ℓ / ϑ))
    (suffix : sDomain 𝔽q β h_ℓ_add_R_rate ⟨k.val * ϑ + ϑ, by
    have := k_succ_mul_ϑ_le_ℓ_₂ (k := k); omega⟩) : Fin (2 ^ (ℓ + 𝓡 - (k.val * ϑ + ϑ))) :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  sDomainToFin 𝔽q β h_ℓ_add_R_rate (i := ⟨k.val * ϑ + ϑ, by omega⟩) (h_i := by
    simp only [k_succ_mul_ϑ_le_ℓ_₂, Nat.lt_add_of_pos_right_of_le]) suffix

/-- Return the point `f^(i)(u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})`
for a fiber index `u ∈ B_ϑ`. -/
noncomputable def getFiberPoint
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) (u : Fin (2 ^ ϑ)) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
      (positionIdx := ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩),
        lt_r_of_lt_ℓ (x := k.val * ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := k_mul_ϑ_lt_ℓ (k := k))⟩) :=
  by
    exact
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
        (steps := ϑ)
        (h_i_add_steps := by
          have h_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
          simp only [Fin.val_mk]; omega)
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v))
        u

end QueryPhase

section QueryPhaseSuffixLemmas

open QueryPhase

lemma getFiberPoint_eq_qMap_total_fiber
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (u : Fin (2 ^ ϑ)) :
    getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u =
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
        (steps := ϑ)
        (h_i_add_steps := by
          have h_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
          simp only [Fin.val_mk]; omega)
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) u := by
  unfold getFiberPoint
  simp only [oraclePositionToDomainIndex, id_eq]

/-- The challenge suffix at block source `j * ϑ` equals the fiber point at the
`extractMiddleFinMask` index. -/
lemma previousSuffix_eq_getFiberPoint_extractMiddleFinMask
    (j : Fin (ℓ / ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨j.val * ϑ, by
        exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := k_mul_ϑ_lt_ℓ (k := j))⟩)
      (h_destIdx_le := Nat.le_of_lt (k_mul_ϑ_lt_ℓ (k := j))) =
      getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (i := ⟨j.val * ϑ, k_mul_ϑ_lt_ℓ (k := j)⟩)
          (steps := ϑ)) := by
  rw [getFiberPoint_eq_qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j v]
  exact cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask_core 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := j.val * ϑ) (steps := ϑ)
    (h_i_lt_ℓ := k_mul_ϑ_lt_ℓ (k := j))
    (h_le := k_succ_mul_ϑ_le_ℓ_₂ (k := j))
    (v := v)

end QueryPhaseSuffixLemmas

end

end Binius.BinaryBasefold
