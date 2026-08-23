/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase2FarLift
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessProposition

/-!
# Proposition 4.21 Case 2 probability bound

This module supplies the concrete fold/tensor bridge from `Soundness.Incremental` to the
cycle-free far-lift theorem in `Prop421Case2FarLift`.
-/

namespace Binius.BinaryBasefold

open AdditiveNTT Matrix MvPolynomial Finset InterleavedCode Code
open scoped NNReal ProbabilityTheory
open ProbabilityTheory

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

/-- **Proposition 4.21 Case 2 (fiberwise far).** The random fold is UDR-close to the
destination code with probability at most `steps * |S_next| / |L|`. -/
lemma prop421Case2_probability_bound
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let next_domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      let f_next := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        h_destIdx h_destIdx_le f_i r
      UDRClose 𝔽q β destIdx h_destIdx_le f_next
    ] ≤ ((steps * next_domain_size) / Fintype.card L) :=
  prop421Case2_probability_bound_of_bridge 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (fun (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
        (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
        (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
        (r_chal : Fin steps → L) =>
      iterated_fold_eq_multilinearCombine_preTensorCombine 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
        i steps h_destIdx h_destIdx_le f_i r_chal)
    i steps h_destIdx h_destIdx_le f_i h_far

/-- **Proposition 4.21, Case 2 (fiberwise far).** This is the residual-free public wrapper
around the concrete DG25/far-lift probability bound. -/
lemma prop_4_21_case_2_fiberwise_far
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let next_domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      let f_next := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i r
      UDRClose 𝔽q β destIdx h_destIdx_le f_next
    ] ≤ ((steps * next_domain_size) / Fintype.card L) :=
  prop421Case2_probability_bound 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le f_i h_far

open Classical in
/-- **Proposition 4.21** (Bound on Bad Folding Event).

The probability over random folding challenges of the bad folding event is bounded by
`steps * |S^(i+steps)| / |L|`. The close branch uses
`prop_4_21_case_1_fiberwise_close`; the far branch uses the concrete DG25/far-lift
`prop_4_21_case_2_fiberwise_far` above. -/
lemma prop_4_21_bad_event_probability
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_challenges ←$ᵖ (Fin steps → L) }[
      foldingBadEvent 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le
        f_i r_challenges ] ≤
    ((steps * domain_size) / Fintype.card L) := by
  unfold foldingBadEvent
  by_cases h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)
  · simp only [h_close, ↓reduceDIte]
    exact prop_4_21_case_1_fiberwise_close 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f_i := f_i) (h_close := h_close)
  · simp only [h_close, ↓reduceDIte]
    exact prop_4_21_case_2_fiberwise_far 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f_i := f_i) (h_far := h_close)

end

end Binius.BinaryBasefold
