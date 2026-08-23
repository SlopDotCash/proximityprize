/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.Data.CodingTheory.ProximityGap.DG25.Contrapositive

/-!
# Proposition 4.21 Case 2: assembly from the DG25 tensor gap

DP24 Proposition 4.21, Case 2 (fiberwise-far branch) closes through the in-tree DG25 chain
(Cor 3.7, `reedSolomon_multilinearCorrelatedAgreement_Nat`, proven): `BBF_Code` *is*
`ReedSolomon.code`, so within unique decoding the tensor combination of a far stack stays far
except with probability `steps · |S_next| / |L|`.

This file does all the proof assembly work now — the RS unfolding of `BBF_Code`, the
`Nontrivial`/`NeZero` side instances, the `UDRClose ↔ distance ≤ uniqueDecodingRadius`
arithmetic, and the ENNReal cast algebra — and packages the result as
`prop421Case2_probability_bound_of_bridges`, conditional on exactly the two statement-level inputs still
being produced by other active lanes:

1. **the fold/tensor bridge** (`iterated_fold_eq_multilinearCombine_preTensorCombine`, proved
   in `Soundness/Incremental.lean`), and
2. **the Lemma 4.22 far-lift** (the `PreTensor*` lane): a fiberwise-far oracle's pre-tensor
   stack is NOT jointly proximate to the interleaved destination code at unique decoding
   radius.

Once both land, the Proposition 4.21 case-2 probability bound follows directly.
-/

set_option linter.unusedSectionVars false

namespace Binius.BinaryBasefold

open AdditiveNTT Matrix MvPolynomial Finset InterleavedCode ProximityGap Code
open scoped NNReal
open ProbabilityTheory

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- The destination BBF code is nontrivial: it contains `0` and the constant-one word. -/
lemma BBF_Code_nontrivial (i : Fin r) (h_i : i ≤ ℓ) :
    Nontrivial (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  refine ⟨⟨0, ?_⟩⟩
  refine ⟨⟨(fun _ => (1 : L)), constFunc_mem_BBFCode 𝔽q β (h_i := h_i) 1⟩, ?_⟩
  intro hcontra
  have h0 : (sDomain 𝔽q β h_ℓ_add_R_rate) i := 0
  have := congrFun (congrArg Subtype.val hcontra) h0
  simp at this

/-- `UDRClose` is exactly "distance at most the unique decoding radius" (Nat arithmetic,
needs the code distance to be positive). -/
lemma UDRClose_iff_dist_le_udr (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f ↔
      Δ₀(f, ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
          : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L)))
        ≤ Code.uniqueDecodingRadius
            (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
              : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L))) := by
  have hd : 1 ≤ BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i]
    omega
  unfold UDRClose Code.uniqueDecodingRadius
  unfold BBF_CodeDistance at hd ⊢
  set d : ℕ := ‖((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L))‖₀ with hd_def
  induction Δ₀(f, ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L))) using ENat.recTopCoe with
  | top =>
    constructor
    · intro h
      have htop : (2 : ℕ∞) * ⊤ = ⊤ := by
        simp
      rw [htop] at h
      exact absurd h not_top_lt
    · intro h
      rw [top_le_iff] at h
      exact absurd h (ENat.coe_ne_top _)
  | coe n =>
    constructor
    · intro h
      have hn : 2 * n < d := by exact_mod_cast h
      exact_mod_cast (by omega : n ≤ (d - 1) / 2)
    · intro h
      have hn : n ≤ (d - 1) / 2 := by exact_mod_cast h
      exact_mod_cast (by omega : 2 * n < d)

/-- **Proposition 4.21, Case 2 — conditional assembly.**

Given (1) the fold/tensor bridge (proven in `Soundness/Incremental.lean` as
`iterated_fold_eq_multilinearCombine_preTensorCombine`) and (2) the Lemma 4.22 far-lift
(PreTensor lane), the fiberwise-far bound holds: the heavy probabilistic input is the
in-tree DG25 Corollary 3.7 with `ε = |S_next|`, consumed in contrapositive form. -/
lemma prop421Case2_probability_bound_of_bridges
    (hBridge : ∀ (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
      (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
      (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
      (r_chal : Fin steps → L),
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
          (r_challenges := r_chal)
        = multilinearCombine (F := L)
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) r_chal)
    (hFarLift : ∀ (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
      (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
      (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩),
      ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
          (h_destIdx_le := h_destIdx_le) (f := f_i) →
      ¬ jointProximityNat
          (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
            : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L)))
          (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)
          (Code.uniqueDecodingRadius
            (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
              : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L)))))
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
    ] ≤ ((steps * next_domain_size) / Fintype.card L) := by
  -- Notation for the destination code (as a set) and its UDR.
  set C : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L) :=
    ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L)) with hC_def
  set u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i with hu_def
  -- The DG25 multilinear correlated-agreement property for the destination RS code.
  have hCA : δ_ε_multilinearCorrelatedAgreement_Nat (F := L) (A := L)
      (C := C) (ϑ := steps) (e := Code.uniqueDecodingRadius (C := C))
      (ε := Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)) := by
    haveI : NeZero (2 ^ (ℓ - destIdx.val)) := ⟨pow_ne_zero _ (by norm_num)⟩
    haveI hNT : Nontrivial (ReedSolomon.code
        (⟨fun x => x.val, fun x y h => Subtype.ext h⟩
          : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx ↪ L)
        (2 ^ (ℓ - destIdx.val))) :=
      BBF_Code_nontrivial 𝔽q β destIdx h_destIdx_le
    have hk : 2 ^ (ℓ - destIdx.val)
        ≤ Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) := by
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by
        have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
        omega), hF₂.out]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have := reedSolomon_multilinearCorrelatedAgreement_Nat
      (ι := (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) (A := L)
      (α := ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩)
      (k := 2 ^ (ℓ - destIdx.val))
      hk (le_refl _) steps (Nat.pos_of_neZero steps)
    exact this
  -- Contrapositive + far-lift: the tensor combination stays far w.h.p.
  have hProb := ProximityGap.multilinearCorrelatedAgreement_contrapositive
    (F := L) (A := L) (C := C) (ϑ := steps) hCA u
    (hFarLift i steps h_destIdx h_destIdx_le f_i h_far)
  -- Event congruence: `UDRClose (fold f r)` is `Δ₀(r |⨂| u, C) ≤ UDR`.
  have hiff : ∀ rch : Fin steps → L,
      (UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx h_destIdx_le
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
            h_destIdx h_destIdx_le f_i rch))
        ↔ Δ₀(multilinearCombine (F := L) u rch, C) ≤ Code.uniqueDecodingRadius (C := C) := by
    intro rch
    rw [UDRClose_iff_dist_le_udr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      destIdx h_destIdx_le]
    rw [hBridge i steps h_destIdx h_destIdx_le f_i rch]
  refine le_trans (le_of_eq (Pr_congr hiff)) (le_trans hProb ?_)
  -- Cast algebra: steps · |S_next| / |L| in the statement's coercion shape.
  push_cast
  exact le_of_eq (by rw [mul_div_assoc])

end

end Binius.BinaryBasefold
