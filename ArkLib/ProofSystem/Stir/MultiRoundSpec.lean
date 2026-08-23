/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.VectorIOR

/-!
# The STIR multi-round vector protocol shape (#301)

The `stir_rbr_soundness` statement (`Stir/MainThm.lean`) opens with
`∃ n, ∃ vPSpec : ProtocolSpec.VectorSpec n, Fintype.card vPSpec.ChallengeIdx = 2 * M + 2 ∧ …`.
This file supplies the canonical witness: the STIR round shape with `M + 1` prover messages
(the folded oracles `g_1, …, g_M` and the final polynomial `p`) and `2M + 2` verifier
challenges (the initial fold challenge, per-round out/shift challenge pairs, and the final
repetition challenge), laid out uniformly as `dir i = P_to_V ↔ i % 3 = 1` on `Fin (3M + 3)`:

`[C₀^fold, P g₁, C₁^out, C₁^shift, P g₂, …, C_M^out, C_M^shift, P p, C^fin]`. -/

namespace StirIOP

open ProtocolSpec VectorSpec

/-- **The STIR multi-round vector-protocol shape** for depth `M`: `3M + 3` rounds, where
round `i` is a prover message iff `i % 3 = 1` (the `M` folded oracles and the final
polynomial), and a verifier challenge otherwise (the initial fold challenge, the `M`
out/shift challenge pairs, and the final repetition challenge). `msgLen j` is the length of
the `j`-th prover message (`j < M`: the folded oracle `g_{j+1}`; `j = M`: the final
polynomial), and `chalLen` the (uniform) challenge length. -/
def stirVSpec (M : ℕ) (msgLen : Fin (M + 1) → ℕ) (chalLen : ℕ) :
    ProtocolSpec.VectorSpec (3 * M + 3) where
  dir i := if (i : ℕ) % 3 = 1 then .P_to_V else .V_to_P
  length i := if h : (i : ℕ) % 3 = 1 then msgLen ⟨(i : ℕ) / 3, by omega⟩ else chalLen

variable {M : ℕ} {msgLen : Fin (M + 1) → ℕ} {chalLen : ℕ}

@[simp] theorem stirVSpec_dir_eq_msg_iff {i : Fin (3 * M + 3)} :
    (stirVSpec M msgLen chalLen).dir i = .P_to_V ↔ (i : ℕ) % 3 = 1 := by
  unfold stirVSpec
  by_cases h : (i : ℕ) % 3 = 1 <;> simp [h]

theorem stirVSpec_dir_eq_chal_iff {i : Fin (3 * M + 3)} :
    (stirVSpec M msgLen chalLen).dir i = .V_to_P ↔ ¬ ((i : ℕ) % 3 = 1) := by
  unfold stirVSpec
  by_cases h : (i : ℕ) % 3 = 1 <;> simp [h]

set_option linter.unusedSimpArgs false in
/-- The initial round is the fold challenge. -/
theorem stirVSpec_dir_zero :
    (stirVSpec M msgLen chalLen).dir ⟨0, by omega⟩ = .V_to_P := by
  rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega

set_option linter.unusedSimpArgs false in
/-- Round `3j + 1` is the `j`-th prover message. -/
theorem stirVSpec_dir_msg (j : Fin (M + 1)) :
    (stirVSpec M msgLen chalLen).dir ⟨3 * (j : ℕ) + 1, by omega⟩ = .P_to_V := by
  rw [stirVSpec_dir_eq_msg_iff]; simp only [Fin.val_mk]; omega

set_option linter.unusedSimpArgs false in
/-- The final round is the last (repetition) challenge. -/
theorem stirVSpec_dir_last :
    (stirVSpec M msgLen chalLen).dir ⟨3 * M + 2, by omega⟩ = .V_to_P := by
  rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega

/-- **The STIR shape has exactly `M + 1` prover messages** (the `M` folded oracles plus the
final polynomial). The message positions are exactly `{3j + 1 : j ≤ M}`. -/
theorem stirVSpec_card_messageIdx :
    Fintype.card (stirVSpec M msgLen chalLen).MessageIdx = M + 1 := by
  rw [show (M + 1) = Fintype.card (Fin (M + 1)) from (Fintype.card_fin _).symm]
  apply Fintype.card_congr
  refine
    { toFun := fun i => ⟨((i : Fin (3 * M + 3)) : ℕ) / 3, by
        have := i.2; rw [stirVSpec_dir_eq_msg_iff] at this
        have := ((i : Fin (3 * M + 3))).2; omega⟩
      invFun := fun j => ⟨⟨3 * (j : ℕ) + 1, by omega⟩, stirVSpec_dir_msg j⟩
      left_inv := ?_, right_inv := ?_ }
  · rintro ⟨⟨i, hi⟩, h⟩
    rw [stirVSpec_dir_eq_msg_iff] at h
    simp only [Fin.val_mk] at h
    simp only [Subtype.mk.injEq, Fin.mk.injEq, Fin.val_mk]
    omega
  · rintro ⟨j, hj⟩
    simp only [Subtype.mk.injEq, Fin.mk.injEq, Fin.val_mk]
    omega

/-- **The STIR shape has exactly `2M + 2` verifier challenges** — the count demanded by the
opening conjunct of `stir_rbr_soundness` (Lemma 5.4): the initial fold challenge, the `M`
out/shift challenge pairs, and the final repetition challenge. -/
theorem stirVSpec_card_challengeIdx :
    Fintype.card (stirVSpec M msgLen chalLen).ChallengeIdx = 2 * M + 2 := by
  have h1 : Fintype.card (stirVSpec M msgLen chalLen).ChallengeIdx
      = Fintype.card {i : Fin (3 * M + 3) // ¬ ((i : ℕ) % 3 = 1)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      rw [stirVSpec_dir_eq_chal_iff])
  have h2 : Fintype.card {i : Fin (3 * M + 3) // (i : ℕ) % 3 = 1} = M + 1 := by
    rw [← stirVSpec_card_messageIdx (msgLen := msgLen) (chalLen := chalLen)]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      rw [stirVSpec_dir_eq_msg_iff])
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]
  omega

end StirIOP

#print axioms StirIOP.stirVSpec_card_messageIdx
#print axioms StirIOP.stirVSpec_card_challengeIdx
