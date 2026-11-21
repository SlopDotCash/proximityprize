/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateTwoRichFloor

/-! # Exact support sizes forced by a first-prime quarter-rate successor failure -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorFirstFailures

open Finset Code HalfPredecessorBadEventRichPointBridge
open scoped NNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- A support for one scalar that admits a folded codeword and rules out a joint explanation. -/
def detects (D : I ↪ F) (u : WordStack F (Fin 2) I) (z : F) (S : Finset I) : Prop :=
  (∃ w ∈ (ReedSolomon.code D 268435456 : Set (I → F)), ∀ i ∈ S, w i = u 0 i + z • u 1 i) ∧
    ¬ _root_.ProximityGap.pairJointAgreesOn
      (ReedSolomon.code D 268435456 : Set (I → F)) S (u 0) (u 1)

/-- If a single pair exceeds the first-prime budget at 447392428 errors, at least
178956969 distinct scalars become bad at precisely this step for that same pair.
Each admits a nonjoint support of exactly 626349396 positions, which is also its maximum. -/
theorem newly_bad (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hchar : ∀ j : ℕ, 0 < j → j ≤ 2505397586 → (j : F) ≠ 0)
    (u : WordStack F (Fin 2) I)
    (hfail : 1073741824 < (badScalars D 268435456 (447392428 / 1073741824) u).card) :
    let fresh := badScalars D 268435456 (447392428 / 1073741824) u \
      badScalars D 268435456 (447392427 / 1073741824) u
    178956969 ≤ fresh.card ∧ ∀ z ∈ fresh,
      (∃ S : Finset I, S.card = 626349396 ∧ detects D u z S) ∧
      ∀ S : Finset I, detects D u z S → S.card ≤ 626349396 := by
  classical
  let prev : ℝ≥0 := 447392427 / 1073741824
  let next : ℝ≥0 := 447392428 / 1073741824
  let fam := canonicalBadScalarRichPointFamily D prev u (by decide : 1 ≤ 268435456)
  have old_step : (1 - prev) * (Fintype.card I : ℝ≥0) = 626349397 := by
    simp only [hn, Nat.cast_ofNat]
    dsimp only [prev]
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num : (1073741824 : ℝ≥0) ≠ 0)]
    exact (tsub_eq_iff_eq_add_of_le (by norm_num)).mpr (by norm_num)
  have new_step : (1 - next) * (Fintype.card I : ℝ≥0) = 626349396 := by
    simp only [hn, Nat.cast_ofNat]
    dsimp only [next]
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num : (1073741824 : ℝ≥0) ≠ 0)]
    exact (tsub_eq_iff_eq_add_of_le (by norm_num)).mpr (by norm_num)
  have card := QuarterRateTwoRichFloor.saturated_exact_cap fam hn
    (by rw [old_step]; norm_num) (fun j hj hj' => hchar j hj (by omega))
  change (badScalars D 268435456 prev u).card ≤ 894784856 at card
  let P := badScalars D 268435456 prev u
  let N := badScalars D 268435456 next u
  change 1073741824 < N.card at hfail
  change P.card ≤ 894784856 at card
  change 178956969 ≤ (N \ P).card ∧ _
  constructor
  · have h := card_le_card_sdiff_add_card (s := N) (t := P)
    omega
  · intro z hz
    obtain ⟨hN, hP⟩ := mem_sdiff.mp (show z ∈ N \ P from hz)
    have max_size (S : Finset I) (h : detects D u z S) : S.card ≤ 626349396 := by
      by_contra! hlarge
      apply hP
      apply (mem_badScalars_iff D 268435456 prev u z).mpr
      refine ⟨S, ?_, h.1, h.2⟩
      rw [old_step]
      exact_mod_cast (show 626349397 ≤ S.card by omega)
    obtain ⟨S, hs, hw, hj⟩ := (mem_badScalars_iff D 268435456 next u z).mp hN
    rw [new_step] at hs
    have hdet : detects D u z S := ⟨hw, hj⟩
    have hs' : 626349396 ≤ S.card := by exact_mod_cast hs
    exact ⟨⟨S, (max_size S hdet).antisymm hs', hdet⟩, max_size⟩

end ArkLib.ProximityGap.Frontier.QuarterSuccessorFirstFailures
