/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSListThresholdGapBracket
import ArkLib.Data.CodingTheory.ProximityGap.UpToCapacityListDecodingFalse

/-!
# Concrete strict bracket: `75 ≤ δ* < 128` at rate `1/2` (#232)

End-to-end strict trap for the headline prize rate, fusing every ingredient:

  `rs_ld_threshold_strict_rate12` — for `RS[F, α, 128]` on a size-`256` domain, `m = 1`,
  `ε* = 2^{-128}`, over any field with `263·2^128 ≤ |F| ≤ 2^256`:

      `75 ≤ listLatticeThreshold  <  128`,   i.e.   `0.293 ≤ δ* < 0.5`.

The lower index `75` is the Johnson radius `1 − √ρ` (`rs_ld_threshold_johnson_pin_general`); the
**strict** upper index `128` is the capacity index, now excluded via
`listLatticeThreshold_lt_of_overflow` fed by the capacity overflow
`rs_uptoCapacity_false_rate12_n256` (`Λ(RS, 1/2) > ε*·|F|`). So capacity is not merely an upper
bound — the threshold is *strictly* below it.

This upgrades the earlier `75 ≤ δ* ≤ 128` to the strict `75 ≤ δ* < 128`, demonstrating the full
machinery (second-moment Johnson lower bound + entropy-volume overflow + interleaving propagation)
end-to-end on a concrete prize instance. The remaining open question is the matching lower bound
`δ* ≥ δ_LD` (the prize). Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Concrete strict bracket at rate `1/2`.** For `RS[F, α, 128]` (`n = 256`), `m = 1`,
`ε* = 2^{-128}`, any field with `263·2^128 ≤ |F| ≤ 2^256`: the lattice threshold satisfies
`75 ≤ δ*-index < 128` — Johnson radius up to, but strictly below, the capacity radius. -/
theorem rs_ld_threshold_strict_rate12
    {F : Type} [Field F] [Fintype F] [DecidableEq F] (α : Fin 256 ↪ F)
    (hF1 : (263 : ℕ) * 2 ^ 128 ≤ Fintype.card F) (hF2 : Fintype.card F ≤ 2 ^ 256) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128)).Nonempty,
      75 ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne < 128 := by
  classical
  haveI : NeZero (128 : ℕ) := ⟨by norm_num⟩
  -- capacity overflow from the negative-side capstone
  have hq1 : (2 : ℝ) ^ 128 ≤ (Fintype.card F : ℝ) := by
    have h : (2 : ℕ) ^ 128 ≤ Fintype.card F :=
      le_trans (by norm_num : (2 : ℕ) ^ 128 ≤ 263 * 2 ^ 128) hF1
    exact_mod_cast h
  have hq2 : (Fintype.card F : ℝ) ≤ 2 ^ 256 := by exact_mod_cast hF2
  have hneg := CodingTheory.rs_uptoCapacity_false_rate12_n256 α hq1 hq2
  -- bridge the negative-result `ofReal` form to the coercion-product form, at radius 128/256
  have hover : ((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) * (Fintype.card F : ENNReal)
      < (Lambda ((ReedSolomon.code α 128 : Set (Fin 256 → F)))
          (((128 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal) := by
    have hrad : (((128 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ) = (1 / 2 : ℝ) := by
      rw [Fintype.card_fin]; push_cast; norm_num
    rw [hrad]
    have hbridge : ((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) * (Fintype.card F : ENNReal)
        = ENNReal.ofReal ((1 / 2 ^ 128) * (Fintype.card F : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      · rw [show ((1 : ℝ) / 2 ^ 128) = (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ) by push_cast; ring,
          ENNReal.ofReal_coe_nnreal]
      · rw [ENNReal.ofReal_natCast]
    rw [hbridge]
    exact hneg
  -- Johnson lower witness at j = 75 (list cap 263)
  have hl : (Fintype.card (Fin 256) ^ 2 /
      ((Fintype.card (Fin 256) - 75) ^ 2 - Fintype.card (Fin 256) * (128 - 1)) : ℕ) = 263 := by
    simp only [Fintype.card_fin]; norm_num
  have hr : (263 : ℝ≥0) ≤ ((1 : ℝ≥0) / 2 ^ 128) * (Fintype.card F : ℝ≥0) := by
    have hFr : (263 : ℝ≥0) * (2 : ℝ≥0) ^ 128 ≤ (Fintype.card F : ℝ≥0) := by exact_mod_cast hF1
    have hmul := mul_le_mul_left' hFr ((1 : ℝ≥0) / 2 ^ 128)
    have hone : ((1 : ℝ≥0) / 2 ^ 128) * ((263 : ℝ≥0) * 2 ^ 128) = 263 := by
      rw [one_div, mul_comm (263 : ℝ≥0) ((2 : ℝ≥0) ^ 128), ← mul_assoc,
        inv_mul_cancel₀ (by positivity), one_mul]
    rwa [hone] at hmul
  obtain ⟨hne, hlo, _⟩ := rs_ld_threshold_johnson_pin_general (F := F) (ι := Fin 256)
    α (k := 128) (j := 75)
    (by rw [Fintype.card_fin]; norm_num)
    (by rw [Fintype.card_fin]; norm_num)
    (by simp only [Fintype.card_fin]; norm_num)
    (ε_star := (1 : ℝ≥0) / 2 ^ 128)
    (by
      rw [one_div]
      exact inv_lt_one_of_one_lt₀ (by
        calc (1 : ℝ≥0) < 2 := by norm_num
          _ ≤ 2 ^ 128 := le_self_pow₀ (by norm_num) (by norm_num)))
    (by
      rw [hl, ← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_mul]
      exact_mod_cast hr)
  exact ⟨hne, hlo, listLatticeThreshold_lt_of_overflow
    (C := (ReedSolomon.code α 128 : Set (Fin 256 → F))) (m := 1) (j := 128) hover hne⟩

#print axioms rs_ld_threshold_strict_rate12

end ProximityGap
