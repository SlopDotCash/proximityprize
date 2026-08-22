/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSListThresholdStrictRate12
import ArkLib.Data.CodingTheory.ProximityGap.ListDecodingCapacityOverflow

/-!
# A smaller-field subcapacity sharpening at rate `1/2` (#232)

The uniform rate-`1/2`, `n = 256`, `k = 128` capstone excludes the capacity lattice
point `j = 128` throughout the full prize field window.  This file tests the next lattice
point: in the smaller field window `|F| ≤ 2^160`, the same entropy-volume overflow already
fires at `j = 127`, giving a stricter upper threshold.

This is not the prize lower-bound breakthrough.  It is a field-window refinement of the
known overflow side, and a useful diagnostic for why the universal theorem cannot simply
move from `127` to `126` under the full `|F| ≤ 2^256` hypothesis.
-/

set_option exponentiation.threshold 4096


namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable
open CodingTheory

set_option maxHeartbeats 800000 in
-- The concrete `j = 127` entropy identity carries large integer powers through `norm_num`/`ring`.
/-- **Rate-`1/2` entropy-volume overflow at index `127`, for smaller fields.**  For
`RS[F, α, 128]` on `Fin 256`, if `263·2^128 ≤ |F| ≤ 2^160`, then at radius
`127/256` the base-code list size already exceeds the prize budget. -/
theorem rs_lambda_gt_rate12_j127_n256_of_card_le_pow160
    {F : Type} [Field F] [Fintype F] (α : Fin 256 ↪ F)
    (hF1 : (263 : ℕ) * 2 ^ 128 ≤ Fintype.card F)
    (hF2 : Fintype.card F ≤ 2 ^ 160) :
    (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ENNReal) * (Fintype.card F : ENNReal)
      < (Lambda ((ReedSolomon.code α 128 : Set (Fin 256 → F))) (127 / 256) :
          ENNReal) := by
  classical
  have hqNat : 2 ≤ Fintype.card F := by
    exact le_trans (by norm_num : 2 ≤ (263 : ℕ) * 2 ^ 128) hF1
  have hover : Real.logb (Fintype.card F)
        (((Fintype.card (Fin 256) : ℝ) + 1) *
          (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ) * (Fintype.card F : ℝ))
      < (Fintype.card (Fin 256) : ℝ) * qEntropy (Fintype.card F)
          ((⌊(127 / 256 : ℝ) * (Fintype.card (Fin 256) : ℝ)⌋₊ : ℝ) /
            (Fintype.card (Fin 256) : ℝ))
        - ((Fintype.card (Fin 256) : ℝ) - (128 : ℝ)) := by
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    have hqlo : (263 : ℝ) * (2 : ℝ) ^ 128 ≤ q := by
      rw [hqdef]
      exact_mod_cast hF1
    have hqhi : q ≤ (2 : ℝ) ^ 160 := by
      rw [hqdef]
      exact_mod_cast hF2
    have hqpos : 0 < q := by
      have h2pow : (0 : ℝ) < (2 : ℝ) ^ 128 := by positivity
      nlinarith [hqlo]
    have hqgt1 : 1 < q := by
      have h2pow : (1 : ℝ) < (2 : ℝ) ^ 128 := by norm_num
      nlinarith [hqlo, h2pow]
    have hqm1pos : 0 < q - 1 := by linarith
    have hqge257 : (257 : ℝ) ≤ q := by
      have hbig : (257 : ℝ) ≤ (263 : ℝ) * (2 : ℝ) ^ 128 := by norm_num
      exact le_trans hbig hqlo
    have hratio_base : (256 : ℝ) * q ≤ 257 * (q - 1) := by
      nlinarith
    have hratio_pow :
        (256 : ℝ) ^ 127 * q ^ 127 ≤ 257 ^ 127 * (q - 1) ^ 127 := by
      have h := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ (256 : ℝ) * q) hratio_base 127
      simpa [mul_pow] using h
    have hratio_num : (257 : ℝ) ^ 127 < 2 * 256 ^ 127 := by norm_num
    have hqpow_le : q ^ 127 ≤ 2 * (q - 1) ^ 127 := by
      have hpos : (0 : ℝ) < (256 : ℝ) ^ 127 := by positivity
      have hmul : q ^ 127 * 256 ^ 127 ≤ 2 * (q - 1) ^ 127 * 256 ^ 127 := by
        calc
        q ^ 127 * 256 ^ 127 = 256 ^ 127 * q ^ 127 := by ring
        _ ≤ 257 ^ 127 * (q - 1) ^ 127 := hratio_pow
        _ ≤ (2 * 256 ^ 127) * (q - 1) ^ 127 := by
          gcongr
        _ = 2 * (q - 1) ^ 127 * 256 ^ 127 := by ring
      nlinarith
    have hq2_le : q ^ 2 ≤ (2 : ℝ) ^ 320 := by
      calc
        q ^ 2 ≤ ((2 : ℝ) ^ 160) ^ 2 := pow_le_pow_left₀ (le_of_lt hqpos) hqhi 2
        _ = (2 : ℝ) ^ 320 := by rw [← pow_mul]
    have hmain :
        (257 : ℝ) * q * ((127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128)
          < (2 : ℝ) ^ 2176 * (q - 1) ^ 127 := by
      have hnum :
          (257 : ℝ) * 127 ^ 127 * 129 ^ 129 * 2 ^ 320 * 2 < 2 ^ 2176 := by
        norm_num
      have hq129 : q * q ^ 128 = q ^ 2 * q ^ 127 := by ring
      calc
        (257 : ℝ) * q * ((127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128)
            = 257 * 127 ^ 127 * 129 ^ 129 * (q * q ^ 128) := by ring
        _ = 257 * 127 ^ 127 * 129 ^ 129 * (q ^ 2 * q ^ 127) := by rw [hq129]
        _ ≤ 257 * 127 ^ 127 * 129 ^ 129 *
              ((2 : ℝ) ^ 320 * (2 * (q - 1) ^ 127)) := by
            gcongr
        _ = (257 * 127 ^ 127 * 129 ^ 129 * 2 ^ 320 * 2) * (q - 1) ^ 127 := by
            ring
        _ < 2 ^ 2176 * (q - 1) ^ 127 := by
            exact mul_lt_mul_of_pos_right hnum (pow_pos hqm1pos 127)
    have harglt :
        (257 : ℝ) * ((((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ) * q)
          < (((2 : ℝ) ^ 2048 * (q - 1) ^ 127) /
              ((127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128)) := by
      have hdenpos : 0 < (127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128 := by positivity
      rw [show (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ) = (1 : ℝ) / 2 ^ 128 by
        norm_num]
      have hpow128 : (0 : ℝ) < (2 : ℝ) ^ 128 := by positivity
      apply (lt_div_iff₀ hdenpos).mpr
      refine lt_of_mul_lt_mul_left ?_ (le_of_lt hpow128)
      calc
        (2 : ℝ) ^ 128 * ((257 : ℝ) * ((1 / 2 ^ 128) * q) *
            ((127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128))
            = 257 * q * ((127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128) := by
              field_simp [pow_ne_zero 128 (by norm_num : (2 : ℝ) ≠ 0)]
        _ < (2 : ℝ) ^ 2176 * (q - 1) ^ 127 := hmain
        _ = (2 : ℝ) ^ 128 * ((2 : ℝ) ^ 2048 * (q - 1) ^ 127) := by
              rw [show 2176 = 128 + 2048 by norm_num, pow_add]
              ring
    have hE :
        (Fintype.card (Fin 256) : ℝ) * qEntropy (Fintype.card F)
            ((⌊(127 / 256 : ℝ) * (Fintype.card (Fin 256) : ℝ)⌋₊ : ℝ) /
              (Fintype.card (Fin 256) : ℝ))
          - ((Fintype.card (Fin 256) : ℝ) - (128 : ℝ))
        = Real.logb (Fintype.card F)
            ((((2 : ℝ) ^ 2048 * (q - 1) ^ 127) /
              ((127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128))) := by
      have hqcard : (Fintype.card F : ℝ) = q := by rw [hqdef]
      have hfloor : ((⌊(127 / 256 : ℝ) * (256 : ℝ)⌋₊ : ℝ) / (256 : ℝ)) =
          127 / 256 := by norm_num
      have hsub : ((256 : ℝ) - (128 : ℝ)) = 128 := by norm_num
      have h1sub : (1 : ℝ) - 127 / 256 = 129 / 256 := by norm_num
      rw [Fintype.card_fin]
      change (256 : ℝ) * qEntropy (Fintype.card F)
          ((⌊(127 / 256 : ℝ) * (256 : ℝ)⌋₊ : ℝ) / (256 : ℝ))
        - ((256 : ℝ) - (128 : ℝ))
        = Real.logb (Fintype.card F)
            ((((2 : ℝ) ^ 2048 * (q - 1) ^ 127) /
              ((127 : ℝ) ^ 127 * 129 ^ 129 * q ^ 128)))
      rw [hfloor, hsub]
      unfold qEntropy
      rw [h1sub, hqcard]
      have hqne : q ≠ 0 := ne_of_gt hqpos
      have hqm1ne : q - 1 ≠ 0 := ne_of_gt hqm1pos
      have h127ne : (127 : ℝ) ≠ 0 := by norm_num
      have h129ne : (129 : ℝ) ≠ 0 := by norm_num
      have h256ne : (256 : ℝ) ≠ 0 := by norm_num
      have h2ne : (2 : ℝ) ≠ 0 := by norm_num
      have h2powne : (2 : ℝ) ^ 2048 ≠ 0 := pow_ne_zero _ h2ne
      have hqm1powne : (q - 1) ^ 127 ≠ 0 := pow_ne_zero _ hqm1ne
      have h127powne : (127 : ℝ) ^ 127 ≠ 0 := pow_ne_zero _ h127ne
      have h129powne : (129 : ℝ) ^ 129 ≠ 0 := pow_ne_zero _ h129ne
      have hqpowne : q ^ 128 ≠ 0 := pow_ne_zero _ hqne
      have hlogq : Real.logb q q = 1 := Real.logb_self_eq_one hqgt1
      have hlogqpow : Real.logb q (q ^ 128) = (128 : ℝ) * Real.logb q q := by
        rw [Real.logb_pow]
        norm_num
      have hlog256 : Real.logb q (256 : ℝ) = (8 : ℝ) * Real.logb q (2 : ℝ) := by
        rw [show (256 : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.logb_pow]
        norm_num
      rw [Real.logb_div (mul_ne_zero h2powne hqm1powne)
          (mul_ne_zero (mul_ne_zero h127powne h129powne) hqpowne),
        Real.logb_mul h2powne hqm1powne,
        Real.logb_mul (mul_ne_zero h127powne h129powne) hqpowne,
        Real.logb_mul h127powne h129powne,
        hlogqpow, hlogq,
        Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_pow,
        show Real.logb q ((127 : ℝ) / 256) =
            Real.logb q (127 : ℝ) - Real.logb q (256 : ℝ) by
          rw [Real.logb_div h127ne h256ne],
        show Real.logb q ((129 : ℝ) / 256) =
            Real.logb q (129 : ℝ) - Real.logb q (256 : ℝ) by
          rw [Real.logb_div h129ne h256ne],
        hlog256]
      norm_num
      ring
    have hargpos : 0 < (257 : ℝ) *
        ((((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ) * q) := by
      have hepspos : 0 < ((((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ)) := by positivity
      exact mul_pos (by norm_num) (mul_pos hepspos hqpos)
    have hloglt := Real.logb_lt_logb (b := q) hqgt1 hargpos harglt
    have hargleft :
        ((Fintype.card (Fin 256) : ℝ) + 1) *
            (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ) * (Fintype.card F : ℝ)
          = (257 : ℝ) * ((((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ℝ) * q) := by
      rw [Fintype.card_fin, hqdef]
      ring
    rw [hE]
    rw [hargleft]
    simpa [hqdef] using hloglt
  exact CodingTheory.rs_lambda_gt_threshold_of_capExp_overflow
    (F := F) (ι := Fin 256) α 128 (127 / 256)
    (by norm_num) (by norm_num) hqNat
    (by rw [Fintype.card_fin]; norm_num)
    (by rw [Fintype.card_fin]; norm_num)
    (by rw [Fintype.card_fin]; norm_num)
    ((1 : ℝ≥0) / 2 ^ 128) (by simpa [mul_assoc] using hover)

#print axioms rs_lambda_gt_rate12_j127_n256_of_card_le_pow160

/-- **Smaller-field strict bracket at rate `1/2`.** For `RS[F, α, 128]` (`n = 256`),
`m = 1`, `ε* = 2^{-128}`, any field with `263·2^128 ≤ |F| ≤ 2^160`: the lattice
threshold satisfies `75 ≤ δ*-index ≤ 126`.  The upper endpoint improves the full-window
`≤ 127` capstone by excluding the next lattice point `j = 127`. -/
theorem rs_ld_threshold_subcapacity_rate12
    {F : Type} [Field F] [Fintype F] (α : Fin 256 ↪ F)
    (hF1 : (263 : ℕ) * 2 ^ 128 ≤ Fintype.card F)
    (hF2 : Fintype.card F ≤ 2 ^ 160) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128)).Nonempty,
      75 ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne
            ≤ 126 := by
  classical
  have hF2_256 : Fintype.card F ≤ 2 ^ 256 :=
    le_trans hF2 (by norm_num : 2 ^ 160 ≤ (2 : ℕ) ^ 256)
  obtain ⟨hne, hlo, _⟩ := rs_ld_threshold_strict_rate12 α hF1 hF2_256
  have hover := rs_lambda_gt_rate12_j127_n256_of_card_le_pow160 α hF1 hF2
  have hover127 :
      (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda (ReedSolomon.code α 128 : Set (Fin 256 → F))
            (((127 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ) :
              ENNReal) := by
    simpa [Fintype.card_fin] using hover
  have hlt127 := listLatticeThreshold_lt_of_overflow
    (C := (ReedSolomon.code α 128 : Set (Fin 256 → F))) (m := 1) (j := 127)
    hover127 hne
  have hle126 :
      GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1
          ((1 : ℝ≥0) / 2 ^ 128) hne ≤ 126 := by
    omega
  exact ⟨hne, hlo, hle126⟩

#print axioms rs_ld_threshold_subcapacity_rate12

end ProximityGap
