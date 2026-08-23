/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# Basic facts about the q-ary Hamming-ball volume

Monotonicity, positivity, the whole-space ceiling `Vol ≤ q^n`, and the full-space equality
`Vol = q^n` for `δ ≥ 1`, for `CodingTheory.hammingBallVolume` (ABF26 Def 2.4) — complementing the
entropy-volume *bounds* in `EntropyVolumeBound.lean`.
-/

namespace CodingTheory

/-- **Monotonicity of the Hamming-ball volume in the relative radius.** -/
theorem hammingBallVolume_mono (q n : ℕ) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    hammingBallVolume q δ₁ n ≤ hammingBallVolume q δ₂ n := by
  unfold hammingBallVolume
  apply Finset.sum_le_sum_of_subset
  apply Finset.range_mono
  exact Nat.succ_le_succ
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n)))

/-- Real-valued form of `hammingBallVolume_mono`. -/
theorem hammingBallVolume_real_mono (q n : ℕ) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    (hammingBallVolume q δ₁ n : ℝ) ≤ (hammingBallVolume q δ₂ n : ℝ) := by
  exact_mod_cast hammingBallVolume_mono q n hδ

/-- **The Hamming-ball volume is at least one** — the centre (the `i = 0` layer) is always counted. -/
theorem one_le_hammingBallVolume (q : ℕ) (δ : ℝ) (n : ℕ) :
    1 ≤ hammingBallVolume q δ n := by
  unfold hammingBallVolume
  calc 1 = Nat.choose n 0 * (q - 1) ^ 0 := by simp
    _ ≤ ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i :=
        Finset.single_le_sum (f := fun i => Nat.choose n i * (q - 1) ^ i)
          (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos _))

/-- **The q-ary Hamming-ball volume never exceeds the whole space `q^n`** (for `1 ≤ q`). -/
theorem hammingBallVolume_le_qpow (q : ℕ) (hq : 1 ≤ q) (δ : ℝ) (n : ℕ) :
    hammingBallVolume q δ n ≤ q ^ n := by
  have hfull : ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (q - 1) ^ i = q ^ n := by
    have h := add_pow (q - 1) 1 n
    simp only [one_pow, mul_one, Nat.cast_id] at h
    rw [Nat.sub_add_cancel hq] at h
    rw [h]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hzero : ∀ i, n < i → Nat.choose n i * (q - 1) ^ i = 0 := by
    intro i hi; rw [Nat.choose_eq_zero_of_lt hi, Nat.zero_mul]
  unfold hammingBallVolume
  rcases Nat.lt_or_ge (⌊δ * n⌋₊ + 1) (n + 1) with hlt | hge
  · calc ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i
        ≤ ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (q - 1) ^ i :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (le_of_lt hlt))
      _ = q ^ n := hfull
  · have heq : ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i
        = ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (q - 1) ^ i := by
      refine (Finset.sum_subset (Finset.range_mono hge) ?_).symm
      intro i _ hni
      rw [Finset.mem_range, not_lt] at hni
      exact hzero i (by omega)
    rw [heq, hfull]

/-- **Full-space ball: `Vol_q(δ,n) = q^n` for `δ ≥ 1`** (and `1 ≤ q`). The floor `⌊δ·n⌋ ≥ n`, so the
layer sum covers all of `range (n+1)`. -/
theorem hammingBallVolume_eq_qpow_of_one_le (q : ℕ) (hq : 1 ≤ q) {δ : ℝ} (hδ : 1 ≤ δ) (n : ℕ) :
    hammingBallVolume q δ n = q ^ n := by
  refine le_antisymm (hammingBallVolume_le_qpow q hq δ n) ?_
  have hfull : ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (q - 1) ^ i = q ^ n := by
    have h := add_pow (q - 1) 1 n
    simp only [one_pow, mul_one, Nat.cast_id] at h
    rw [Nat.sub_add_cancel hq] at h
    rw [h]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [← hfull]
  unfold hammingBallVolume
  apply Finset.sum_le_sum_of_subset
  apply Finset.range_mono
  have hle : n ≤ ⌊δ * (n : ℝ)⌋₊ :=
    Nat.le_floor (by nlinarith [Nat.cast_nonneg (α := ℝ) n, hδ])
  exact Nat.succ_le_succ hle

end CodingTheory

#print axioms CodingTheory.hammingBallVolume_mono
#print axioms CodingTheory.one_le_hammingBallVolume
#print axioms CodingTheory.hammingBallVolume_le_qpow
#print axioms CodingTheory.hammingBallVolume_eq_qpow_of_one_le
