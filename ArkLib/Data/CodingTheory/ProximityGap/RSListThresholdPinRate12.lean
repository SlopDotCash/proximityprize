/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LDThreshold
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode

/-!
# Rate-`1/2` two-sided pin of a Reed–Solomon list-decoding threshold (#232)

Companion to `RSListThresholdPin.lean` (rate `1/16`), at the **headline prize rate** `ρ = 1/2`
that matches the negative-side capstone `rs_uptoCapacity_false_rate12_n256` (`δ* < 1 − ρ = 1/2`).

The Sudan list-size bound degenerates at high rate (at `ρ = 1/2` it yields error budget `0`), so the
rate-`1/2` lower side needs the *minimum-distance* unique-decoding bound instead. This file proves a
clean, reusable

  `reedSolomon_Lambda_le_one` — `2⌊δn⌋ < n − k + 1  ⟹  Λ(RS[k], δ) ≤ 1`,

directly from `ReedSolomon.unique_decode` (two codewords within the unique-decoding radius of a
common word coincide ⇒ each point list is a subsingleton). Combined with the unconditional capacity
ceiling `ProximityGap.listLatticeThreshold_le_capacity`, this pins the genuine rate-`1/2` RS
list-decoding threshold:

  `rs_ld_threshold_pin_rate12` —  for `RS[F, α, 128]` on a size-`256` domain, `m = 1`,
  `ε* = 2^{-128}`, over every field with `2^128 ≤ |F|`:
  `64 ≤ listLatticeThreshold ≤ 128`,  i.e.  `0.25 ≤ δ* ≤ 0.5` (unique-decoding radius `δ_min/2`
  to capacity `1 − ρ`).

The negative-side result shows the upper end is *not attained* (`δ* < 1/2` strictly); pinning the
exact value inside `[0.25, 0.5]` — in particular whether it reaches the Johnson radius
`1 − √(1/2) ≈ 0.293` or beyond — is the open prize. Nothing here is fabricated.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Reed–Solomon unique-decoding list cap `Λ(RS, δ) ≤ 1`.** If `2⌊δn⌋ < n − k + 1` (the
unique-decoding radius `δ < δ_min/2`), every point list `Λ(RS[k], δ, f)` is a subsingleton — by
`ReedSolomon.unique_decode`, two codewords within `⌊δn⌋` Hamming errors of a common word `f`
coincide — so the maximised list size is at most `1`. -/
theorem reedSolomon_Lambda_le_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {k : ℕ} [NeZero k] {α : ι ↪ F} (hk : k ≤ Fintype.card ι)
    {δ : ℝ} (he : 2 * ⌊δ * Fintype.card ι⌋₊ < Fintype.card ι - k + 1) :
    ListDecodable.Lambda ((ReedSolomon.code α k : Set (ι → F))) δ ≤ (1 : ℕ∞) := by
  classical
  -- relative-distance membership ⟹ Hamming distance ≤ ⌊δn⌋
  have hbridge : ∀ c f : ι → F, c ∈ ListDecodable.closeCodewordsRel
      ((ReedSolomon.code α k : Set (ι → F))) f δ →
      hammingDist f c ≤ ⌊δ * Fintype.card ι⌋₊ := by
    intro c f hc
    have hrel : (Code.relHammingDist f c : ℝ) ≤ δ := by
      have h := hc.2
      simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq] at h
      convert h using 3
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hreleq : (Code.relHammingDist f c : ℝ) = (hammingDist f c : ℝ) / Fintype.card ι := by
      rw [Code.relHammingDist]; push_cast; ring
    rw [hreleq, div_le_iff₀ hn] at hrel
    exact Nat.le_floor hrel
  -- each point list is a subsingleton
  have hsub : ∀ f : ι → F, (ListDecodable.closeCodewordsRel
      ((ReedSolomon.code α k : Set (ι → F))) f δ).Subsingleton := by
    intro f c hc c' hc'
    exact ReedSolomon.unique_decode hk hc.1 hc'.1 (hbridge c f hc) (hbridge c' f hc') he
  -- subsingleton ⟹ ncard ≤ 1 ⟹ Lambda ≤ 1
  have hcard : ∀ f : ι → F, (ListDecodable.closeCodewordsRel
      ((ReedSolomon.code α k : Set (ι → F))) f δ).ncard ≤ 1 := by
    intro f
    rcases (hsub f).eq_empty_or_singleton with h | ⟨a, h⟩ <;> rw [h] <;> simp
  have hmain := ListDecodable.Lambda_le_natCast_of_forall_ncard_le
    (C := (ReedSolomon.code α k : Set (ι → F))) (δ := δ) (ℓ := 1) hcard
  simpa using hmain

/-- **Concrete two-sided pin of a Reed–Solomon list-decoding threshold (rate `1/2`).**
For the rate-`1/2` Reed–Solomon code `RS[F, α, 128]` on a size-`256` domain, with single column
`m = 1` and prize tolerance `ε* = 2^{-128}`, over any field with `2^128 ≤ |F|`, the faithful
list-decoding lattice is nonempty and its threshold satisfies `64 ≤ δ*-index ≤ 128`
(`0.25 ≤ δ* ≤ 0.5` in relative-radius units): the unique-decoding radius `δ_min/2` lower bounds it
and the capacity radius `1 − ρ` upper bounds it. (The negative-side
`rs_uptoCapacity_false_rate12_n256` further shows the upper end is not attained.) -/
theorem rs_ld_threshold_pin_rate12
    {F : Type} [Field F] [Fintype F] [DecidableEq F] (α : Fin 256 ↪ F)
    (hF : (2 : ℕ) ^ 128 ≤ Fintype.card F) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128)).Nonempty,
      64 ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne ≤ 128 := by
  classical
  haveI : NeZero (128 : ℕ) := ⟨by norm_num⟩
  have hjn : (64 : ℕ) ≤ Fintype.card (Fin 256) := by rw [Fintype.card_fin]; norm_num
  have hfloor : ⌊(((64 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ)
      * (Fintype.card (Fin 256) : ℝ)⌋₊ = 64 := by
    rw [Fintype.card_fin]
    rw [show (((64 : ℝ≥0) / ((256 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) = (64 : ℝ) / 256 by push_cast; ring]
    norm_num
  -- **Lower side**: unique-decoding cap `Λ(RS[128], 64/256) ≤ 1`.
  have hLam : ListDecodable.Lambda ((ReedSolomon.code α 128 : Set (Fin 256 → F)))
      (((64 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((1 : ℕ) : ℕ∞) := by
    have hb := reedSolomon_Lambda_le_one (F := F) (ι := Fin 256) (k := 128) (α := α)
      (by rw [Fintype.card_fin]; norm_num)
      (δ := (((64 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ))
      (by rw [hfloor, Fintype.card_fin]; norm_num)
    exact_mod_cast hb
  -- **Budget**: `ℓ^m = 1 ≤ ε*·|F|` because `|F| ≥ 2^128`.
  have h2ne : (2 : ℝ≥0) ^ 128 ≠ 0 := pow_ne_zero _ (by norm_num)
  have hbudget : (1 : ENNReal) ≤
      (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ENNReal) * (Fintype.card F : ENNReal) := by
    have hr : (1 : ℝ≥0) ≤ ((1 : ℝ≥0) / 2 ^ 128) * (Fintype.card F : ℝ≥0) := by
      have hFr : (2 : ℝ≥0) ^ 128 ≤ (Fintype.card F : ℝ≥0) := by exact_mod_cast hF
      have hmul := mul_le_mul_left' hFr ((1 : ℝ≥0) / 2 ^ 128)
      have hone : ((1 : ℝ≥0) / 2 ^ 128) * (2 : ℝ≥0) ^ 128 = 1 := by
        rw [one_div, inv_mul_cancel₀ h2ne]
      rwa [hone] at hmul
    rw [← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_mul]
    exact_mod_cast hr
  have hpow : ((1 : ℕ) : ENNReal) ^ (1 : ℕ) ≤
      (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ENNReal) * (Fintype.card F : ENNReal) := by
    rw [Nat.cast_one, one_pow]; exact hbudget
  have hmem := mem_listLatticeSet_of_Lambda_le
    (C := (ReedSolomon.code α 128 : Set (Fin 256 → F))) (m := 1) (j := 64) (ℓ := 1)
    hjn hLam hpow
  refine ⟨⟨64, hmem⟩, ?_, ?_⟩
  · exact le_listLatticeThreshold_of_Lambda_le
      (C := (ReedSolomon.code α 128 : Set (Fin 256 → F))) (m := 1) (j := 64) (ℓ := 1)
      hjn hLam hpow ⟨64, hmem⟩
  · -- **Upper side**: capacity ceiling `δ* ≤ n − k = 256 − 128 = 128`.
    have hup := listLatticeThreshold_le_capacity (F := F) (ι := Fin 256) α (deg := 128) (m := 1)
      (by rw [Fintype.card_fin]; norm_num) (by norm_num)
      (ε_star := (1 : ℝ≥0) / 2 ^ 128)
      (by
        rw [one_div]
        exact inv_lt_one_of_one_lt₀ (by
          calc (1 : ℝ≥0) < 2 := by norm_num
            _ ≤ 2 ^ 128 := le_self_pow₀ (by norm_num) (by norm_num)))
      ⟨64, hmem⟩
    rw [Fintype.card_fin] at hup
    exact le_trans hup (by norm_num)

#print axioms reedSolomon_Lambda_le_one
#print axioms rs_ld_threshold_pin_rate12

end ProximityGap
