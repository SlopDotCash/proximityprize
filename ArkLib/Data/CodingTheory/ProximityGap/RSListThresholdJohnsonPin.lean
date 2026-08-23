/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSLambdaJohnson
import ArkLib.Data.CodingTheory.ProximityGap.LDThreshold

/-!
# Concrete Johnson-radius pin: `δ*` trapped in exactly the open gap (#232)

The strongest concrete formalized statement reachable without the open breakthrough: for a concrete
prize-rate Reed–Solomon code over a large field, the genuine list-decoding threshold `δ*` is trapped
*exactly* in the open Johnson→capacity gap `[1 − √ρ, 1 − ρ)`.

  `rs_ld_threshold_johnson_pin_rate16` — for `RS[F, α, 16]` on a size-`256` domain (`ρ = 1/16`),
  `m = 1`, `ε* = 2^{-128}`, over any field with `256·2^128 ≤ |F|`:

      `192 ≤ listLatticeThreshold ≤ 240`,   i.e.   `0.75 ≤ δ* ≤ 0.9375`.

The lower index `192` is the **Johnson radius** `1 − √ρ = 0.75` exactly (`reedSolomon_Lambda_le_johnson`
gives `Λ(RS, 192/256) ≤ 256` at the second-moment gap `256·15 = 3840 < 64² = 4096`, and the
list size `256 = 2^8` clears the budget `ε*·|F| ≥ 2^8`); the upper index `240 = n − k` is the
capacity radius `1 − ρ` (`listLatticeThreshold_le_capacity`). The negative-side analysis shows the
upper end is not attained.

So `δ*` is now formally caught in `[1 − √ρ, 1 − ρ)` — *exactly the open prize gap*, with the lower
edge at the Johnson radius reached by the elementary second-moment bound alone (no Guruswami–Sudan
multiplicity interpolation). Pinning the exact value *inside* this gap is the open $1M problem; this
file traps it to the gap boundary and fabricates nothing.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Concrete Johnson-radius two-sided pin (rate `1/16`).** For `RS[F, α, 16]` on a size-`256`
domain, `m = 1`, `ε* = 2^{-128}`, over any field with `256·2^128 ≤ |F|`, the list-decoding lattice
is nonempty and its threshold satisfies `192 ≤ δ*-index ≤ 240` — i.e. `δ*` is trapped in
`[0.75, 0.9375] = [1 − √ρ, 1 − ρ]`, exactly the open Johnson→capacity gap. -/
theorem rs_ld_threshold_johnson_pin_rate16
    {F : Type} [Field F] [Fintype F] [DecidableEq F] (α : Fin 256 ↪ F)
    (hF : (256 : ℕ) * 2 ^ 128 ≤ Fintype.card F) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α 16 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128)).Nonempty,
      192 ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 16 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 16 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne ≤ 240 := by
  classical
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have hjn : (192 : ℕ) ≤ Fintype.card (Fin 256) := by rw [Fintype.card_fin]; norm_num
  have hfloor : ⌊(((192 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ)
      * (Fintype.card (Fin 256) : ℝ)⌋₊ = 192 := by
    rw [Fintype.card_fin]
    rw [show (((192 : ℝ≥0) / ((256 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) = (192 : ℝ) / 256 by push_cast; ring]
    norm_num
  -- the Johnson list-size cap evaluates to 256 (= 2^8)
  have hl : (Fintype.card (Fin 256) ^ 2 /
      ((Fintype.card (Fin 256) - 192) ^ 2 - Fintype.card (Fin 256) * (16 - 1)) : ℕ) = 256 := by
    simp only [Fintype.card_fin]; norm_num
  -- **Lower side**: Johnson-radius cap `Λ(RS[16], 192/256) ≤ 256`.
  have hLam : ListDecodable.Lambda ((ReedSolomon.code α 16 : Set (Fin 256 → F)))
      (((192 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((256 : ℕ) : ℕ∞) := by
    have hb := reedSolomon_Lambda_le_johnson (F := F) (ι := Fin 256) (k := 16) (α := α)
      (δ := (((192 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ))
      (by rw [hfloor, Fintype.card_fin]; norm_num)
    rw [hfloor, hl] at hb
    exact hb
  -- **Budget**: `ℓ = 256 = 2^8 ≤ ε*·|F|` since `|F| ≥ 256·2^128`.
  have hbudget : ((256 : ℕ) : ENNReal) ≤
      (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ENNReal) * (Fintype.card F : ENNReal) := by
    have hr : (256 : ℝ≥0) ≤ ((1 : ℝ≥0) / 2 ^ 128) * (Fintype.card F : ℝ≥0) := by
      have hFr : (256 : ℝ≥0) * (2 : ℝ≥0) ^ 128 ≤ (Fintype.card F : ℝ≥0) := by exact_mod_cast hF
      have hmul := mul_le_mul_left' hFr ((1 : ℝ≥0) / 2 ^ 128)
      have hone : ((1 : ℝ≥0) / 2 ^ 128) * ((256 : ℝ≥0) * 2 ^ 128) = 256 := by
        rw [one_div, mul_comm (256 : ℝ≥0) ((2 : ℝ≥0) ^ 128), ← mul_assoc,
          inv_mul_cancel₀ (by positivity), one_mul]
      rwa [hone] at hmul
    rw [← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_mul]
    exact_mod_cast hr
  have hpow : ((256 : ℕ) : ENNReal) ^ (1 : ℕ) ≤
      (((1 : ℝ≥0) / 2 ^ 128 : ℝ≥0) : ENNReal) * (Fintype.card F : ENNReal) := by
    rw [pow_one]; exact hbudget
  have hmem := mem_listLatticeSet_of_Lambda_le
    (C := (ReedSolomon.code α 16 : Set (Fin 256 → F))) (m := 1) (j := 192) (ℓ := 256)
    hjn hLam hpow
  refine ⟨⟨192, hmem⟩, ?_, ?_⟩
  · exact le_listLatticeThreshold_of_Lambda_le
      (C := (ReedSolomon.code α 16 : Set (Fin 256 → F))) (m := 1) (j := 192) (ℓ := 256)
      hjn hLam hpow ⟨192, hmem⟩
  · have hup := listLatticeThreshold_le_capacity (F := F) (ι := Fin 256) α (deg := 16) (m := 1)
      (by rw [Fintype.card_fin]; norm_num) (by norm_num)
      (ε_star := (1 : ℝ≥0) / 2 ^ 128)
      (by
        rw [one_div]
        exact inv_lt_one_of_one_lt₀ (by
          calc (1 : ℝ≥0) < 2 := by norm_num
            _ ≤ 2 ^ 128 := le_self_pow₀ (by norm_num) (by norm_num)))
      ⟨192, hmem⟩
    rw [Fintype.card_fin] at hup
    exact le_trans hup (by norm_num)

#print axioms rs_ld_threshold_johnson_pin_rate16

end ProximityGap
