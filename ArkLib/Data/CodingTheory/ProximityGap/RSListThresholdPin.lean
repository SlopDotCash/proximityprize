/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LDThreshold
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode

/-!
# A concrete two-sided pin of a Reed–Solomon list-decoding threshold (#232)

The faithful object of the Grand List-Decoding Challenge is
`GrandChallenges.listLatticeThreshold C m ε*` — the largest grid index `j` (relative radius `j/n`)
with `Λ(C^⋈m, j/n) ≤ ε*·|F|`.  Two one-sided value bounds on it already exist, hole-free:

* `ProximityGap.listLatticeThreshold_le_capacity` — the *capacity ceiling* `δ* ≤ 1 − ρ`
  (unconditional, from the `|F|`-sized vanishing family beyond capacity);
* `ProximityGap.le_listLatticeThreshold_of_Lambda_le` — a *generic lower certificate*: any
  base-code list-size cap `Λ(C, j/n) ≤ ℓ` whose `m`-th power clears the budget pushes
  `j ≤ δ*`.

This file *instantiates both at once* on a concrete prize-regime Reed–Solomon code, producing the
first end-to-end **nondegenerate two-sided trap** of an actual RS list-decoding threshold (and, en
route, the nonemptiness of its lattice).  For rate `ρ = 1/16` (`k = 16`, domain size `n = 256`),
single column `m = 1`, prize tolerance `ε* = 2^{-128}`, over **every** field with `2^128 ≤ |F|`:

  `rs_ld_threshold_pin_rate16` —  `112 ≤ listLatticeThreshold(RS[F,α,16], 1, 2^{-128}) ≤ 240`.

The lower index `112` is a Sudan unique-decoding radius (`Λ ≤ 1` via `reedSolomon_Lambda_le`,
which trivially clears the budget since `1 ≤ ε*·|F|` for `|F| ≥ 2^128`); the upper index `240`
is the capacity index `n − k`.  In δ-units this reads `0.4375 ≤ δ* ≤ 0.9375` — a genuine,
field-uniform, axiom-clean interval.

What remains open — the content of the prize — is *narrowing this interval*: the threshold's exact
position inside `[0.4375, 0.9375]`, and in particular whether it sits at the Johnson radius
`1 − √ρ = 0.75` or escapes toward capacity, is the unresolved breakthrough.  This file pins the
provable trap and leaves the open core explicit; it fabricates nothing.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Concrete two-sided pin of a Reed–Solomon list-decoding threshold (rate `1/16`).**
For the rate-`1/16` Reed–Solomon code `RS[F, α, 16]` on a size-`256` domain, with single column
`m = 1` and prize tolerance `ε* = 2^{-128}`, over any field with `2^128 ≤ |F|`, the faithful
list-decoding lattice is nonempty and its threshold satisfies `112 ≤ δ*-index ≤ 240`
(`0.4375 ≤ δ* ≤ 0.9375` in relative-radius units): a unique-decoding radius lower bounds it and
the capacity radius `1 − ρ` upper bounds it. -/
theorem rs_ld_threshold_pin_rate16
    {F : Type} [Field F] [Fintype F] [DecidableEq F] (α : Fin 256 ↪ F)
    (hF : (2 : ℕ) ^ 128 ≤ Fintype.card F) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α 16 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128)).Nonempty,
      112 ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 16 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α 16 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne ≤ 240 := by
  classical
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  -- lower index, radius, and the matching real radius `δ = 112/256`
  have hjn : (112 : ℕ) ≤ Fintype.card (Fin 256) := by rw [Fintype.card_fin]; norm_num
  -- floor of `δ·n` is the error budget `112`
  have hfloor : ⌊(((112 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ)
      * (Fintype.card (Fin 256) : ℝ)⌋₊ = 112 := by
    rw [Fintype.card_fin]
    rw [show (((112 : ℝ≥0) / ((256 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) = (112 : ℝ) / 256 by push_cast; ring]
    norm_num
  -- **Lower side**: Sudan unique-decoding cap `Λ(RS[16], 112/256) ≤ 1`.
  have hLam : ListDecodable.Lambda ((ReedSolomon.code α 16 : Set (Fin 256 → F)))
      (((112 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((1 : ℕ) : ℕ∞) :=
    ReedSolomon.reedSolomon_Lambda_le (ι := Fin 256) (F := F) (k := 16) (dX := 128) (dZ := 1)
      (α := α) (δ := (((112 : ℝ≥0) / (Fintype.card (Fin 256) : ℝ≥0) : ℝ≥0) : ℝ))
      (by positivity)
      (by rw [Fintype.card_fin]; norm_num)
      (by rw [hfloor, Fintype.card_fin]; norm_num)
      (by rw [hfloor, Fintype.card_fin]; norm_num)
  -- **Budget**: `ℓ^m = 1^1 = 1 ≤ ε*·|F|` because `|F| ≥ 2^128`.
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
  -- lattice membership at index `112` ⟹ nonemptiness, and the lower bound
  have hmem := mem_listLatticeSet_of_Lambda_le
    (C := (ReedSolomon.code α 16 : Set (Fin 256 → F))) (m := 1) (j := 112) (ℓ := 1)
    hjn hLam hpow
  refine ⟨⟨112, hmem⟩, ?_, ?_⟩
  · exact le_listLatticeThreshold_of_Lambda_le
      (C := (ReedSolomon.code α 16 : Set (Fin 256 → F))) (m := 1) (j := 112) (ℓ := 1)
      hjn hLam hpow ⟨112, hmem⟩
  · -- **Upper side**: capacity ceiling `δ* ≤ n − k = 256 − 16 = 240`.
    have hup := listLatticeThreshold_le_capacity (F := F) (ι := Fin 256) α (deg := 16) (m := 1)
      (by rw [Fintype.card_fin]; norm_num) (by norm_num)
      (ε_star := (1 : ℝ≥0) / 2 ^ 128)
      (by
        rw [one_div]
        exact inv_lt_one_of_one_lt₀ (by
          calc (1 : ℝ≥0) < 2 := by norm_num
            _ ≤ 2 ^ 128 := le_self_pow₀ (by norm_num) (by norm_num)))
      ⟨112, hmem⟩
    rw [Fintype.card_fin] at hup
    exact le_trans hup (by norm_num)

#print axioms rs_ld_threshold_pin_rate16

end ProximityGap
