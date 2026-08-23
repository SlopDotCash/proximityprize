/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSLambdaJohnson
import ArkLib.Data.CodingTheory.ProximityGap.LDThreshold

/-!
# General Johnson-radius pin: `δ*` trapped in the open gap for every rate (#232)

Master form of `rs_ld_threshold_johnson_pin_rate16`: a single two-sided trap of the genuine
list-decoding threshold `δ*` at the **Johnson radius**, valid for every Reed–Solomon code, every
budget-clearing field, and every lattice radius `j` inside the Johnson regime.

  `rs_ld_threshold_johnson_pin_general` — for `RS[F, α, k]` with `k ≤ n = |ι|`, single column
  `m = 1`, any `ε* < 1`, and any grid index `j ≤ n` with the second-moment Johnson gap
  `n·(k−1) < (n−j)²` whose list cap clears the budget
  (`⌊n²/((n−j)²−n(k−1))⌋ ≤ ε*·|F|`):

      `j  ≤  listLatticeThreshold  ≤  n − k`.

The lower bound comes from `reedSolomon_Lambda_le_johnson` (elementary second-moment bound, no
Guruswami–Sudan multiplicity interpolation); the upper bound is the capacity ceiling
`listLatticeThreshold_le_capacity`. Taking `j` at the integer Johnson radius
`j = n − ⌈√(n(k−1))⌉` and a large field, this traps `δ*` into the open gap `[1 − √ρ, 1 − ρ)` for
each prize rate. Concretely on `n = 256`, `ε* = 2^{-128}` (large `|F|`):

| rate `ρ` | `k`  | Johnson index `j` | list cap `ℓ` | capacity `n−k` | δ-trap            |
|----------|------|-------------------|--------------|----------------|-------------------|
| `1/2`    | 128  | 75                | 263          | 128            | `[0.293, 0.5]`    |
| `1/4`    | 64   | 129               | 65536        | 192            | `[0.504, 0.75]`   |
| `1/8`    | 32   | 166               | 399          | 224            | `[0.648, 0.875]`  |
| `1/16`   | 16   | 194               | 16384        | 240            | `[0.758, 0.9375]` |

Pinning `δ*` *inside* each gap is the open $1M problem. This file traps it to the gap boundary for
the whole prize-rate family and fabricates nothing. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **General Johnson-radius two-sided pin.** For `RS[F, α, k]` with `k ≤ n`, `m = 1`, any `ε* < 1`,
and any grid index `j ≤ n` satisfying the second-moment Johnson gap `n·(k−1) < (n−j)²` with the
list cap `⌊n²/((n−j)²−n(k−1))⌋` clearing the budget, the list-decoding lattice is nonempty and its
threshold satisfies `j ≤ listLatticeThreshold ≤ n − k`. -/
theorem rs_ld_threshold_johnson_pin_general
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (α : ι ↪ F) {k j : ℕ} [NeZero k] (hk : k ≤ Fintype.card ι) (hjn : j ≤ Fintype.card ι)
    (hgap : Fintype.card ι * (k - 1) < (Fintype.card ι - j) ^ 2)
    {ε_star : ℝ≥0} (hε : ε_star < 1)
    (hbud : ((Fintype.card ι ^ 2 /
        ((Fintype.card ι - j) ^ 2 - Fintype.card ι * (k - 1)) : ℕ) : ENNReal)
      ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α k : Set (ι → F)) 1 ε_star).Nonempty,
      j ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α k : Set (ι → F)) 1 ε_star hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α k : Set (ι → F)) 1 ε_star hne ≤ Fintype.card ι - k := by
  classical
  have hne0 : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  -- the radius `j/n` has floor `j`
  have hfloor : ⌊(((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      * (Fintype.card ι : ℝ)⌋₊ = j := by
    have heq : (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
        * (Fintype.card ι : ℝ) = (j : ℝ) := by
      push_cast; field_simp
    rw [heq, Nat.floor_natCast]
  -- **Lower side**: Johnson cap `Λ(RS, j/n) ≤ ⌊n²/((n−j)²−n(k−1))⌋`.
  have hLam : ListDecodable.Lambda ((ReedSolomon.code α k : Set (ι → F)))
      (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ ((Fintype.card ι ^ 2 /
          ((Fintype.card ι - j) ^ 2 - Fintype.card ι * (k - 1)) : ℕ) : ℕ∞) := by
    have hb := reedSolomon_Lambda_le_johnson (F := F) (ι := ι) (k := k) (α := α)
      (δ := (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ))
      (by rw [hfloor]; exact hgap)
    rw [hfloor] at hb
    exact hb
  have hpow : (((Fintype.card ι ^ 2 /
        ((Fintype.card ι - j) ^ 2 - Fintype.card ι * (k - 1)) : ℕ) : ENNReal)) ^ (1 : ℕ)
      ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal) := by
    rw [pow_one]; exact hbud
  have hmem := mem_listLatticeSet_of_Lambda_le
    (C := (ReedSolomon.code α k : Set (ι → F))) (m := 1) (j := j)
    (ℓ := Fintype.card ι ^ 2 / ((Fintype.card ι - j) ^ 2 - Fintype.card ι * (k - 1)))
    hjn hLam hpow
  refine ⟨⟨j, hmem⟩, ?_, ?_⟩
  · exact le_listLatticeThreshold_of_Lambda_le
      (C := (ReedSolomon.code α k : Set (ι → F))) (m := 1) (j := j)
      (ℓ := Fintype.card ι ^ 2 / ((Fintype.card ι - j) ^ 2 - Fintype.card ι * (k - 1)))
      hjn hLam hpow ⟨j, hmem⟩
  · exact listLatticeThreshold_le_capacity (F := F) (ι := ι) α (deg := k) (m := 1)
      hk (by norm_num) hε ⟨j, hmem⟩

#print axioms rs_ld_threshold_johnson_pin_general

end ProximityGap
