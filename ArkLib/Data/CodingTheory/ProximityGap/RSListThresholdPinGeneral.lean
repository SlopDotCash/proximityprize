/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSListThresholdPinRate12

/-!
# General two-sided pin of every Reed–Solomon list-decoding threshold (#232)

Master consolidation of the concrete per-rate pins (`RSListThresholdPin.lean`,
`RSListThresholdPinRate12.lean`): a *single* two-sided trap valid for **every** Reed–Solomon code,
**every** field clearing the budget, and **every** rate at once.

  `rs_ld_threshold_pin_general` — for `RS[F, α, k]` on a domain of size `n = |ι|` with `k ≤ n`,
  single column `m = 1`, any tolerance `ε* < 1` with `1 ≤ ε*·|F|`:

      `(n − k)/2  ≤  listLatticeThreshold  ≤  n − k`.

The lower index `(n−k)/2` is the **unique-decoding radius** `δ_min/2` (via `reedSolomon_Lambda_le_one`,
the budget cleared by `ℓ = 1`); the upper index `n − k` is the **capacity radius** `1 − ρ`
(`listLatticeThreshold_le_capacity`).  In δ-units: `(1−ρ)/2 ≤ δ* ≤ 1 − ρ`.

Specializing to the four prize rates on `n = 256`, `ε* = 2^{-128}`, `|F| ≥ 2^128`:

| rate `ρ` | `k`  | lower `(n−k)/2` | upper `n−k` | δ-interval        |
|----------|------|-----------------|-------------|-------------------|
| `1/2`    | 128  | 64              | 128         | `[0.25, 0.5]`     |
| `1/4`    | 64   | 96              | 192         | `[0.375, 0.75]`   |
| `1/8`    | 32   | 112             | 224         | `[0.4375, 0.875]` |
| `1/16`   | 16   | 120             | 240         | `[0.46875, 0.9375]` |

What stays open — the content of the prize — is *narrowing each interval* to the exact `δ*`, in
particular whether it reaches the Johnson radius `1 − √ρ`. This file pins the provable trap for the
entire prize-rate family uniformly and fabricates nothing.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **General two-sided pin of a Reed–Solomon list-decoding threshold.** For any Reed–Solomon code
`RS[F, α, k]` with `k ≤ n = |ι|`, single column `m = 1`, and any prize tolerance `ε* < 1` whose
budget is cleared by a single codeword (`1 ≤ ε*·|F|`), the faithful list-decoding lattice is
nonempty and its threshold is trapped between the unique-decoding radius `(n−k)/2` and the capacity
radius `n−k`. -/
theorem rs_ld_threshold_pin_general
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (α : ι ↪ F) {k : ℕ} [NeZero k] (hk : k ≤ Fintype.card ι)
    {ε_star : ℝ≥0} (hε : ε_star < 1)
    (hbud : (1 : ℝ≥0) ≤ ε_star * (Fintype.card F : ℝ≥0)) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α k : Set (ι → F)) 1 ε_star).Nonempty,
      (Fintype.card ι - k) / 2 ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α k : Set (ι → F)) 1 ε_star hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α k : Set (ι → F)) 1 ε_star hne ≤ Fintype.card ι - k := by
  classical
  set j_lo : ℕ := (Fintype.card ι - k) / 2 with hjlo
  have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
  have hjn : j_lo ≤ Fintype.card ι := by omega
  -- the radius `j_lo / n` has floor `j_lo`
  have hne0 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcardpos.ne'
  have hfloor : ⌊(((j_lo : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      * (Fintype.card ι : ℝ)⌋₊ = j_lo := by
    have heq : (((j_lo : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
        * (Fintype.card ι : ℝ) = (j_lo : ℝ) := by
      push_cast
      field_simp
    rw [heq, Nat.floor_natCast]
  -- **Lower side**: unique-decoding cap `Λ(RS, j_lo/n) ≤ 1`.
  have hLam : ListDecodable.Lambda ((ReedSolomon.code α k : Set (ι → F)))
      (((j_lo : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((1 : ℕ) : ℕ∞) := by
    have hb := reedSolomon_Lambda_le_one (F := F) (ι := ι) (k := k) (α := α) hk
      (δ := (((j_lo : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ))
      (by rw [hfloor]; omega)
    exact_mod_cast hb
  -- **Budget**: `ℓ^m = 1 ≤ ε*·|F|`.
  have hpow : ((1 : ℕ) : ENNReal) ^ (1 : ℕ) ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal) := by
    rw [Nat.cast_one, one_pow, ← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_mul]
    exact_mod_cast hbud
  have hmem := mem_listLatticeSet_of_Lambda_le
    (C := (ReedSolomon.code α k : Set (ι → F))) (m := 1) (j := j_lo) (ℓ := 1) hjn hLam hpow
  refine ⟨⟨j_lo, hmem⟩, ?_, ?_⟩
  · exact le_listLatticeThreshold_of_Lambda_le
      (C := (ReedSolomon.code α k : Set (ι → F))) (m := 1) (j := j_lo) (ℓ := 1)
      hjn hLam hpow ⟨j_lo, hmem⟩
  · exact listLatticeThreshold_le_capacity (F := F) (ι := ι) α (deg := k) (m := 1)
      hk (by norm_num) hε ⟨j_lo, hmem⟩

#print axioms rs_ld_threshold_pin_general

end ProximityGap
