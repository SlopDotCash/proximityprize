/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StructureLoop38

/-!
# Loop 39 (PROOF, conditional) — capstone: BGM budget × FRI union bound ⟹ full-band prize

This file integrates the two frontiers that Loops 37 and 38 isolated:

* **Loop 17 (P4)** — the Brakensiek–Gopi–Makam *generic* list-decoding-capacity budget at the
  prize radius, `L_BGM(ρ,η) = (1−ρ−η)/η ≤ 1/η`, is `q`-independent and carries no `n`/`(2^m)`
  factor. It is the one budget finite across the **entire** band `0 < η ≤ 1−ρ`, including the
  small-gap region `0 < η ≤ η₀` the Johnson method cannot reach.
* **Loop 38** — the actual BCIKS proximity-gaps / FRI soundness mechanism composes its `m`
  per-round events as a **union bound** `∑_{j<m} e_j`, additive, never a multiplicative tower.

Composing them: if each per-round proximity event is the one-shot BGM event `e_j ≤ L_BGM(ρ,η)/q`,
then the union-bound total error obeys

    err ≤ ∑_{j<m} e_j ≤ m · L_BGM(ρ,η)/q ≤ m/(η·q) ≤ (2^m)/(η·q)
        = (1/q) · (2^m)^1 / η^1 ,

i.e. **exactly the prize RHS** with the single constant triple `c₁ = 1, c₂ = 0, c₃ = 1`, for
**every** gap `η > 0`, including the small-gap band. This is the first statement that lands the
prize on its own RHS *across the entire band* (not just the Johnson range) from one clean
hypothesis, in the shape the real FRI mechanism actually produces.

The hypothesis discharged here, `hround : ∀ j < m, e j ≤ L_BGM(ρ,η)/q`, is precisely
**(BGM-for-smooth)**: that the deterministic smooth multiplicative-subgroup RS code's per-round
proximity event is bounded by the *generic* BGM capacity budget. In the Johnson range it is the
BCIKS 2025/2055 theorem (so the prize is unconditional there); in the small-gap band it is the
genuine open core. This brick is conditional and does **not** close the prize — it certifies that
the open core is reduced to exactly one hypothesis, and that hypothesis lands the prize. See
`DISPROOF_LOG.md` (Loop39).
-/

namespace ArkLib.ProximityGap.ProofLoop39

open scoped BigOperators

/-- The BGM (generic list-decoding capacity) budget at the prize radius: `(1−ρ−η)/η`. -/
noncomputable def bgmBudget (ρ η : ℝ) : ℝ := (1 - ρ - η) / η

/-- The BGM budget is at most `1/η` for `ρ ≥ 0` and positive gap `η`. -/
theorem bgmBudget_le_inv_gap {ρ η : ℝ} (hρ : 0 ≤ ρ) (hη : 0 < η) :
    bgmBudget ρ η ≤ 1 / η := by
  unfold bgmBudget
  gcongr
  linarith

/-- The BGM budget is nonnegative for a below-capacity radius and positive gap. -/
theorem bgmBudget_nonneg {ρ η : ℝ} (hcap : 0 ≤ 1 - ρ - η) (hη : 0 < η) :
    0 ≤ bgmBudget ρ η := by
  unfold bgmBudget
  positivity

/-- **Integration capstone (conditional): the full-band prize mass clause.**
If every per-round FRI/proximity event `e j` is bounded by the one-shot BGM capacity event
`L_BGM(ρ,η)/q`, then the union-bound total error over the `m` fold rounds lands on the prize RHS

    ∑_{j<m} e j ≤ (1/q) · (2^m)^1 / η ,

with the single constant triple `c₁ = 1, c₂ = 0, c₃ = 1`, for **every** gap `η > 0` — including
the small-gap band the Johnson method cannot reach. The per-round budget is carried *once* (into
the depth-independent factor `1/η`), exactly as Loop 37 requires, and accumulated *additively*
(the union bound), exactly as Loop 38 establishes for the real mechanism. -/
theorem full_band_prize_mass
    (e : ℕ → ℝ) {ρ η q : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ) (hcap : 0 ≤ 1 - ρ - η) (hη : 0 < η) (hq : 0 < q)
    (hround : ∀ j, j < m → e j ≤ bgmBudget ρ η / q) :
    (∑ j ∈ Finset.range m, e j) ≤ (1 / q) * ((2 : ℝ) ^ m) ^ 1 / η := by
  -- union bound (Loop 38): total ≤ m · (one-shot per-round budget)
  have hUnion :
      (∑ j ∈ Finset.range m, e j) ≤ (m : ℝ) * (bgmBudget ρ η / q) :=
    ArkLib.ProximityGap.StructureLoop38.fri_union_bound e hround
  -- per-round budget ≤ 1/(η·q)
  have hpr : bgmBudget ρ η / q ≤ 1 / (η * q) := by
    have hb : bgmBudget ρ η ≤ 1 / η := bgmBudget_le_inv_gap hρ hη
    calc bgmBudget ρ η / q ≤ (1 / η) / q := by gcongr
      _ = 1 / (η * q) := by rw [div_div]
  have hbnn : 0 ≤ bgmBudget ρ η / q := by
    have := bgmBudget_nonneg hcap hη
    positivity
  -- m ≤ 2^m
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have h := Nat.lt_two_pow_self (n := m)
    calc (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h.le
      _ = (2 : ℝ) ^ m := by push_cast; ring
  have hηq : 0 < η * q := mul_pos hη hq
  calc
    (∑ j ∈ Finset.range m, e j)
        ≤ (m : ℝ) * (bgmBudget ρ η / q) := hUnion
    _ ≤ (m : ℝ) * (1 / (η * q)) := by gcongr
    _ ≤ ((2 : ℝ) ^ m) * (1 / (η * q)) := by gcongr
    _ = (1 / q) * ((2 : ℝ) ^ m) ^ 1 / η := by rw [pow_one]; field_simp

end ArkLib.ProximityGap.ProofLoop39

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ProofLoop39.bgmBudget_le_inv_gap
#print axioms ArkLib.ProximityGap.ProofLoop39.bgmBudget_nonneg
#print axioms ArkLib.ProximityGap.ProofLoop39.full_band_prize_mass
