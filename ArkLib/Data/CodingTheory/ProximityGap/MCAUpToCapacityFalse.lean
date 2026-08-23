/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCANearCapacityGeneralRate

/-!
# The up-to-capacity MCA bound is FALSE near capacity (#232, MCA negative side)

The mutual correlated agreement error `ε_mca` is what WHIR/STARK soundness actually needs. Here we
give an **admit-free** counterexample to the up-to-capacity MCA bound, driven by the sunflower
lower bound `ProximityGap.MCANearCapacityGK.epsMCA_ge_of_prefix_sunflower`
(`ε_mca(RS[α,k], 1−(k+1)/n) ≥ (n−k)/|F|`):

> For a Reed–Solomon code `RS[F, α, k]` with `1 ≤ k ≤ n` over a field with
> `|F| < (n−k)·2^128`, at the near-capacity radius `δ = 1 − (k+1)/n`:
>
>   `ε* < ε_mca(RS, δ)`,    `ε* = 2^{-128}`     (`rs_mca_uptoCapacity_false_of_smallField`).

So no resolution can place the MCA threshold `δ*` at or above `1 − (k+1)/n` in this field regime —
the up-to-capacity MCA conjecture fails. Unlike `MCAConjectureRefutation` (which routes through the
external `rs_epsCA_breakdown_cs25` admit), this is fully self-contained and axiom-clean.

The field bound `|F| < (n−k)·2^128` covers, at rate `1/2` with `n ≤ 2^40`, fields up to
`≈ 2^{167}`. The full prize range up to `2^256` requires `n^{Ω(1)}` bad scalars with a larger
exponent (the CS25 list-explosion spread), which is the genuinely open construction.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap.MCANearCapacityGK

open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- **The up-to-capacity MCA bound fails near capacity (small-field regime).** For an RS code with
`1 ≤ k ≤ n` over a field with `|F| < (n−k)·2^128`, the MCA error at the near-capacity radius
`δ = 1 − (k+1)/n` exceeds the prize threshold `ε* = 2^{-128}`. Hence the MCA threshold `δ*` cannot
reach `1 − (k+1)/n`. -/
theorem rs_mca_uptoCapacity_false_of_smallField [NeZero n] (domain : Fin n ↪ F)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hsmall : (Fintype.card F : ℝ) < ((n - k : ℕ) : ℝ) * 2 ^ 128) :
    ENNReal.ofReal (1 / 2 ^ 128)
      < epsMCA (F := F) (A := F)
          (ReedSolomon.code (domain := domain) k : Set (Fin n → F))
          (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)) := by
  refine lt_of_lt_of_le ?_ (epsMCA_ge_of_prefix_sunflower domain k hk hkn)
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnk : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
    by_contra h
    push_neg at h
    have hz : ((n - k : ℕ) : ℝ) = 0 := le_antisymm h (by positivity)
    rw [hz, zero_mul] at hsmall
    linarith [hqpos]
  -- rewrite the ENNReal ratio as an `ofReal`
  have hratio : ((n - k : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      = ENNReal.ofReal (((n - k : ℕ) : ℝ) / (Fintype.card F : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hqpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hratio, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  rw [lt_div_iff₀ hqpos]
  nlinarith [hsmall]

#print axioms rs_mca_uptoCapacity_false_of_smallField

end ProximityGap.MCANearCapacityGK
