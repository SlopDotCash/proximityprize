/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarCapacity
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDRBound

/-!
# Concrete two-sided bracket on the MCA threshold (#232, MCA Grand Challenge)

The MCA analog of the list-decoding strict bracket, on the faithful continuous threshold
`mcaDeltaStar C ε* = sSup {δ | ε_mca(C, δ) ≤ ε*}`:

  `rs_mcaDeltaStar_bracket` — for `RS[F, domain, k]` in the unique-decoding regime
  `3(n − ⌈(1−δ)n⌉) < n − k + 1` over a field window
  `2(n − ⌈(1−δ)n⌉)·2^128 ≤ |F| < (n−k)·2^128`:

      `δ  ≤  mcaDeltaStar(RS, 2^{-128})  ≤  1 − (k+1)/n`.

The lower side is the unique-decoding MCA bound `epsMCA_rs_udr_le` pushed through
`le_mcaDeltaStar_of_good` (the field-lower hypothesis clears the `2(n−t)/|F| ≤ ε*`
budget); the upper side is `rs_mcaDeltaStar_le_capacity` (the near-capacity refutation).
Instantiated at the
unique-decoding radius `δ ≲ (1−ρ)/3`, this traps the concrete MCA threshold in
`[(1−ρ)/3, 1−(k+1)/n]`. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

The MCA→Johnson refinement of the lower side is the BCIKS20 bivariate line-decoding argument;
MCA→capacity is the open prize.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. #232.
-/

namespace ProximityGap.MCAThresholdLedger

open scoped NNReal ENNReal
open ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- **Concrete two-sided bracket on the MCA threshold.** In the unique-decoding regime and the field
window `2(n−t)·2^128 ≤ |F| < (n−k)·2^128`, the faithful MCA threshold satisfies
`δ ≤ mcaDeltaStar(RS, 2^{-128}) ≤ 1 − (k+1)/n`. -/
theorem rs_mcaDeltaStar_bracket {n : ℕ} [NeZero n] (domain : Fin n ↪ F)
    (k : ℕ) [NeZero k] (hk1 : 1 ≤ k) (hkn : k ≤ n) (δ : ℝ≥0) (hδ1 : δ ≤ 1)
    (htn : ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ < Fintype.card (Fin n))
    (hreg : 3 * (Fintype.card (Fin n) - ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
      < Fintype.card (Fin n) - k + 1)
    (hFlo : 2 * (Fintype.card (Fin n) - ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊) * 2 ^ 128
      ≤ Fintype.card F)
    (hFhi : (Fintype.card F : ℝ) < ((n - k : ℕ) : ℝ) * 2 ^ 128) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
          (ReedSolomon.code domain k : Set (Fin n → F)) (ENNReal.ofReal (1 / 2 ^ 128))
      ∧ mcaDeltaStar (F := F) (A := F)
          (ReedSolomon.code domain k : Set (Fin n → F)) (ENNReal.ofReal (1 / 2 ^ 128))
        ≤ 1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0) := by
  classical
  refine ⟨?_, rs_mcaDeltaStar_le_capacity domain k hk1 hkn hFhi⟩
  -- lower side: ε_mca(RS, δ) ≤ ε* clears the budget, so δ ≤ mcaDeltaStar
  have hcardpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  set t : ℕ := ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ with htdef
  have hgood : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain k : Set (Fin n → F)) δ ≤ ENNReal.ofReal (1 / 2 ^ 128) := by
    refine le_trans (ProximityGap.UDRwire.epsMCA_rs_udr_le domain k
      (by rw [Fintype.card_fin]; exact hkn) δ htn hreg) ?_
    rw [show ((2 * (Fintype.card (Fin n) - t) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        = ENNReal.ofReal (((2 * (Fintype.card (Fin n) - t) : ℕ) : ℝ) / (Fintype.card F : ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos hcardpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hcardpos,
      show (1 : ℝ) / 2 ^ 128 * (Fintype.card F : ℝ) = (Fintype.card F : ℝ) / 2 ^ 128 from by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)]
    exact_mod_cast hFlo
  exact le_mcaDeltaStar_of_good (F := F) (A := F) _ _ hδ1 hgood

#print axioms rs_mcaDeltaStar_bracket

end ProximityGap.MCAThresholdLedger
