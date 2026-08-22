/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCASmoothJumpUnconditional
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation

/-!
# The full-band threshold capstone (#357): `δ*(RS[F, μ_n, n−2], ε*) = 1/n` on `[1/q, n/q)`

The campaign's round-2 chain — family theorem (2-scalar band), antichain engine (cap `n`),
exact jump value (`n/q`, unconditional on smooth domains) — welds into the complete
threshold function on the natural band:

  **`mcaDeltaStar(RS[F, μ_n, n−2], ε*) = 1/n` for every `ε* ∈ [1/q, n/q)`**

(`mcaDeltaStar_rs_smooth_full_band`): below `1/n` the sub-unit collapse prices every
radius at `1/q ≤ ε*`; at `1/n` the error is exactly `n/q > ε*`; the jump-pin engine closes
the sandwich. This is the first complete determination of the `δ*(ε*)` function for any
Reed–Solomon family — at the unique-decoding radius of the high-rate family, over every
smooth 2-power evaluation domain in odd characteristic.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

open Polynomial
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.MCADeltaStarExactPoint ProximityGap.MCAListBracketInterpolation
open ProximityGap.MCASmoothJumpUnconditional

namespace ProximityGap.MCADeltaStarFullBand

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The full-band threshold.** For every smooth even-order subgroup domain (with an
antipodal marked pair, odd characteristic, `(n : F) ≠ 0`) and every error target
`ε* ∈ [1/q, n/q)`:  `mcaDeltaStar(RS[F, μ_n, n−2], ε*) = 1/n`. -/
theorem mcaDeltaStar_rs_smooth_full_band (domain : ι ↪ F)
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Fintype.card ι))
    (hn : 4 ≤ Fintype.card ι)
    (hnF : ((Fintype.card ι : ℕ) : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) (hanti : domain b₂ = -domain b₁)
    {εstar : ℝ≥0∞}
    (hlo : 1 / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) εstar
      = 1 / (Fintype.card ι : ℝ≥0) := by
  have hnpos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  apply mcaDeltaStar_eq_of_jump
  · rw [div_le_one hnpos]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  · -- good below the jump: the sub-unit collapse
    intro δ hδ
    have hδn : δ * (Fintype.card ι : ℝ≥0) < 1 := by
      have h := mul_lt_mul_of_pos_right hδ hnpos
      rwa [one_div, inv_mul_cancel₀ (ne_of_gt hnpos)] at h
    exact le_trans
      (epsMCA_le_inv_card_of_small_radius
        (ReedSolomon.code domain (Fintype.card ι - 2)) hδn) hlo
  · -- bad at the jump: the exact value n/q exceeds ε*
    rw [epsMCA_rs_smooth_jump_eq domain himg hζ hn hnF h2 hb hanti]
    exact hhi

/-! ## Source audit -/

#print axioms mcaDeltaStar_rs_smooth_full_band

end ProximityGap.MCADeltaStarFullBand
