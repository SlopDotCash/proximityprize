/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTailRootSharp

/-!
# Comparing the sharp and coarse char-p moment-tail roots

`CharPDeepMomentTailRootSharp` records the exact root of the sharper unconditional energy tail,
with exponent `(2r-1)/(2r)` on `|G|`.  This file packages the honest comparison with the older
coarse rooted form: once `G` is nonempty, the sharp root is at most the coarse `|G|` root, and the
entire improvement is only the harmless factor `|G|^{-1/(2r)}`.  This is no-go bookkeeping for the
moment route, not a square-root-cancellation or CORE claim.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.CharPDeepMomentTailComparison

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exact rooted tail's `|G|` factor is bounded by the coarse `|G|` factor for nonempty `G`.
This makes explicit that the sharp unconditional saving is only the exponent gap `1/(2r)`, not a
new route toward square-root cancellation. -/
theorem sharp_card_factor_le_coarse (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (hG : 1 ≤ G.card) :
    (G.card : ℝ) ^ (((2 * r - 1 : ℕ) : ℝ) * ((((2 * r : ℕ) : ℝ))⁻¹)) ≤ (G.card : ℝ) := by
  have hbase : (1 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hG
  have hden : (0 : ℝ) < ((2 * r : ℕ) : ℝ) := by positivity
  have hnum_le : (((2 * r - 1 : ℕ) : ℝ)) ≤ ((2 * r : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_le (2 * r) 1)
  have hexp : (((2 * r - 1 : ℕ) : ℝ) * ((((2 * r : ℕ) : ℝ))⁻¹)) ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hden).2 hnum_le
  simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hexp

/-- Consumer comparison: the sharp rooted Markov tail is always at most the coarse rooted tail for
nonempty `G`.  This is a scoped comparison of two unconditional moment-route bounds only. -/
theorem sharp_root_rhs_le_coarse (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (hG : 1 ≤ G.card) :
    (Fintype.card F : ℝ) ^ ((((2 * r : ℕ) : ℝ))⁻¹) *
        (G.card : ℝ) ^ (((2 * r - 1 : ℕ) : ℝ) * ((((2 * r : ℕ) : ℝ))⁻¹)) ≤
      (Fintype.card F : ℝ) ^ ((((2 * r : ℕ) : ℝ))⁻¹) * (G.card : ℝ) := by
  gcongr
  exact sharp_card_factor_le_coarse G r hr hG

/-- The exact rooted sharp tail immediately implies the older coarse rooted tail for nonempty `G`.
No cancellation is gained here; the conclusion is still the trivial `|G|`-floor moment bound. -/
theorem eta_le_coarse_of_eta_le_sharp {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hr : 1 ≤ r) (hG : 1 ≤ G.card) (b : F) :
    ‖eta ψ G b‖ ≤ (Fintype.card F : ℝ) ^ ((((2 * r : ℕ) : ℝ))⁻¹) * (G.card : ℝ) := by
  exact le_trans
    (ArkLib.ProximityGap.CharPDeepMomentTailRootSharp.eta_le_rpow_sharp hψ G r hr b)
    (sharp_root_rhs_le_coarse G r hr hG)

end ArkLib.ProximityGap.CharPDeepMomentTailComparison

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharPDeepMomentTailComparison.sharp_card_factor_le_coarse
#print axioms ArkLib.ProximityGap.CharPDeepMomentTailComparison.sharp_root_rhs_le_coarse
#print axioms ArkLib.ProximityGap.CharPDeepMomentTailComparison.eta_le_coarse_of_eta_le_sharp
