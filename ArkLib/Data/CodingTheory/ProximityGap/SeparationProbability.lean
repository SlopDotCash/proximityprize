/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SeparationSurvivalCount

/-!
# The separation probability (issue #389, GG25 §4.3)

The probability form of `SeparatingCoordsCount.card_separates_ge`: for a `τ`-subspace-design `C`
with `0 ≤ θ ≤ 1` bounding `τ`, and `H ≤ C` with `finrank H ≤ r`, a uniformly random coordinate
tuple separates `H` with probability at least `(1−θ)^r`:

  `prob_separates_ge` : `(1−θ)^r ≤ (Pr_{v ←$ᵖ (Fin r → ι)}[Separates H v]).toReal`.

This is the GG25 §4.3 `η^r` separation factor in its native probabilistic form (the counting bound
divided by `n^r` via the uniform law). Paired with `IidCoordinateHit.prob_iid_all_mem_ge` (the
agreement-hitting factor `θ^r`), these are the two probabilistic ingredients subspace-design
list-decoding composes to obtain curve-decodability. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset CodingTheory
open scoped ProbabilityTheory NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Field F]

open Classical in
theorem prob_separates_ge {s : ℕ} {τ : ℕ → ℝ} {θ : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (hθ : ∀ j, τ j ≤ θ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    (1 - θ) ^ r ≤ (Pr_{ let v ←$ᵖ (Fin r → ι) }[ Separates H v ]).toReal := by
  have hcount := card_separates_ge h hθ hθ0 hθ1 r H hHC hr
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) ^ r := by positivity
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.toReal_div, ENNReal.coe_toReal, NNReal.coe_pow, NNReal.coe_natCast,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [le_div_iff₀ hpos]
  exact hcount

open Classical in
/-- Probability form of `card_surv_ge`: if `T` has density at least `θ'`, a uniformly random
coordinate tuple both separates `H` and lands coordinatewise in `T` with probability at least
`(θ' - θ)^r`. -/
theorem prob_surv_ge {s : ℕ} {τ : ℕ → ℝ} {θ θ' : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (hθ : ∀ j, τ j ≤ θ) (hθ0 : 0 ≤ θ) (hθθ' : θ ≤ θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    (θ' - θ) ^ r
      ≤ (Pr_{ let v ←$ᵖ (Fin r → ι) }[ Separates H v ∧ ∀ j, v j ∈ T ]).toReal := by
  have hcount := card_surv_ge h hθ hθ0 hθθ' hθ'1 T hT r H hHC hr
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) ^ r := by positivity
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.toReal_div, ENNReal.coe_toReal, NNReal.coe_pow, NNReal.coe_natCast,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [le_div_iff₀ hpos]
  exact hcount

end ProximityGap

#print axioms ProximityGap.prob_separates_ge
#print axioms ProximityGap.prob_surv_ge
