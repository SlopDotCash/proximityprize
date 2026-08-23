/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Probability.Instances

/-!
# I.i.d. coordinates hit a set with product probability (issue #389, GG25 §4.3 toward B2)

The independence kernel of the GG25 §4.3 / `[KRSW23, Tam24]` `η^r` bound: drawing `r` coordinates
independently and uniformly from `ι`, the probability that **all** of them land in a fixed set `T`
is exactly `(|T|/n)^r`.

`prob_iid_all_mem`. The proof reads the event off the uniform law on the function type
`Fin r → ι` (`prob_uniform_eq_card_filter_div_card`): the favorable outcomes are exactly
`Fintype.piFinset (fun _ => T)`, of cardinality `|T|^r`, against `|ι|^r` total, and
`|T|^r / |ι|^r = (|T|/|ι|)^r`.

Combined with the design's coordinate budget (`SubspaceDesignFullVanish`, `SeparatingCoordsAvoiding`),
this is the "random coordinates land in the agreement set" half of the probabilistic separation that
turns subspace-design list-decoding into curve-decodability. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

open Finset
open scoped ProbabilityTheory NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Classical in
theorem prob_iid_all_mem (r : ℕ) (T : Finset ι) :
    Pr_{ let v ←$ᵖ (Fin r → ι) }[ ∀ j, v j ∈ T ]
      = (((T.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ^ r : ℝ≥0) := by
  rw [prob_uniform_eq_card_filter_div_card]
  have hfilter : (univ.filter (fun v : Fin r → ι => ∀ j, v j ∈ T))
      = Fintype.piFinset (fun _ : Fin r => T) := by
    ext v; simp [Fintype.mem_piFinset]
  rw [hfilter, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun,
    Nat.cast_pow]
  rw [div_pow, ← ENNReal.coe_div (pow_ne_zero r (by exact_mod_cast Fintype.card_ne_zero))]

/-- **Usable lower bound.** If `T` has density at least `θ` (`θ·n ≤ |T|`), then `r` i.i.d. uniform
coordinates all land in `T` with probability at least `θ^r`. With `T` the agreement set of a
codeword `δ`-close to `y`, this is the `η^r`-style survival factor. -/
theorem prob_iid_all_mem_ge (r : ℕ) (T : Finset ι) {θ : ℝ≥0}
    (hθ : θ * Fintype.card ι ≤ T.card) :
    (θ : ENNReal) ^ r ≤ Pr_{ let v ←$ᵖ (Fin r → ι) }[ ∀ j, v j ∈ T ] := by
  rw [prob_iid_all_mem, ← ENNReal.coe_pow]
  apply ENNReal.coe_le_coe.mpr
  gcongr
  rw [le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
  exact hθ

end ProximityGap

#print axioms ProximityGap.prob_iid_all_mem
#print axioms ProximityGap.prob_iid_all_mem_ge
