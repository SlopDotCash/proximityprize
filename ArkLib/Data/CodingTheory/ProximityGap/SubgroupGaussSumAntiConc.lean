/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMarkov

/-!
# The combined average-side anti-concentration bound for the subgroup Gauss sum (#357)

Capstone of the two Markov bricks (dossier §24–25), tying together the second- and fourth-moment
frequency counts into the sharpest bound the proven moments give, with NO Weil input:

* second moment ⟹ `#{b : ‖η_b‖² ≥ q} ≤ |G|`            (`card_johnson_scale_frequencies_le`)
* fourth moment ⟹ `#{b : ‖η_b‖² ≥ q} ≤ E(G)/q`         (`card_johnson_scale_frequencies_le_energy_div`)

so

  **`#{b : ‖η_b‖² ≥ q} ≤ min(|G|, E(G)/q)`.**

The fourth-moment term wins (is sharper) precisely when `E(G) < q·|G|`, i.e. when the multiplicative
subgroup's additive energy is sub-`q·|G|` — the sum-product regime (`E(G) ≪ |G|^{5/2}`,
Heath-Brown–Konyagin/Shkredov), where `E(G)/q ≪ |G|`. This is the optimal *average-side*
anti-concentration the moment method yields: even at the Johnson scale, the fraction of frequencies
reaching it is `≤ min(|G|, E(G)/q)/q`, vanishing for the deployed parameters.

**Honest scope (final, unchanged):** this bounds the *count* of Johnson-scale frequencies (the average
side), which provably beats Johnson; it does NOT pin `δ*`. The worst-case list bound is set by the
single worst frequency for an *adversarial* `(p, w)`, which no moment/count bound controls — the open
core (regime III). By §25, pushing the moment ladder to worst-case strength re-enters the Weil no-go
(§23). This is the machine-checked terminus of the *provable* average side; the worst-case apex is the
25-year open problem and is not fabricated.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumAntiConc

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Combined (optimal) average-side anti-concentration.** The number of frequencies reaching the
Johnson scale `‖η_b‖² ≥ q` is bounded by `min(|G|, E(G)/q)` — the better of the second-moment count
`|G|` and the fourth-moment additive-energy count `E(G)/q`. Pure Parseval + Markov; no Weil. The
fourth-moment term is sharper exactly in the sum-product regime `E(G) < q·|G|`. -/
theorem card_johnson_scale_frequencies_le_min {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
      ≤ min (G.card : ℝ) ((addEnergy G : ℝ) / (Fintype.card F : ℝ)) := by
  refine le_min ?_ ?_
  · exact_mod_cast card_johnson_scale_frequencies_le hψ G hq
  · exact card_johnson_scale_frequencies_le_energy_div hψ G hq

end ArkLib.ProximityGap.SubgroupGaussSumAntiConc

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumAntiConc.card_johnson_scale_frequencies_le_min
