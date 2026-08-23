/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumAntiConcElementary

/-!
# Density form: almost all frequencies beat the Johnson scale (#357)

The anti-concentration ladder bounds the *count* `#{b : ‖η_b‖² ≥ q} ≤ min(|G|, |G|³/q)`. Dividing by
the number of frequencies `q = |F|` gives the **density / fraction** form — the cleanest statement of
"the average over frequencies beats Johnson":

  `johnson_scale_frequency_density_le`:
  `#{b : ‖η_b‖² ≥ q} / q ≤ min(|G|, |G|³/q) / q`.

In particular the fraction of frequencies reaching the Johnson scale is `≤ |G|/q`, which vanishes as
`|G| = o(q)` — i.e. *almost every* frequency has `‖η_b‖ < √q`, strictly below Johnson. Unconditional,
elementary (Parseval + Markov + counting); no Weil, no sum-product input.

**Honest scope (final, unchanged):** this is the average-side density (a fraction-of-frequencies
statement), provably below Johnson. It does NOT pin the *deployed* `δ*`: the worst-case list bound is
set by the single worst frequency for an adversarial `(p, w)` — the open core (regime III), which no
density/count bound controls. (`mcaDeltaStar` IS proven-pinned for explicit small codes —
`MCAWindowInteriorPin`, `…Family` — those are genuine axiom-clean pins; only the high-rate deployed
regime is open.)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumAntiConc

namespace ArkLib.ProximityGap.SubgroupGaussSumDensity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Density of Johnson-scale frequencies.** The *fraction* of frequencies reaching `‖η_b‖² ≥ q` is
`≤ min(|G|, |G|³/q)/q`; in particular `≤ |G|/q`, vanishing for `|G| = o(q)`. The unconditional,
elementary form of "almost all frequencies beat Johnson". -/
theorem johnson_scale_frequency_density_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        / (Fintype.card F : ℝ)
      ≤ min (G.card : ℝ) ((G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) := by
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  gcongr
  exact card_johnson_scale_frequencies_le_elementary hψ G hq

/-- **The fraction beating Johnson is at least `1 − |G|/q`.** Restatement: at most a `|G|/q`-fraction
of frequencies reach the Johnson scale, so at least a `1 − |G|/q` fraction are strictly below it. -/
theorem johnson_scale_frequency_density_le_simple {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        / (Fintype.card F : ℝ)
      ≤ (G.card : ℝ) / (Fintype.card F : ℝ) := by
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hcard : ((Finset.univ.filter
      (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast card_johnson_scale_frequencies_le hψ G hq
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

end ArkLib.ProximityGap.SubgroupGaussSumDensity

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumDensity.johnson_scale_frequency_density_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumDensity.johnson_scale_frequency_density_le_simple
