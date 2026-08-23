/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumAntiConc
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergyCubeBound

/-!
# The fully-elementary (unconditional) average-side anti-concentration bound (#357)

`SubgroupGaussSumAntiConc` proved `#{b : ‖η_b‖² ≥ q} ≤ min(|G|, E(G)/q)`; `AddEnergyCubeBound` proved
`E(G) ≤ |G|³`. Composing them removes the additive energy from the statement, giving a bound that is
**unconditional and purely elementary** (Parseval + Markov + counting, no Weil, no sum-product input):

  `card_johnson_scale_frequencies_le_elementary`:
  `#{b : ‖η_b‖² ≥ q} ≤ min(|G|, |G|³/q)`.

This is the honest, self-contained endpoint of the average-side ladder: with no open hypotheses, at
most `min(|G|, |G|³/q)` of the `q` frequencies reach the Johnson scale. (The `|G|` term wins when
`|G| ≤ √q`; the `|G|³/q` term when `|G| > √q`. The genuine sum-product `E(G) ≪ |G|^{5/2}` would replace
`|G|³/q` by the sharper `|G|^{3/2}/√q · …` — the hard open input, dossier §24.)

**Honest scope (final):** average-side count, provably below Johnson; does NOT pin `δ*` (worst-case
adversarial frequency = the open core, §25). It is the unconditional, fully-formalized terminus of the
*provable* side of the wall analysis.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.SubgroupGaussSumAntiConc

namespace ArkLib.ProximityGap.SubgroupGaussSumAntiConc

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Unconditional elementary anti-concentration.** `#{b : ‖η_b‖² ≥ q} ≤ min(|G|, |G|³/q)` — the
average-side Johnson-scale frequency count, with the additive energy eliminated via `E(G) ≤ |G|³`.
No Weil, no sum-product hypothesis; the honest, self-contained endpoint of the provable side. -/
theorem card_johnson_scale_frequencies_le_elementary {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
      ≤ min (G.card : ℝ) ((G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)) := by
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  refine (card_johnson_scale_frequencies_le_min hψ G hq).trans ?_
  refine min_le_min (le_refl _) ?_
  -- `E(G)/q ≤ |G|³/q` from `E(G) ≤ |G|³`
  gcongr
  exact_mod_cast addEnergy_le_cube G

end ArkLib.ProximityGap.SubgroupGaussSumAntiConc

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumAntiConc.card_johnson_scale_frequencies_le_elementary
