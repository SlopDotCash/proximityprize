/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodLowerBound
import Mathlib.Tactic

/-!
# Fourth-moment ratio lower bound on the worst-case subgroup period (#444)

This brick puts the in-tree cross-multiplied lower bound
`exists_period_sq_ge` into the explicit **ratio / Cauchy–Schwarz** form

> `worstCase_period_lower_bound_from_fourth_moment` :
> `∃ b ≠ 0, (q·E(G) − |G|⁴) / (q·|G| − |G|²) ≤ ‖η_b‖²`,

i.e. `Λ²(ψ,G) = max_{b≠0} ‖η_b‖²  ≥  (q·E(G) − |G|⁴) / (q·|G| − |G|²)`, the power-mean
fact `max aᵢ ≥ (∑aᵢ²)/(∑aᵢ)` applied to `aᵢ = ‖η_i‖²` over the nonzero frequencies, with
`∑ aᵢ = q·|G| − |G|²` (DC-subtracted second moment) and `∑ aᵢ² = q·E(G) − |G|⁴`
(DC-subtracted fourth moment), both proven in-tree.

For `G = μ_n` the `2^μ`-th roots of unity (Sidon-except-negation, additive energy
`E = 3n² − 2n` in char 0), substituting `E = 3n² − 2n` gives

  `Λ² ≥ (q·(3n² − 2n) − n⁴) / (q·n − n²)  ⟶  3n − 2`  as `q → ∞`,

an **unconditional `Λ ≳ √(3n)` floor**, strictly above the Parseval `√n` floor
(`PrizeStructuralConstant`): the spectrum is NOT flat — the worst period exceeds the
L²-average by a `√3` factor. (`worstCase_period_lower_bound_muN` packages the substituted
ratio.) This is a LOWER-bound result only; it does not bound the open BGK/Paley wall above.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.Frontier

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Fourth-moment ratio lower bound on the worst nonzero period.**

There is a nontrivial frequency `b ≠ 0` whose squared period dominates the ratio of the
DC-subtracted fourth and second moments:
`(q·E(G) − |G|⁴) / (q·|G| − |G|²) ≤ ‖η_b‖²`, whenever the denominator is positive
(`|G|² < q·|G|`, e.g. `|G| < q`). This is the division form of the in-tree cross-multiplied
`exists_period_sq_ge`, i.e. `Λ²(ψ,G) ≥ (q·E − |G|⁴)/(q·|G| − |G|²)`. -/
theorem worstCase_period_lower_bound_from_fourth_moment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hden : (0 : ℝ) < (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4)
        / ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
      ≤ ‖eta ψ G b‖ ^ 2 := by
  obtain ⟨b, hb, hcross⟩ :=
    ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.exists_period_sq_ge hψ G
  refine ⟨b, hb, ?_⟩
  rw [div_le_iff₀ hden]
  exact hcross

/-- **Specialization to `μ_n` (Sidon-except-negation, char-0 energy `E = 3n² − 2n`).**

Substituting `addEnergy G = 3·|G|² − 2·|G|` into the ratio bound:
`(q·(3n² − 2n) − n⁴) / (q·n − n²) ≤ ‖η_b‖²` for some `b ≠ 0`, where `n = |G|`.
As `q → ∞` the right ratio `(q·(3n²−2n) − n⁴)/(q·n − n²) → 3n − 2`, the unconditional
`Λ ≳ √(3n)` floor strictly above the Parseval `√n` floor. -/
theorem worstCase_period_lower_bound_muN
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hE : (addEnergy G : ℝ) = 3 * (G.card : ℝ) ^ 2 - 2 * (G.card : ℝ))
    (hden : (0 : ℝ) < (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 2 * (G.card : ℝ)) - (G.card : ℝ) ^ 4)
        / ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
      ≤ ‖eta ψ G b‖ ^ 2 := by
  have h := worstCase_period_lower_bound_from_fourth_moment hψ G hden
  rwa [hE] at h

end ArkLib.ProximityGap.Frontier

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.worstCase_period_lower_bound_from_fourth_moment
#print axioms ArkLib.ProximityGap.Frontier.worstCase_period_lower_bound_muN
