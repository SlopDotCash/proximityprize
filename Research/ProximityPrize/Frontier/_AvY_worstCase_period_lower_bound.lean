/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyNegClosedLower
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

For `G = μ_n` with `n = 2^μ ≥ 2` (negation-closed, Sidon-except-negation in char 0) the char-0
additive energy is `E = 3n² − 3n` (e.g. `G = {1, −1}`: ordered sum multiplicities `1, 2, 1`,
energy `6`). Audit correction R-100: an earlier version of this file used `3n² − 2n`, which is
wrong (`8 ≠ 6` already at `n = 2`).

In a finite field the energy can only be larger: `additiveEnergy_ge_of_negClosed` proves
`3n² − 3n ≤ E(G)` for every negation-closed `G` with `0 ∉ G`, `2 ≠ 0`, and the excess
`E(G) − (3n² − 3n) ≥ 0` (char-`p` extra collisions) is a separate, generally nonzero term. Since
the ratio is monotone in `E`, the lower bound suffices, and this file proves the **unconditional**
finite-field floor (`worstCase_period_lower_bound_negClosed`)

  `Λ² ≥ (q·(3n² − 3n) − n⁴) / (q·n − n²)`   (exact, finite `q`, DC-corrected),

whose right side tends to `3n − 3` as `q → ∞` with `n` fixed. So for `n ≥ 2` and large `q` the
worst period exceeds the Parseval `√n` average by roughly a `√3` factor (precisely
`Λ² ≥ 3n − 3 − o_q(1)`, not `3n` or `3n − 2`). `worstCase_period_lower_bound_muN` keeps the
substituted ratio under an *explicit* equality hypothesis `E = 3n² − 3n` (the no-excess /
Sidon-mod-negation case, see `addEnergy_eq_of_sidonModNeg`); it is not by itself a discharged
concrete specialization. This is a LOWER-bound result only; it does not bound the open
BGK/Paley wall above.

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

/-- **Ratio bound from an energy lower bound.** Since the ratio is increasing in the energy,
any lower bound `3·|G|² − 3·|G| ≤ addEnergy G` (the char-0 baseline; finite-field excess only
increases the energy) gives `(q·(3n² − 3n) − n⁴) / (q·n − n²) ≤ ‖η_b‖²` for some `b ≠ 0`. -/
theorem worstCase_period_lower_bound_of_energy_ge
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hE : 3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ) ≤ (addEnergy G : ℝ))
    (hden : (0 : ℝ) < (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) - (G.card : ℝ) ^ 4)
        / ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
      ≤ ‖eta ψ G b‖ ^ 2 := by
  obtain ⟨b, hb, h⟩ := worstCase_period_lower_bound_from_fourth_moment hψ G hden
  refine ⟨b, hb, le_trans ?_ h⟩
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  gcongr

/-- **Specialization under the no-excess energy equality `E = 3n² − 3n`.**

Substituting the explicit hypothesis `addEnergy G = 3·|G|² − 3·|G|` (the char-0 value for
`μ_n`, `n = 2^μ ≥ 2`; in a finite field it holds exactly in the Sidon-mod-negation / no-excess
case, cf. `AdditiveEnergyBridge.addEnergy_eq_of_sidonModNeg`) into the ratio bound:
`(q·(3n² − 3n) − n⁴) / (q·n − n²) ≤ ‖η_b‖²` for some `b ≠ 0`, where `n = |G|`.
As `q → ∞` (fixed `n`) the ratio tends to `3n − 3`.

Audit correction R-100: this previously assumed the wrong value `3n² − 2n`. The equality is an
assumption here; the unconditional finite-field statement is
`worstCase_period_lower_bound_negClosed`. -/
theorem worstCase_period_lower_bound_muN
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hE : (addEnergy G : ℝ) = 3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ))
    (hden : (0 : ℝ) < (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) - (G.card : ℝ) ^ 4)
        / ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
      ≤ ‖eta ψ G b‖ ^ 2 := by
  have h := worstCase_period_lower_bound_from_fourth_moment hψ G hden
  rwa [hE] at h

/-- **Unconditional finite-field floor for negation-closed sets (e.g. `μ_n`, `n` even, odd
characteristic).** For `0 ∉ G`, `2 ≠ 0`, `G = −G` and `|G|² < q·|G|`, there is `b ≠ 0` with
`(q·(3n² − 3n) − n⁴) / (q·n − n²) ≤ ‖η_b‖²`, `n = |G|`. This uses the proved lower bound
`3n² − 3n ≤ E(G)` (`additiveEnergy_ge_of_negClosed`), so it holds with any char-`p` energy
excess; no energy equality is assumed. -/
theorem worstCase_period_lower_bound_negClosed
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hden : (0 : ℝ) < (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) - (G.card : ℝ) ^ 4)
        / ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
      ≤ ‖eta ψ G b‖ ^ 2 := by
  refine worstCase_period_lower_bound_of_energy_ge hψ G ?_ hden
  have hnat : 3 * G.card ^ 2 - 3 * G.card ≤ addEnergy G := by
    rw [← ArkLib.ProximityGap.AdditiveEnergyBridge.additiveEnergy_eq_addEnergy]
    exact ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_ge_of_negClosed h2 h0 hneg
  have hle : 3 * G.card ≤ 3 * G.card ^ 2 := by
    have : G.card ≤ G.card ^ 2 := by
      rcases Nat.eq_zero_or_pos G.card with h | h
      · simp [h]
      · exact Nat.le_self_pow (by norm_num) _
    omega
  have hcast : ((3 * G.card ^ 2 - 3 * G.card : ℕ) : ℝ)
      = 3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [← hcast]
  exact_mod_cast hnat

end ArkLib.ProximityGap.Frontier

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.worstCase_period_lower_bound_from_fourth_moment
#print axioms ArkLib.ProximityGap.Frontier.worstCase_period_lower_bound_of_energy_ge
#print axioms ArkLib.ProximityGap.Frontier.worstCase_period_lower_bound_muN
#print axioms ArkLib.ProximityGap.Frontier.worstCase_period_lower_bound_negClosed
