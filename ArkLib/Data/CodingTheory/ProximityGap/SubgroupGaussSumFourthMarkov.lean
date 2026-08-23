/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMarkov

/-!
# Fourth-moment (additive-energy) anti-concentration of the subgroup Gauss sum (#357)

`SubgroupGaussSumMarkov` proved, from the second moment, that at most `|G|` frequencies reach the
Johnson scale `‖η_b‖² ≥ q`. This file gives the **sharper** fourth-moment bound, which makes the
dependence on the multiplicative subgroup's **additive energy** `E(G)` explicit — the exact
sum-product → anti-concentration bridge of dossier §24–25.

From `subgroup_gaussSum_fourthMoment` (`∑_b ‖η_b‖⁴ = q·E(G)`, proven, NO Weil), Markov at the squared
Johnson scale gives

  `#{b : ‖η_b‖² ≥ q} · q ≤ E(G)`,    i.e.    `#{b : ‖η_b‖² ≥ q} ≤ E(G)/q`.

This **beats** the second-moment count `|G|` exactly when `E(G) < q·|G|` — and a sum-product estimate
`E(G) ≪ |G|^{5/2}` (Heath-Brown–Konyagin / Shkredov) makes it `≪ |G|^{3/2}/√q · |G|`-sharp in the
relevant regime (`|G| < q^{2/3}`). So the additive energy of the `2^k` subgroup *quantitatively*
controls how few frequencies reach Johnson — the proven, machine-checked content of the §24–25
analysis.

**Honest scope (unchanged):** this is the AVERAGE-side anti-concentration (a *count* of Johnson-scale
frequencies). It does NOT pin `δ*`: the worst-case list bound is set by the single worst frequency for
an *adversarial* `(p, w)`, which no moment/count bound controls (the open core, regime III; see
dossier §25 — driving moments to worst-case strength re-enters the Weil no-go §23). It is the honest
quantitative anchor of the sum-product side, not a closure.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Fourth-moment (additive-energy) Johnson-scale count bound.** From `∑_b ‖η_b‖⁴ = q·E(G)`, the
number of frequencies reaching the Johnson scale `‖η_b‖² ≥ q` satisfies `#{·}·q ≤ E(G)`. Sharper than
the second-moment bound `|G|` whenever `E(G) < q·|G|`; the additive energy `E(G)` of the multiplicative
subgroup is the sum-product quantity that controls the anti-concentration. No Weil input. -/
theorem card_johnson_scale_frequencies_mul_le_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ)
      ≤ (addEnergy G : ℝ) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hqpos : (0 : ℝ) < q := by rw [hqdef]; exact_mod_cast hq
  set S := Finset.univ.filter (fun b : F => q ≤ ‖eta ψ G b‖ ^ 2) with hS
  -- `|S|·q² ≤ ∑_{b∈S} ‖η_b‖⁴ ≤ ∑_b ‖η_b‖⁴ = q·E(G)`
  have hstep : (S.card : ℝ) * q ^ 2 ≤ q * (addEnergy G : ℝ) := by
    calc (S.card : ℝ) * q ^ 2
        = ∑ _b ∈ S, q ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 := by
            refine Finset.sum_le_sum (fun b hb => ?_)
            have hb2 : q ≤ ‖eta ψ G b‖ ^ 2 := (Finset.mem_filter.mp hb).2
            have hsq : ‖eta ψ G b‖ ^ 4 = (‖eta ψ G b‖ ^ 2) ^ 2 := by ring
            rw [hsq]
            nlinarith [sq_nonneg (‖eta ψ G b‖ ^ 2 - q), hb2, hqpos.le]
      _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ 4 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              (fun b _ _ => by positivity)
      _ = q * (addEnergy G : ℝ) := by rw [subgroup_gaussSum_fourthMoment hψ G]
  -- cancel one factor of `q`: `|S|·q² ≤ q·E` ⟹ `|S|·q ≤ E`
  have hfac : (S.card : ℝ) * q ^ 2 = ((S.card : ℝ) * q) * q := by ring
  rw [hfac, mul_comm q (addEnergy G : ℝ)] at hstep
  exact le_of_mul_le_mul_right hstep hqpos

/-- **Energy-sharpened Johnson-scale frequency count.** `#{b : ‖η_b‖² ≥ q} ≤ E(G)/q`. Combined with
`addEnergy_ge_sq` (`E(G) ≥ |G|²`) this is consistent with — and refines — the second-moment bound
`|G|` in the small-energy (sum-product) regime. Pure Parseval + Markov; no Weil. -/
theorem card_johnson_scale_frequencies_le_energy_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
      ≤ (addEnergy G : ℝ) / (Fintype.card F : ℝ) := by
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  rw [le_div_iff₀ hqpos]
  exact card_johnson_scale_frequencies_mul_le_energy hψ G hq

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.card_johnson_scale_frequencies_mul_le_energy
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.card_johnson_scale_frequencies_le_energy_div
