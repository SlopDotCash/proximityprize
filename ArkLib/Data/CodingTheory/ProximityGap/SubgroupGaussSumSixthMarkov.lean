/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMoment

/-!
# Sixth-moment (3-fold-energy) anti-concentration of the subgroup Gauss sum (#357/#389)

`SubgroupGaussSumFourthMarkov` proved, from the fourth moment, that `#{b : ‖η_b‖² ≥ q} ≤ E(G)/q`.
This file gives the next rung from `subgroup_gaussSum_sixthMoment` (`∑_b ‖η_b‖⁶ = q·E₃(G)`, proven,
NO Weil): Markov at the *cubed* Johnson scale gives

  `#{b : ‖η_b‖² ≥ q} · q² ≤ E₃(G)`,    i.e.    `#{b : ‖η_b‖² ≥ q} ≤ E₃(G)/q²`.

With the trivial `addEnergy3_le_pow` (`E₃(G) ≤ |G|⁵`) this is `≤ |G|⁵/q²`, **strictly sharper** than
the fourth-moment `E(G)/q ≤ |G|³/q` exactly when `|G|² < q`. Consequence
(`no_johnson_scale_frequency_of_pow_lt`): when `|G|⁵ < q²` (i.e. `|G| < q^{2/5}`) **no** frequency
reaches the Johnson scale — pushing the fourth-moment threshold `|G| < q^{1/3}` (from `E(G) ≤ |G|³`)
up to `|G| < q^{2/5}`. The full moment ladder `∑_b ‖η_b‖^{2r} = q·E_r(G)` drives this to `|G| < q^{1/2}`.

**Honest scope (unchanged):** this is the AVERAGE-side anti-concentration (a *count* of Johnson-scale
frequencies), provably below Johnson. It does NOT pin `δ*`: the worst-case list bound is set by the
single worst frequency for an *adversarial* `(p, w)`, which no moment/count bound controls — the open
core (regime III; pushing moments to worst-case strength re-enters the Weil no-go). It sharpens the
regime in which the moment method already gives sub-Johnson behaviour, not a closure.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sixth-moment (3-fold-energy) Johnson-scale count bound.** From `∑_b ‖η_b‖⁶ = q·E₃(G)`, the
number of frequencies reaching the Johnson scale `‖η_b‖² ≥ q` satisfies `#{·}·q² ≤ E₃(G)`. Sharper
than the fourth-moment bound `E(G)/q` whenever `|G|² < q`. No Weil input. -/
theorem card_johnson_scale_frequencies_mul_sq_le_energy3 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ 2
      ≤ (addEnergy3 G : ℝ) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hqpos : (0 : ℝ) < q := by rw [hqdef]; exact_mod_cast hq
  set S := Finset.univ.filter (fun b : F => q ≤ ‖eta ψ G b‖ ^ 2) with hS
  -- `|S|·q³ ≤ ∑_{b∈S} ‖η_b‖⁶ ≤ ∑_b ‖η_b‖⁶ = q·E₃(G)`
  have hstep : (S.card : ℝ) * q ^ 3 ≤ q * (addEnergy3 G : ℝ) := by
    calc (S.card : ℝ) * q ^ 3
        = ∑ _b ∈ S, q ^ 3 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 6 := by
            refine Finset.sum_le_sum (fun b hb => ?_)
            have hb2 : q ≤ ‖eta ψ G b‖ ^ 2 := (Finset.mem_filter.mp hb).2
            have h6 : ‖eta ψ G b‖ ^ 6 = (‖eta ψ G b‖ ^ 2) ^ 3 := by ring
            rw [h6]
            gcongr
      _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ 6 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              (fun b _ _ => by positivity)
      _ = q * (addEnergy3 G : ℝ) := by rw [subgroup_gaussSum_sixthMoment hψ G]
  -- cancel one factor of `q`: `|S|·q³ ≤ q·E₃` ⟹ `|S|·q² ≤ E₃`
  have hfac : (S.card : ℝ) * q ^ 3 = ((S.card : ℝ) * q ^ 2) * q := by ring
  rw [hfac, mul_comm q (addEnergy3 G : ℝ)] at hstep
  exact le_of_mul_le_mul_right hstep hqpos

/-- **3-fold-energy-sharpened Johnson-scale frequency count.** `#{b : ‖η_b‖² ≥ q} ≤ E₃(G)/q²`. With
`addEnergy3_le_pow` (`E₃(G) ≤ |G|⁵`) this refines the fourth-moment bound `E(G)/q` whenever `|G|² < q`.
Pure Parseval + Markov; no Weil. -/
theorem card_johnson_scale_frequencies_le_energy3_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
      ≤ (addEnergy3 G : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ 2 := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
    positivity
  rw [le_div_iff₀ hqpos]
  exact card_johnson_scale_frequencies_mul_sq_le_energy3 hψ G hq

/-- **The `q^{2/5}` no-Johnson threshold.** If `|G|⁵ < q²` (i.e. `|G| < q^{2/5}`) then *no* frequency
reaches the Johnson scale `‖η_b‖² ≥ q`. This strictly widens the fourth-moment threshold `|G| < q^{1/3}`
(`|G|³ < q`): the sixth moment reaches `q^{2/5}`, and the full moment ladder reaches `q^{1/2}`. -/
theorem no_johnson_scale_frequency_of_pow_lt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F)
    (hlt : (G.card : ℝ) ^ 5 < (Fintype.card F : ℝ) ^ 2) :
    (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)) = ∅ := by
  classical
  by_contra hne
  have hnemp : (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hcard1 : (1 : ℝ) ≤
      ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) := by
    have : 1 ≤ (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card :=
      Finset.Nonempty.card_pos hnemp
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ 2 := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
    positivity
  -- `q² ≤ |S|·q² ≤ E₃ ≤ |G|⁵ < q²`, contradiction
  have hb := card_johnson_scale_frequencies_mul_sq_le_energy3 hψ G hq
  have he3 : (addEnergy3 G : ℝ) ≤ (G.card : ℝ) ^ 5 := by exact_mod_cast addEnergy3_le_pow G
  have hq2le : (Fintype.card F : ℝ) ^ 2 ≤
      ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ 2 := by
    nlinarith [hcard1, hqpos]
  linarith [hq2le, hb, he3, hlt]

end ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.card_johnson_scale_frequencies_le_energy3_div
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.no_johnson_scale_frequency_of_pow_lt
