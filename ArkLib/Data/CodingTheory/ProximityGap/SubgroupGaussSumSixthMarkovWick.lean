/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMarkov
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# Sixth-moment no-Johnson threshold sharpened by the char-0 Wick bound: `q^{2/5} → q^{2/3}` (#444)

`SubgroupGaussSumSixthMarkov` proved, from the sixth moment `∑_b ‖η_b‖⁶ = q·E₃(G)`, the
Johnson-scale frequency count bound `#{b : ‖η_b‖² ≥ q}·q² ≤ E₃(G)`, and then used the **trivial**
ceiling `E₃(G) ≤ |G|⁵` (`addEnergy3_le_pow`) to obtain the no-Johnson threshold `|G|⁵ < q²`, i.e.
`|G| < q^{2/5}`.

For the smooth subgroup `G = μ_n` in the prize regime the additive 3-energy is **`Θ(n³)`**, not
`n⁵`: the char-0 Gaussian (Wick) bound `E₃(G) ≤ (2·3−1)‼·|G|³ = 15·|G|³` (the `GaussPeriodMomentBound`
predicate `GaussianEnergyBound G 3`, proven for `μ_n` in the prize regime via the Lam-Leung antipodal
census, `Frontier.GaussianEnergyBoundMuNDepthThree`). Feeding `15·|G|³` instead of `|G|⁵` widens the
no-Johnson threshold to

> `15·|G|³ < q²`,   i.e.   `|G| < (q²/15)^{1/3} ≈ q^{2/3}`,

a strict improvement over `q^{2/5}` under the SAME char-0 input the campaign already proves for `μ_n`.

The bridge needed to feed the `rEnergy`-stated `GaussianEnergyBound` into the `addEnergy3`-stated
Markov count is the count identity `rEnergy G 3 = addEnergy3 G` (the r = 3 analogue of
`REnergyTwoExact.rEnergy_two_eq_addEnergy`), read off the two sixth-moment Parseval laws.

## Theorems

* **`rEnergy_three_eq_addEnergy3`**: `rEnergy G 3 = addEnergy3 G` for any finite field, by cancelling
  `q ≠ 0` from `∑_b ‖η_b‖⁶ = q·rEnergy G 3` (`subgroup_gaussSum_moment` at `r = 3`) and
  `∑_b ‖η_b‖⁶ = q·addEnergy3 G` (`subgroup_gaussSum_sixthMoment`). A primitive `ψ` is a proof device.
* **`card_johnson_scale_frequencies_mul_sq_le_wick`**: under the Wick hypothesis
  `GaussianEnergyBound G 3` (`rEnergy G 3 ≤ 15·|G|³`), `#{b : ‖η_b‖² ≥ q}·q² ≤ 15·|G|³`.
* **`no_johnson_scale_frequency_of_wick_lt`**: under `GaussianEnergyBound G 3`, if `15·|G|³ < q²`
  then **no** frequency reaches the Johnson scale `‖η_b‖² ≥ q`. For `μ_n` (prize regime) this is the
  `q^{2/3}` threshold, vs the trivial `q^{2/5}`.

## Honest scope

This is the AVERAGE-side anti-concentration (a *count* of Johnson-scale frequencies), sharpened for
the actual prize object `μ_n` under its proven char-0 Wick bound. It does NOT pin `δ*`: the worst-case
single-frequency BGK/Paley √-cancellation wall `M(μ_n) ≤ C·√(n·log(p/n))` (CORE) is **untouched** and
**OPEN**. The Wick input is conditional (it is char-0 / large-`p`; in char `p` at small `p`,
`E₃(μ_n)` exceeds `15n³` by the extra-collision surplus, so the threshold guard `15|G|³ < q²` simply
does not fire there). NON-MOMENT in spirit (it consumes an exact-census Wick value, not a cancellation
bound on `M`). Probe `scripts/probes/probe_sixthmarkov_e3_threshold.py` confirms the bridge
(`addE3 == rE3`, 9/9) and the threshold (`15n³ < q² ⟹ no Johnson-scale frequency`, 9/9 incl. thick
cases where the surplus makes the guard inert).

Issue #444. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`rEnergy G 3 = addEnergy3 G`.** The two sixth-moment census definitions agree: the
nested-`piFinset` relation energy at `r = 3` equals the 3-fold additive energy. Read off the two
Parseval sixth-moment laws (`∑_b ‖η_b‖⁶ = q · rEnergy G 3` from `subgroup_gaussSum_moment` at `r = 3`,
and `∑_b ‖η_b‖⁶ = q · addEnergy3 G` from `subgroup_gaussSum_sixthMoment`), cancelling `q = |F| ≠ 0`.
The r = 3 analogue of `REnergyTwoExact.rEnergy_two_eq_addEnergy`. The primitive character `ψ` is a
proof device (one exists on every `ZMod p`); it is absent from the statement. -/
theorem rEnergy_three_eq_addEnergy3 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    rEnergy G 3 = addEnergy3 G := by
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  -- ∑_b ‖η_b‖^(2*3) = q · rEnergy G 3
  have hP1 := subgroup_gaussSum_moment hψ G 3
  -- ∑_b ‖η_b‖^6 = q · addEnergy3 G
  have hP2 := subgroup_gaussSum_sixthMoment hψ G
  -- the two left-hand sides are equal (2*3 = 6)
  have hpow : (2 * 3 : ℕ) = 6 := by norm_num
  have hsum_eq : (Fintype.card F : ℝ) * (rEnergy G 3 : ℝ)
      = (Fintype.card F : ℝ) * (addEnergy3 G : ℝ) := by
    rw [← hP1, ← hP2, hpow]
  have hRE : (rEnergy G 3 : ℝ) = (addEnergy3 G : ℝ) :=
    mul_left_cancel₀ (ne_of_gt hqR) hsum_eq
  exact_mod_cast hRE

/-- **Wick-sharpened Johnson-scale count bound.** From the sixth-moment Markov bound
`#{b : ‖η_b‖² ≥ q}·q² ≤ E₃(G)` (`card_johnson_scale_frequencies_mul_sq_le_energy3`) and the char-0
Wick hypothesis `GaussianEnergyBound G 3` (`rEnergy G 3 ≤ 15·|G|³`), feeding the bridge
`E₃(G) = rEnergy G 3` gives `#{b : ‖η_b‖² ≥ q}·q² ≤ 15·|G|³`. For `μ_n` (prize regime) the RHS is
`Θ(n³)`, vastly below the trivial `|G|⁵`. -/
theorem card_johnson_scale_frequencies_mul_sq_le_wick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) (hWick : GaussianEnergyBound G 3) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ 2
      ≤ 15 * (G.card : ℝ) ^ 3 := by
  -- the deployed sixth-moment Markov count bound, in terms of E₃
  have hMarkov := card_johnson_scale_frequencies_mul_sq_le_energy3 hψ G hq
  -- the Wick bound: rEnergy G 3 ≤ (2·3−1)‼ · |G|³ = 15·|G|³
  have hWick' : (rEnergy G 3 : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by
    have h := hWick
    unfold GaussianEnergyBound at h
    have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
    rwa [hdf] at h
  -- bridge E₃ = rEnergy G 3, so E₃ ≤ 15·|G|³
  have hbridge : (addEnergy3 G : ℝ) = (rEnergy G 3 : ℝ) := by
    rw [rEnergy_three_eq_addEnergy3 hψ G]
  have hE3le : (addEnergy3 G : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by rw [hbridge]; exact hWick'
  exact le_trans hMarkov hE3le

/-- **The `q^{2/3}` no-Johnson threshold** (sharpening the sixth-moment `q^{2/5}`). Under the char-0
Wick bound `GaussianEnergyBound G 3` (`rEnergy G 3 ≤ 15·|G|³`), if `15·|G|³ < q²` then **no** frequency
reaches the Johnson scale `‖η_b‖² ≥ q`. For `μ_n` in the prize regime this is the threshold
`|G| < (q²/15)^{1/3} ≈ q^{2/3}`, strictly wider than the trivial `|G| < q^{2/5}` (`|G|⁵ < q²`). Pure
Parseval + Markov + the exact-census Wick value; no Weil, no worst-case control. -/
theorem no_johnson_scale_frequency_of_wick_lt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) (hWick : GaussianEnergyBound G 3)
    (hlt : 15 * (G.card : ℝ) ^ 3 < (Fintype.card F : ℝ) ^ 2) :
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
  -- `q² ≤ |S|·q² ≤ 15·|G|³ < q²`, contradiction
  have hb := card_johnson_scale_frequencies_mul_sq_le_wick hψ G hq hWick
  have hq2le : (Fintype.card F : ℝ) ^ 2 ≤
      ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ 2 := by
    nlinarith [hcard1, hqpos]
  linarith [hq2le, hb, hlt]

end ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.rEnergy_three_eq_addEnergy3
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.card_johnson_scale_frequencies_mul_sq_le_wick
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.no_johnson_scale_frequency_of_wick_lt
