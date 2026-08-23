/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMarkovWick
import ArkLib.Data.CodingTheory.ProximityGap.PrizeSpectralLevelSetSharp

/-!
# The sixth-moment (cube-level) sharp spectral level-set upper bound (#444)

`PrizeSpectralLevelSetSharp.prize_levelset_sharp` gave the **fourth-moment** level-set tail
`#{b : lam <= ||eta_b||} * lam^4 <= q * E_2(G)`, with the exact in-regime `E_2 = 3n^2 - 3n`. This
file gives the next rung -- the **sixth-moment** level-set tail at the cube of the spectral scale:

> `#{b : lam <= ||eta_b||} * lam^6 <= q * E_3(G)`,

read off the proven sixth-moment Parseval law `sum_b ||eta_b||^6 = q * E_3(G)`
(`subgroup_gaussSum_sixthMoment`). With the char-0 Gaussian (Wick) bound
`E_3(G) <= (2*3-1)!! * |G|^3 = 15 * |G|^3` (the `GaussianEnergyBound G 3` predicate, proven for
`mu_n` in the prize regime via the Lam-Leung antipodal census) this is

> `#{b : lam <= ||eta_b||} * lam^6 <= q * 15 * |G|^3`,

a **sharper tail at the `sqrt(n)` scale** than the fourth-moment bound (a `lam^6` decay vs `lam^4`):
setting `lam = sqrt(c*n)` gives `#{b : ||eta_b|| >= sqrt(c*n)} <= q * 15 / c^3 = O(q/c^3)`, tighter
control of the resonant-frequency count than the fourth-moment `O(q/c^2)`.

## Theorems

* **`prize_levelset_sixth`** -- `#{b : lam <= ||eta_b||} * lam^6 <= q * E_3(G)` for any `G`, any
  `lam >= 0` (the raw sixth-moment level-set, no hypothesis on `G`). The bridge
  `E_3(G) = addEnergy3 G` is internal to `subgroup_gaussSum_sixthMoment`.
* **`prize_levelset_sixth_wick`** -- under the char-0 Wick bound `GaussianEnergyBound G 3`
  (`rEnergy G 3 <= 15*|G|^3`), `#{b : lam <= ||eta_b||} * lam^6 <= q * 15 * |G|^3`. The cube-level
  analogue of `prize_levelset_sharp`, with the exact `Theta(n^3)` Wick value.

## Honest scope

This is the AVERAGE-side spectral tail (a *count* of resonant frequencies above `lam`), at the cube
of the second-moment scale, sharpened by the proven char-0 Wick bound. It does NOT pin `delta*`: the
worst-case single-frequency BGK/Paley sqrt-cancellation wall `M(mu_n) <= C*sqrt(n*log(p/n))` (CORE)
is **untouched** and **OPEN** -- it is the single worst `lam` above this average L^6 mass. The Wick
input is consumed as an explicit hypothesis (char-0 / large-`p`). NON-MOMENT in spirit (consumes an
exact-census Wick value). Companion to `SubgroupGaussSumSixthMarkovWick` (the no-Johnson-threshold
side of the same sixth moment).

Issue #444. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.PrizeSpectralLevelSetSixth

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sixth-moment (cube-level) sharp level-set tail.** From the proven sixth-moment Parseval law
`sum_b ||eta_b||^6 = q * E_3(G)`, the number of frequencies with `||eta_b|| >= lam` satisfies
`#{b : lam <= ||eta_b||} * lam^6 <= q * E_3(G)`. The cube-of-the-scale analogue of
`prize_levelset_sharp` (which is `lam^4 <= q*E_2`). No hypothesis on `G`; no Weil. -/
theorem prize_levelset_sixth {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ((univ.filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ) * lam ^ 6
      ≤ (Fintype.card F : ℝ) * (addEnergy3 G : ℝ) := by
  classical
  set S := univ.filter (fun b => lam ≤ ‖eta ψ G b‖) with hSdef
  have h1 : (S.card : ℝ) * lam ^ 6 = ∑ _b ∈ S, lam ^ 6 := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2' : ∑ _b ∈ S, lam ^ 6 ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 6 :=
    Finset.sum_le_sum (fun b hb => pow_le_pow_left₀ hlam (Finset.mem_filter.mp hb).2 6)
  have h3 : ∑ b ∈ S, ‖eta ψ G b‖ ^ 6 ≤ ∑ b : F, ‖eta ψ G b‖ ^ 6 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => by positivity)
  rw [h1]
  calc ∑ _b ∈ S, lam ^ 6
      ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 6 := h2'
    _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ 6 := h3
    _ = (Fintype.card F : ℝ) * (addEnergy3 G : ℝ) := subgroup_gaussSum_sixthMoment hψ G

/-- **Wick-sharpened sixth-moment level-set tail.** Under the char-0 Wick bound
`GaussianEnergyBound G 3` (`rEnergy G 3 <= 15*|G|^3`), feeding the bridge `E_3(G) = rEnergy G 3` into
`prize_levelset_sixth` gives `#{b : lam <= ||eta_b||} * lam^6 <= q * 15 * |G|^3`. The cube-level
analogue of `prize_levelset_sharp`, with the exact `Theta(n^3)` Wick value: at `lam = sqrt(c*n)` this
is `#{b : ||eta_b|| >= sqrt(c*n)} <= q * 15 / c^3 = O(q/c^3)` (vs the fourth-moment `O(q/c^2)`). -/
theorem prize_levelset_sixth_wick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hWick : GaussianEnergyBound G 3) {lam : ℝ} (hlam : 0 ≤ lam) :
    ((univ.filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ) * lam ^ 6
      ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := by
  have hbase := prize_levelset_sixth hψ G hlam
  -- E_3 = rEnergy G 3 (bridge), and rEnergy G 3 <= 15*|G|^3 (Wick)
  have hWick' : (rEnergy G 3 : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by
    have h := hWick
    unfold GaussianEnergyBound at h
    have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
    rwa [hdf] at h
  have hE3le : (addEnergy3 G : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by
    rw [show (addEnergy3 G : ℝ) = (rEnergy G 3 : ℝ) from by rw [rEnergy_three_eq_addEnergy3 hψ G]]
    exact hWick'
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ((univ.filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ) * lam ^ 6
      ≤ (Fintype.card F : ℝ) * (addEnergy3 G : ℝ) := hbase
    _ ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := by
        exact mul_le_mul_of_nonneg_left hE3le hqnn

end ArkLib.ProximityGap.PrizeSpectralLevelSetSixth

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.PrizeSpectralLevelSetSixth.prize_levelset_sixth
#print axioms ArkLib.ProximityGap.PrizeSpectralLevelSetSixth.prize_levelset_sixth_wick
