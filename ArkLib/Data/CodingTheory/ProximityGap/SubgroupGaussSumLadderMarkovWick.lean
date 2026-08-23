/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumLadderMarkov
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# Wick-sharpened general-`r` no-Johnson threshold: `q^{1/2} -> q^{1-o(1)}` (#444)

`SubgroupGaussSumLadderMarkov` proved the general Markov count bound
`#{b : ||eta_b||^2 >= q} * q^{r-1} <= E_r(G)` and then used the **trivial** ceiling
`E_r(G) <= |G|^{2r-1}` (`energyR_le_pow`), giving the no-Johnson threshold `|G|^{2r-1} < q^{r-1}`,
i.e. `|G| < q^{m/(2m+1)} -> q^{1/2}` as `r -> infinity`. That `q^{1/2}` is the strongest threshold
the moment method yields **with the trivial energy bound**.

The char-0 Gaussian (Wick) bound `E_r(G) <= (2r-1)!! * |G|^r` (the `GaussPeriodMomentBound`
predicate `GaussianEnergyBound G r`, proven char-0 for all `r` via the Lam-Leung antipodal census,
`Frontier._CharZeroWickEnergy.gaussianEnergyBound_dyadic`; in-tree for `mu_n` at `r = 2, 3`) replaces
`|G|^{2r-1}` by `(2r-1)!! * |G|^r`. The resulting no-Johnson threshold is

> `(2r-1)!! * |G|^r < q^{r-1}`,   i.e.   `|G| < (q^{r-1}/(2r-1)!!)^{1/r}`,

whose exponent `(r-1)/r -> 1` as `r -> infinity`: the Wick bound pushes the count-side threshold from
`q^{1/2}` all the way to `q^{1-o(1)}`. This is the general-`r` lift of `SubgroupGaussSumSixthMarkovWick`
(the `r = 3` `q^{2/3}` case).

## Theorems

* **`energyR_eq_rEnergy`** -- `energyR G r = rEnergy G r` (the two nested-`piFinset` energy census
  definitions agree; read off the two moment-ladder Parseval laws, cancelling `q != 0`). Lets the
  `rEnergy`-stated `GaussianEnergyBound` feed the `energyR`-stated ladder Markov bound.
* **`card_johnson_scale_frequencies_mul_le_wick`** -- under `GaussianEnergyBound G r` (`r >= 1`),
  `#{b : ||eta_b||^2 >= q} * q^{r-1} <= (2r-1)!! * |G|^r`.
* **`no_johnson_scale_frequency_of_wick_ladder`** -- under `GaussianEnergyBound G r` (`r >= 1`), if
  `(2r-1)!! * |G|^r < q^{r-1}` then **no** frequency reaches the Johnson scale `||eta_b||^2 >= q`.
  The exponent `(r-1)/r -> 1`: the Wick-sharpened threshold tends to `q^{1-o(1)}`, vs the trivial
  `q^{1/2}`.

## Honest scope

AVERAGE-side anti-concentration (a *count* of Johnson-scale frequencies), sharpened by the proven
char-0 Wick bound. **NOT a CORE closure:** the worst-case single-frequency BGK/Paley
sqrt-cancellation wall `M(mu_n) <= C*sqrt(n*log(p/n))` is untouched and **OPEN**. The Wick input is
conditional (char-0 for all `r`; at the fixed prize prime the deep-`r` onset is itself the wall, so
this does NOT silently close it -- it consumes the Wick bound as an explicit hypothesis, exactly
where it is available). NON-MOMENT in spirit (consumes an exact-census Wick value, not a cancellation
bound on `M`). Generalizes `SubgroupGaussSumSixthMarkovWick` (r = 3) to all `r` in one theorem.

Issue #444. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`energyR G r = rEnergy G r`.** The moment-ladder energy census `energyR` and the
`SubgroupGaussSumMoment` relation energy `rEnergy` are the same nested-`piFinset` count. Read off the
two `2r`-th moment Parseval laws (`energyR` version `subgroup_gaussSum_moment` and the
`SubgroupGaussSumMoment` version), cancelling `q = |F| != 0`. Lets `GaussianEnergyBound` (stated on
`rEnergy`) feed the `energyR`-stated ladder Markov bound. The primitive `psi` is a proof device. -/
theorem energyR_eq_rEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    energyR G r = ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r := by
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hP1 := subgroup_gaussSum_moment hψ G r
  have hP2 := ArkLib.ProximityGap.SubgroupGaussSumMoment.subgroup_gaussSum_moment hψ G r
  have hsum_eq : (Fintype.card F : ℝ) * (energyR G r : ℝ)
      = (Fintype.card F : ℝ)
          * (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ) := by
    rw [← hP1, ← hP2]
  have hRE : (energyR G r : ℝ)
      = (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ) :=
    mul_left_cancel₀ (ne_of_gt hqR) hsum_eq
  exact_mod_cast hRE

/-- **Wick-sharpened general-`r` Johnson-scale count bound.** From the ladder Markov bound
`#{b : ||eta_b||^2 >= q} * q^{r-1} <= E_r(G)` and the char-0 Wick hypothesis `GaussianEnergyBound G r`
(`rEnergy G r <= (2r-1)!! * |G|^r`), feeding the bridge `energyR = rEnergy` gives
`#{b : ||eta_b||^2 >= q} * q^{r-1} <= (2r-1)!! * |G|^r`. The RHS `(2r-1)!! * |G|^r` is vastly below the
trivial `|G|^{2r-1}` once `|G|` is large. -/
theorem card_johnson_scale_frequencies_mul_le_wick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (hq : 0 < Fintype.card F)
    (hWick : GaussianEnergyBound G r) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ (r - 1)
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  have hMarkov := card_johnson_scale_frequencies_mul_le_energyR hψ G r hr hq
  -- the Wick hypothesis on rEnergy
  have hWick' : (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ)
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := hWick
  -- bridge energyR = rEnergy
  have hbridge : (energyR G r : ℝ)
      = (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ) := by
    rw [energyR_eq_rEnergy hψ G r]
  have hER : (energyR G r : ℝ)
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
    rw [hbridge]; exact hWick'
  exact le_trans hMarkov hER

/-- **The Wick-sharpened `q^{1-o(1)}` no-Johnson threshold.** Under the char-0 Wick bound
`GaussianEnergyBound G r` (`r >= 1`), if `(2r-1)!! * |G|^r < q^{r-1}` then **no** frequency reaches the
Johnson scale `||eta_b||^2 >= q`. The condition is `|G| < (q^{r-1}/(2r-1)!!)^{1/r}`, exponent
`(r-1)/r -> 1` as `r -> infinity`: the Wick bound pushes the count-side threshold from the trivial
`q^{1/2}` (`energyR_le_pow`, exponent `m/(2m+1) -> 1/2`) up to `q^{1-o(1)}`. The `r = 3` instance is
`SubgroupGaussSumSixthMarkovWick.no_johnson_scale_frequency_of_wick_lt` (`q^{2/3}`). -/
theorem no_johnson_scale_frequency_of_wick_ladder {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (hq : 0 < Fintype.card F)
    (hWick : GaussianEnergyBound G r)
    (hlt : (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
      < (Fintype.card F : ℝ) ^ (r - 1)) :
    (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)) = ∅ := by
  classical
  by_contra hne
  have hnemp : (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hcard1 : (1 : ℝ) ≤
      ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) := by
    exact_mod_cast Finset.Nonempty.card_pos hnemp
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (r - 1) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
    positivity
  have hb := card_johnson_scale_frequencies_mul_le_wick hψ G r hr hq hWick
  -- `q^{r-1} <= #S·q^{r-1} <= (2r-1)!!·|G|^r < q^{r-1}`, contradiction
  have hq2le : (Fintype.card F : ℝ) ^ (r - 1) ≤
      ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ (r - 1) := by
    nlinarith [hcard1, hqpos]
  linarith [hq2le, hb, hlt]

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.energyR_eq_rEnergy
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.card_johnson_scale_frequencies_mul_le_wick
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.no_johnson_scale_frequency_of_wick_ladder
