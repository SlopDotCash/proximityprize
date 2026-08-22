/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R55Depth3VarianceReformulation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R56RepThreeMultiplicativeInvariance

/-!
# LANE B2 (#466 round 57): THE DEVIATION FUNCTION — mean-zero, G-invariant, and the orbit
  multiplicity bound (capstone of the depth-3 variance arc)

Rounds 55–56 recast the DC-subtracted depth-3 energy as the ℓ²-flatness deficit
`∑_c d(c)²` of the deviation function `d(c) = q·rep3 G c − |G|³`, and showed `rep3` (hence `d`)
is `G`-invariant.  This brick packages the structural consequences that finish the arc:

* **`deviation_smul`** :  `d(a·c) = d(c)` for `a ∈ G`  (from `rep3_smul`);
* **`sum_deviation_zero`** :  `∑_c d(c) = 0`  (the deviation is mean-zero — from `sum_rep3`);
* **`deficit_ge_orbit`** :  for `b ≠ 0`, `∑_c d(c)² ≥ |G| · d(b)²`.

The last is the additive-side mirror of the in-tree character reduction
`GaussPeriodCosetReduction.card_mul_eta_pow_le_sum_erase`: because `d` is constant on the
multiplicative orbit `G·b` (which has exactly `|G|` elements for `b ≠ 0`), a single large
period-deviation forces the whole flatness deficit up by a factor `|G|`.  Via the round-55
`variance_identity` (`∑_c d(c)² = q·(q·E₃ − |G|⁶)`) this is exactly the `/|G|` saving the moment
method relies on: the deficit "sees" each Gauss period `|G|` times, so the effective number of
degrees of freedom is `(q−1)/|G|`, not `q`.

Does not break the wall — the per-orbit deviations are still Paley/BGK-governed — but it is the
complete, machine-checked structural normalization of the depth-3 variance.  Issue #466,
round 57, LANE B2.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R57Depth3DeviationOrbitBound

open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation
open ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **deviation function** `d(c) = q·rep3 G c − |G|³` — the summand of the round-55
flatness deficit `∑_c d(c)² = q·(q·E₃ − |G|⁶)`. -/
def deviation (G : Finset F) (c : F) : ℝ :=
  (Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3

/-- **The deviation inherits the multiplicative symmetry** of `rep3`: `d(a·c) = d(c)` for
`a ∈ G`. -/
theorem deviation_smul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    deviation G (a * c) = deviation G c := by
  unfold deviation
  rw [rep3_smul G hmul hinv h0 ha c]

/-- **The deviation is mean-zero**: `∑_c d(c) = 0`. -/
theorem sum_deviation_zero (G : Finset F) : ∑ c : F, deviation G c = 0 := by
  unfold deviation
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ c : F, (rep3 G c : ℝ) = (G.card : ℝ) ^ 3 := by
    calc ∑ c : F, (rep3 G c : ℝ) = ((∑ c : F, rep3 G c : ℕ) : ℝ) := by push_cast; rfl
      _ = ((G.card ^ 3 : ℕ) : ℝ) := by rw [sum_rep3 G]
      _ = (G.card : ℝ) ^ 3 := by push_cast; ring
  have h2 : ∑ _c : F, (G.card : ℝ) ^ 3 = (Fintype.card F : ℝ) * (G.card : ℝ) ^ 3 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, h2]; ring

/-- **The orbit multiplicity bound.**  For a multiplicative subgroup `G` and `b ≠ 0`, the
flatness deficit is at least `|G|` times the single-period contribution `d(b)²`, because `d` is
constant on the `|G|`-element orbit `G·b`. -/
theorem deficit_ge_orbit (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (deviation G b) ^ 2 ≤ ∑ c : F, (deviation G c) ^ 2 := by
  classical
  -- the orbit `G·b = image (· * b) G`, of cardinality `|G|` (free action, `b ≠ 0`)
  set orbit : Finset F := G.image (fun a => a * b) with horbit
  have hcard : orbit.card = G.card := by
    rw [horbit, Finset.card_image_of_injective _ (fun x y h => by
      exact mul_right_cancel₀ hb h)]
  -- `d` is constant `= d(b)` on the orbit
  have hconst : ∀ c ∈ orbit, (deviation G c) ^ 2 = (deviation G b) ^ 2 := by
    intro c hc
    rw [horbit, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    rw [show a * b = a * b from rfl, deviation_smul G hmul hinv h0 ha b]
  -- lower-bound the full sum by the orbit sum
  calc (G.card : ℝ) * (deviation G b) ^ 2
      = ∑ _c ∈ orbit, (deviation G b) ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = ∑ c ∈ orbit, (deviation G c) ^ 2 :=
        (Finset.sum_congr rfl hconst).symm
    _ ≤ ∑ c : F, (deviation G c) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun c _ _ => sq_nonneg _)

/-- **The orbit bound in energy form.**  Via the round-55 variance identity, the DC-subtracted
depth-3 energy dominates `|G|` copies of any single period-deviation:
`|G| · d(b)² ≤ q·(q·E₃ − |G|⁶)`. -/
theorem energy_ge_orbit (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (deviation G b) ^ 2
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (addEnergy3 G : ℝ) - (G.card : ℝ) ^ 6) := by
  have h := deficit_ge_orbit G hmul hinv h0 hb
  rwa [show (∑ c : F, (deviation G c) ^ 2)
      = ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2 from rfl,
    variance_identity G] at h

end ArkLib.ProximityGap.Frontier.R57Depth3DeviationOrbitBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R57Depth3DeviationOrbitBound.deviation_smul
#print axioms ArkLib.ProximityGap.Frontier.R57Depth3DeviationOrbitBound.sum_deviation_zero
#print axioms ArkLib.ProximityGap.Frontier.R57Depth3DeviationOrbitBound.deficit_ge_orbit
#print axioms ArkLib.ProximityGap.Frontier.R57Depth3DeviationOrbitBound.energy_ge_orbit
