/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussianEnergyFromPairing
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment

/-!
# The `r = 3` energy rung: `GaussianEnergyBound G 3` from a `repThree` condition (#407)

This is the **`r = 3` analogue of the landed `r = 2` reducer** (`AdditiveEnergyRepBound`:
`repCount t ≤ 2 ⟹ E₂(G) ≤ 3|G|²`, the Sidon-2 / `repTwo` rung). It reduces the prize
per-frequency energy carrier `GaussPeriodMomentBound.GaussianEnergyBound G 3`, i.e.

> `E₃(G) = rEnergy G 3 ≤ (2·3−1)‼·|G|³ = 5‼·|G|³ = 15·|G|³`     (the char-0 Gaussian value),

to **one** clean in-tree `repThree`-type condition: the **antipodal-pairing residual at order 6**
(`RepThree` below — every zero-sum `6`-tuple of `G` is a disjoint union of antipodal pairs
`{z, −z}`), plus negation-closure of `G`. Everything else is discharged here from proven in-tree
substrate, so the open surface is localized to exactly that single residual.

The reduction chain (all but `RepThree` proven):

1. `rEnergy G 3 = N0 G 6`           — `N0_eq_rEnergy_of_neg_closed` (negation-closure bijection,
                                       via reality of the periods; needs a primitive `ψ`);
2. `N0 G 6 = zeroSumCount G 6`      — indicator-sum = filter-card (`Finset.card_filter`);
3. `zeroSumCount G 6 ≤ #pairings · |G|³` — `zeroSumCount_le_pairings` (K1 counting core), under
                                       the `RepThree` antipodal-pairing residual;
4. `#pairings(Fin 6) = 5‼ = 15`    — `pairings_card_eq_doubleFactorial` (the matching census).

Composing gives `rEnergy G 3 ≤ 15·|G|³ = GaussianEnergyBound G 3`.

**Honest scope (the residual that remains).** `RepThree` is the genuine char-0 / above-threshold
input (Lam–Leung: in characteristic 0 every vanishing sum of six `2^μ`-th roots of unity splits
into three antipodal pairs). Its **char-`p` transfer** to the prize regime `n = 2^30`, `q = 2^158`
is the open core — same wall as the general-`r` `H` input of `gaussianEnergyBound_of_pairing`, here
pinned to the single order-6 instance. This file does NOT close that; it closes the *reduction*
to it, exactly as the `r = 2` file reduces to `repCount ≤ 2`. With `RepThree` the bound is a
theorem; the `r ≥ 4` rungs and the char-`p` transfer of `RepThree` stay open.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.GaussianEnergyFromPairing

namespace ArkLib.ProximityGap.GaussianEnergyThreeRepThree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The `repThree` condition (antipodal-pairing residual at order 6).** Every zero-sum
`6`-tuple of `G` is antipodally paired: there is a perfect matching `σ` of the six positions
with `c (σ i) = −c i` for all `i`. This is the `r = 3` instance of the no-genuine-relation
hypothesis (char-0 Lam–Leung for six `2^μ`-th roots of unity); its char-`p` transfer is the
open core. The exact `r = 3` analogue of the `r = 2` Sidon condition `repCount t ≤ 2`. -/
def RepThree (G : Finset F) : Prop :=
  ∀ c ∈ Fintype.piFinset (fun _ : Fin (2 * 3) => G), (∑ i, c i = 0) →
    ∃ σ : Equiv.Perm (Fin (2 * 3)), IsPairing σ ∧ ∀ i, c (σ i) = - c i

/-- **`N₀ = zeroSumCount`** (indicator sum = filter cardinality): the relation count `N₀(G,m)`
written as a sum of indicators equals the cardinality of the zero-sum filter `Z_m(G)`. -/
theorem N0_eq_zeroSumCount (G : Finset F) (m : ℕ) : N0 G m = zeroSumCount G m := by
  classical
  rw [N0, zeroSumCount, Finset.card_filter]

/-- **The `r = 3` energy rung.** For a negation-closed `G` (`hG`) with a primitive additive
character (`hψ`), the `repThree` antipodal-pairing residual discharges the prize energy carrier
`GaussianEnergyBound G 3 : rEnergy G 3 ≤ 15·|G|³`. The exact `r = 3` analogue of
`additiveEnergy_le_three_of_repTwo`. -/
theorem gaussianEnergyBound_three_of_repThree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : ∀ x ∈ G, -x ∈ G) (hrep : RepThree G) :
    GaussianEnergyBound G 3 := by
  classical
  -- the matching census at order 6: #pairings(Fin 6) = 5‼ = 15
  have hcount : (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin (2 * 3)) => IsPairing σ)).card
      ≤ Nat.doubleFactorial (2 * 3 - 1) :=
    le_of_eq (pairings_card_eq_doubleFactorial 3)
  -- energy ↔ zero-sum count (negation-closure bijection, via period reality)
  have henergy : rEnergy G 3 = zeroSumCount G (2 * 3) := by
    rw [← N0_eq_zeroSumCount, N0_eq_rEnergy_of_neg_closed hψ G hG 3]
  -- close via the all-`r` pairing reducer
  exact gaussianEnergyBound_of_pairing G 3 henergy hcount hrep

/-- **Concrete `15·|G|³` form.** Restates `gaussianEnergyBound_three_of_repThree` with the
double factorial evaluated to `15`, the char-0 Gaussian value `(2·3−1)‼ = 5‼ = 15`. -/
theorem rEnergy_three_le_of_repThree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : ∀ x ∈ G, -x ∈ G) (hrep : RepThree G) :
    (rEnergy G 3 : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by
  have h := gaussianEnergyBound_three_of_repThree hψ hG hrep
  unfold GaussianEnergyBound at h
  have h15 : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rwa [h15] at h

end ArkLib.ProximityGap.GaussianEnergyThreeRepThree

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.GaussianEnergyThreeRepThree.N0_eq_zeroSumCount
#print axioms ArkLib.ProximityGap.GaussianEnergyThreeRepThree.gaussianEnergyBound_three_of_repThree
#print axioms ArkLib.ProximityGap.GaussianEnergyThreeRepThree.rEnergy_three_le_of_repThree
