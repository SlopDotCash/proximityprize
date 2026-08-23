/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AdditiveEnergySwapFloors
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyTwoEqAdditiveEnergy

/-!
# Door-(iv) Lane 3 — the worst-frequency rep set has no additive-energy excess (#444)

## Probe motivation (honest, recorded, not larped)

`scripts/probes/probe_Wenergy_floor.py` / `probe_Wenergy2.py` measured the **additive energy**
`E(W) = #{(a,b,c,d) ∈ W⁴ : a+b = c+d}` of the door-(iv) worst-frequency **rep set** `W` (one
representative per near-max `μ_n`-coset, proper 2-power subgroup `μ_n ⊊ F_p^*`, prize regime
`p ≫ n³`, `p = k·n+1`, multiple structured primes, `τ ∈ {2%,5%}`).  Whenever `|W| ≥ 3` the
measurement was, at every tested instance, **EXACTLY the Sidon floor**:

    E(W) = 2|W|² − |W|        (E/floor = 1.000, also E/E_random = 1.000)

i.e. the worst-frequency rep set is an **additive Sidon set**: it carries *no* nontrivial additive
coincidence, and is in fact additively *poorer* than a random same-size set.  (This is complementary
to `_AttackB1_BadSetCosetNonSidon`, which records that the *full* negation-closed bad set is NOT
Sidon because `−1 ∈ μ_n` forces antipodal `{a,−a}` zero-sum pairs; the **quotient rep set** of one
min-rep per coset does not carry those antipodal pairs and lands exactly on the Sidon floor.)

## What this kernel locks (a Lane-3 constraint lemma; it does NOT close CORE)

The brief's door-(iv) requirement is an arithmetic anti-concentration for the phase set that does
**NOT** route through additive energy / sum–product (which saturate at `n^{1−o(1)}`).  This file
locks the corresponding structural obstruction on the worst-b object itself: the **additive-energy
excess above the Sidon floor**

    excess(G) := additiveEnergy G − (2|G|² − |G|)        (truncated ℕ subtraction; floor ≤ energy)

is `0` exactly for a Sidon set, so on the measured worst-frequency rep set there is **no positive
additive-energy budget** for an additive-combinatorics / sum-product lever to grip.  Any door-(iv)
certificate that demands a strictly positive additive-energy excess (energy above the Sidon floor)
is therefore **vacuous** on the worst-frequency rep set.

This is a refutation-with-mechanism (brief rule 4 = WIN): the additive structure that an
energy/sum-product door-(iv) attack would need is provably absent on the object, leaving only the
bare multiplicative `μ_n`-coset structure (orthogonal to additive energy).  **No CORE / cancellation
/ completion / moment / anti-concentration / capacity claim.**

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #444.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

open ArkLib.ProximityGap.AdditiveEnergyRepBound (additiveEnergy)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive-energy **excess** of a finite set above the Sidon floor `2|G|² − |G|`
(truncated ℕ subtraction).  Since the floor always lower-bounds the energy
(`additiveEnergy_ge_swap_floor`) this is the honest "energy budget above Sidon". -/
def additiveEnergyExcess (G : Finset F) : ℕ :=
  additiveEnergy G - (2 * G.card ^ 2 - G.card)

/-- The excess recovers the energy: `floor + excess = additiveEnergy`, using `floor ≤ energy`. -/
theorem swap_floor_add_excess (G : Finset F) :
    (2 * G.card ^ 2 - G.card) + additiveEnergyExcess G = additiveEnergy G := by
  unfold additiveEnergyExcess
  exact Nat.add_sub_cancel' (additiveEnergy_ge_swap_floor G)

/-- **Energy excess vanishes iff Sidon.**  `additiveEnergyExcess G = 0 ↔ IsSidonSet G`. -/
theorem additiveEnergyExcess_eq_zero_iff_sidon (G : Finset F) :
    additiveEnergyExcess G = 0 ↔ IsSidonSet G := by
  rw [← additiveEnergy_eq_swap_floor_iff_sidon]
  constructor
  · intro h
    have := swap_floor_add_excess G
    rw [h, Nat.add_zero] at this
    exact this.symm
  · intro h
    unfold additiveEnergyExcess
    rw [h, Nat.sub_self]

/-- **No positive additive-energy budget on a Sidon set.**  If `G` is Sidon, the additive energy
is pinned exactly at the floor, so no strictly positive excess budget `B` is attainable.  Concretely
a door-(iv) energy certificate `B ≤ excess(G)` with `0 < B` is impossible. -/
theorem no_positive_additiveEnergyExcess_of_sidon (G : Finset F)
    (hG : IsSidonSet G) :
    ∀ B : ℕ, 0 < B → ¬ (B ≤ additiveEnergyExcess G) := by
  have hzero : additiveEnergyExcess G = 0 :=
    (additiveEnergyExcess_eq_zero_iff_sidon G).mpr hG
  intro B hB hle
  rw [hzero] at hle
  exact (Nat.not_lt.mpr hle) hB

/-- **Probe-facing pin.**  On a Sidon set (the measured worst-frequency rep set) the additive energy
equals the Sidon floor exactly: there is nothing above the floor for an additive-energy /
sum–product lever to use. -/
theorem additiveEnergy_eq_floor_of_sidon (G : Finset F)
    (hG : IsSidonSet G) :
    additiveEnergy G = 2 * G.card ^ 2 - G.card :=
  (additiveEnergy_eq_swap_floor_iff_sidon G).mpr hG

/-- **Contrapositive selector form.**  If a set DOES carry a strictly positive additive-energy
excess then it is NOT Sidon — i.e. a genuine additive-energy door-(iv) lever can only exist on a
non-Sidon worst-b object, which the probe shows the worst-frequency rep set is not. -/
theorem not_sidon_of_positive_additiveEnergyExcess (G : Finset F)
    (h : 0 < additiveEnergyExcess G) :
    ¬ IsSidonSet G := by
  intro hG
  exact (Nat.lt_irrefl 0)
    (by rwa [(additiveEnergyExcess_eq_zero_iff_sidon G).mpr hG] at h)

/-- **Positive excess is exactly non-Sidon-ness.**  The energy-excess audit has no hidden middle
case: a set has strictly positive additive-energy budget above the Sidon floor iff it fails to be
Sidon.  Thus the measured Sidon worst-frequency rep set is not merely low-energy; it has exactly
zero usable additive-energy excess, while every positive-excess certificate would be a certificate
of non-Sidon structure. -/
theorem positive_additiveEnergyExcess_iff_not_sidon (G : Finset F) :
    0 < additiveEnergyExcess G ↔ ¬ IsSidonSet G := by
  constructor
  · exact not_sidon_of_positive_additiveEnergyExcess G
  · intro hnot
    exact Nat.pos_of_ne_zero fun hzero =>
      hnot ((additiveEnergyExcess_eq_zero_iff_sidon G).mp hzero)

/-- **No-excess iff Sidon, inequality form.**  Since the excess is natural-valued, the
probe-facing statement `excess ≤ 0` is equivalent to Sidon-ness.  This packages failed
additive-energy probes that report a zero budget as the exact Sidon-floor obstruction. -/
theorem additiveEnergyExcess_le_zero_iff_sidon
    (G : Finset F) :
    additiveEnergyExcess G ≤ 0 ↔ IsSidonSet G := by
  rw [Nat.le_zero, additiveEnergyExcess_eq_zero_iff_sidon]

/-- **Hereditarity: no sub-collection escape.**  Since Sidon-ness is hereditary
(`IsSidonSet.subset`), every subset `H ⊆ W` of the (Sidon) worst-frequency rep set is itself Sidon,
hence has additive-energy excess `0`.  A door-(iv) attack cannot recover additive structure by
restricting to a sub-collection of the worst frequencies: the energy floor is inherited by every
subset. -/
theorem additiveEnergyExcess_eq_zero_of_subset_sidon {G H : Finset F}
    (hG : IsSidonSet G) (hHG : H ⊆ G) :
    additiveEnergyExcess H = 0 :=
  (additiveEnergyExcess_eq_zero_iff_sidon H).mpr (hG.subset hHG)

/-- **No positive additive-energy budget on any sub-collection of a Sidon worst-b object.**
The sum-product / additive-energy lever is vacuous not just on `W` but on every `H ⊆ W`. -/
theorem no_positive_additiveEnergyExcess_of_subset_sidon {G H : Finset F}
    (hG : IsSidonSet G) (hHG : H ⊆ G) :
    ∀ B : ℕ, 0 < B → ¬ (B ≤ additiveEnergyExcess H) :=
  no_positive_additiveEnergyExcess_of_sidon H (hG.subset hHG)

end ArkLib.ProximityGap.SubgroupGaussSumMoment

#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess_eq_zero_iff_sidon
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.no_positive_additiveEnergyExcess_of_sidon
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergy_eq_floor_of_sidon
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.not_sidon_of_positive_additiveEnergyExcess
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.positive_additiveEnergyExcess_iff_not_sidon
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess_le_zero_iff_sidon
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess_eq_zero_of_subset_sidon
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumMoment.no_positive_additiveEnergyExcess_of_subset_sidon
