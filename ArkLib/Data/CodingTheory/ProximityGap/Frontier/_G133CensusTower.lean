/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G132PerRungBudgetAssembly

/-!
# G133: the census tower — the whole DC hierarchy from the disjoint-census family

The capstone of the descent programme (G121–G132).  Two theorems:

1. `perRung_census_gate`: at every rung `11 ≤ t ≤ 110`, `DCEnergyBound G t` follows from
   DC-shape bounds at the eight predecessor rungs plus the rung-`t` fully-disjoint census
   fitting the Wick budget and half the DC mass.
2. `dc_tower` (**the tower**): by strong induction, the DC-shape bounds hold at ALL rungs
   `t ≤ 110` given only
   - the disjoint-census bounds `2·q·depthFiber G t t ≤ 2·q·Wick_t + n^{2t}` for
     `11 ≤ t ≤ 110`, and
   - low-rung anchors (`t ≤ 10`).

   Corollary `dcEnergyBound_of_census_family`: `DCEnergyBound G t` at every rung
   `11 ≤ t ≤ 110` from the same data.

**The entire production DC hierarchy at a certified prime is now one disjoint-census family
plus ten low-rung anchors.**  Every step in between — decoders, weighting, welds, LPs,
isolation, budgets — is unconditional with kernel constants (G89→G132).

**Honest scope.**  The census bounds and the low-rung anchors are the wall; no claim they
hold.  CORE remains OPEN.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G133CensusTower

open Finset
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld
open ArkLib.ProximityGap.Frontier.G126DisjointCensusGate
open ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ℕ-clean DC shape at rung `s` (matches `dcEnergyBound_iff_nat` at `#G = 2^30`). -/
def DCShape (F : Type*) [Fintype F] [DecidableEq F] [AddCommMonoid F]
    (G : Finset F) (s : ℕ) : Prop :=
  Fintype.card F * Finset.addREnergy s G
    ≤ Fintype.card F * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
      + (2 ^ 30) ^ (2 * s)

/-- **Per-rung census gate.**  At every rung `11 ≤ t ≤ 110`: DC-shape bounds at the eight
predecessor rungs plus the rung-`t` disjoint census fitting Wick and half the DC mass give
`DCEnergyBound G t`. -/
theorem perRung_census_gate {t : ℕ} (ht11 : 11 ≤ t) (ht : t ≤ 110)
    (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hq : Fintype.card F ≤ 2 ^ 160)
    (hDC : ∀ s, t - 8 ≤ s → s < t → DCShape F G s)
    (hcensus : 2 * (Fintype.card F * depthFiber G t t)
        ≤ 2 * (Fintype.card F *
            (Nat.doubleFactorial (2 * t - 1) * (2 ^ 30) ^ t))
          + (2 ^ 30) ^ (2 * t)) :
    DCEnergyBound G t := by
  have hE0 : Finset.addREnergy 0 G ≤ 1 := by
    rw [Finset.addREnergy_def]
    simp
  have hEs : ∀ s, 1 ≤ s → Finset.addREnergy s G ≤ (2 ^ 30 : ℕ) ^ (2 * s - 1) := by
    intro s hs
    have := Finset.addREnergy_le hs G
    rwa [hcard] at this
  have hbudget := perRung_full_budget ht11 ht (Fintype.card F) hq
    (fun s => Finset.addREnergy s G) hE0 hEs hDC
  have hover : descentOverhead G t
      = ∑ s ∈ Finset.range t,
          (Nat.descFactorial t (t - s)) ^ 2 *
            ((2 ^ 30) ^ (t - s) * Finset.addREnergy s G) := by
    unfold descentOverhead
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hcard]
  have htwo : 2 * (Fintype.card F * (depthFiber G t t + descentOverhead G t))
      ≤ 2 * (Fintype.card F *
          (Nat.doubleFactorial (2 * t - 1) * G.card ^ t)
        + G.card ^ (2 * t)) := by
    have hcard2t : G.card ^ (2 * t) = (2 ^ 30 : ℕ) ^ (2 * t) := by rw [hcard]
    have hcardt : G.card ^ t = (2 ^ 30 : ℕ) ^ t := by rw [hcard]
    calc
      2 * (Fintype.card F * (depthFiber G t t + descentOverhead G t))
          = 2 * (Fintype.card F * depthFiber G t t)
            + 2 * (Fintype.card F * descentOverhead G t) := by ring
      _ ≤ (2 * (Fintype.card F *
              (Nat.doubleFactorial (2 * t - 1) * (2 ^ 30) ^ t))
            + (2 ^ 30) ^ (2 * t)) + (2 ^ 30) ^ (2 * t) := by
        refine Nat.add_le_add hcensus ?_
        rw [hover]
        exact hbudget
      _ = 2 * (Fintype.card F *
            (Nat.doubleFactorial (2 * t - 1) * G.card ^ t)
          + G.card ^ (2 * t)) := by
        rw [hcard2t, hcardt]
        ring
  have hgate : Fintype.card F * (depthFiber G t t + descentOverhead G t)
      ≤ Fintype.card F * (Nat.doubleFactorial (2 * t - 1) * G.card ^ t)
        + G.card ^ (2 * t) :=
    Nat.le_of_mul_le_mul_left htwo (by norm_num)
  exact dcEnergyBound_of_disjoint_census G t hgate

/-- `DCEnergyBound` at `#G = 2^30` is exactly the ℕ-clean `DCShape`. -/
theorem dcShape_of_dcEnergyBound {t : ℕ} (G : Finset F) (hcard : G.card = 2 ^ 30)
    (h : DCEnergyBound G t) : DCShape F G t := by
  have := (dcEnergyBound_iff_nat G t).mp h
  rw [rEnergy_eq_addREnergy, hcard] at this
  exact this

/-- **The census tower.**  By strong induction over rungs: the DC shape holds at every rung
`t ≤ 110`, given only the disjoint-census family at rungs `11..110` and low-rung anchors. -/
theorem dc_tower (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hq : Fintype.card F ≤ 2 ^ 160)
    (hanchor : ∀ s, s ≤ 10 → DCShape F G s)
    (hcensus : ∀ t, 11 ≤ t → t ≤ 110 →
      2 * (Fintype.card F * depthFiber G t t)
        ≤ 2 * (Fintype.card F *
            (Nat.doubleFactorial (2 * t - 1) * (2 ^ 30) ^ t))
          + (2 ^ 30) ^ (2 * t)) :
    ∀ t, t ≤ 110 → DCShape F G t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      intro ht110
      rcases Nat.lt_or_ge t 11 with hlow | hhigh
      · exact hanchor t (by omega)
      · have hDCpred : ∀ s, t - 8 ≤ s → s < t → DCShape F G s := by
          intro s hs1 hs2
          exact ih s hs2 (by omega)
        have hgate := perRung_census_gate hhigh ht110 G hcard hq hDCpred
          (hcensus t hhigh ht110)
        exact dcShape_of_dcEnergyBound G hcard hgate

/-- **Corollary: the whole DC hierarchy from the census family.**  `DCEnergyBound G t` at
every rung `11 ≤ t ≤ 110`, from the disjoint-census family and the low-rung anchors
alone. -/
theorem dcEnergyBound_of_census_family (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hq : Fintype.card F ≤ 2 ^ 160)
    (hanchor : ∀ s, s ≤ 10 → DCShape F G s)
    (hcensus : ∀ t, 11 ≤ t → t ≤ 110 →
      2 * (Fintype.card F * depthFiber G t t)
        ≤ 2 * (Fintype.card F *
            (Nat.doubleFactorial (2 * t - 1) * (2 ^ 30) ^ t))
          + (2 ^ 30) ^ (2 * t)) :
    ∀ t, 11 ≤ t → t ≤ 110 → DCEnergyBound G t := by
  intro t ht11 ht110
  have hDCpred : ∀ s, t - 8 ≤ s → s < t → DCShape F G s := by
    intro s hs1 hs2
    exact dc_tower G hcard hq hanchor hcensus s (by omega)
  exact perRung_census_gate ht11 ht110 G hcard hq hDCpred (hcensus t ht11 ht110)

end ArkLib.ProximityGap.Frontier.G133CensusTower

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G133CensusTower.perRung_census_gate
#print axioms ArkLib.ProximityGap.Frontier.G133CensusTower.dcShape_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.G133CensusTower.dc_tower
#print axioms
  ArkLib.ProximityGap.Frontier.G133CensusTower.dcEnergyBound_of_census_family
