/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R366CenteredRelationAnomaly

/-!
# G75: raw Wick deviation is not the centered relation anomaly

FS15--FS18 control the raw Gaussian energy inequality `E_r ≤ W_r` away from a
resultant-defined bad-prime set, while G64 proves that the principal frequency eventually forces
`E_r > W_r` at the explicit prize field.  Neither statement decides R366's centered relation target.

Write

```text
B_r = shadowEnergy,
C_r = shadowCollisionMass,
E_r = B_r + C_r,
A_r = relationAnomaly = q C_r - (n^(2r) - B_r),
K_r = q W_r - (q-1) B_r.
```

The exact comparison is

```text
A_r - K_r = q (E_r - W_r) - n^(2r).
```

Consequently the R366 target `A_r ≤ K_r` is equivalent to

```text
q (E_r - W_r) ≤ n^(2r),
```

not to the stronger raw sign condition `E_r - W_r ≤ 0`.  The DC correction leaves an allowance
of exactly `n^(2r) / q`.  Thus:

* every raw Wick bound is sufficient for the centered target;
* a positive raw deviation does not by itself refute the centered target;
* failure occurs only when the raw excess exceeds the full DC allowance.

This also separates the actual R367 signed discrepancy from complex Gauss-period averaging.
The identity `eta_{bg} = eta_b` on a multiplicative coset gives phase coherence inside that coset,
but R367's cancellation is between kernel and non-kernel shadow-difference orbits.  No sign or
CORE closure is claimed here.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G75RawDeviationVsRelationAnomaly

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly

/-- The Wick budget left for the centered relation anomaly after paying the characteristic-zero
shadow floor.  R366 uses the concrete value
`W = (2r-1)!! * card(powerRootSet g n)^r`; keeping `W` abstract makes the algebra reusable. -/
noncomputable def relationAnomalyBudget
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n m r : ℕ) (W : ℝ) : ℝ :=
  (Fintype.card F : ℝ) * W -
    ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ)

/-- **The binding identity before representation transport.**  Relative to an arbitrary Wick
scale `W`, the centered anomaly's budget error is the raw shadow-plus-collision deviation, minus the
entire DC mass `n^(2r)`. -/
theorem relationAnomaly_sub_budget_eq_shadowDeviation
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (W : ℝ) :
    relationAnomaly g n m r - relationAnomalyBudget (F := F) n m r W =
      (Fintype.card F : ℝ) *
          ((shadowEnergy n m r : ℝ) + (shadowCollisionMass g n m r : ℝ) - W) -
        (n : ℝ) ^ (2 * r) := by
  unfold relationAnomaly relationAnomalyBudget
  ring

/-- **The concrete power-root identity.**  For an exact-order dyadic power-root set, transport
`shadowEnergy + shadowCollisionMass` to the actual additive energy `rEnergy`. -/
theorem relationAnomaly_sub_budget_eq_rawEnergyDeviation
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (W : ℝ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    relationAnomaly g n m r - relationAnomalyBudget (F := F) n m r W =
      (Fintype.card F : ℝ) * ((rEnergy (powerRootSet g n) r : ℝ) - W) -
        (n : ℝ) ^ (2 * r) := by
  rw [relationAnomaly_sub_budget_eq_shadowDeviation]
  have henergy := rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g n m r hg0 hord hm hn hg
  have henergyReal :
      (rEnergy (powerRootSet g n) r : ℝ) =
        (shadowEnergy n m r : ℝ) + (shadowCollisionMass g n m r : ℝ) := by
    exact_mod_cast henergy
  rw [henergyReal]

/-- **The corrected binding inequality.**  The centered relation target is equivalent to allowing
raw Wick excess up to the full DC mass:

`relationAnomaly ≤ budget  ↔  q * (E_r - W_r) ≤ n^(2r)`.

In particular, the sign of `E_r-W_r` alone does not decide the signed relation route. -/
theorem relationAnomaly_le_budget_iff_q_mul_rawDeviation_le_dc
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (W : ℝ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    relationAnomaly g n m r ≤ relationAnomalyBudget (F := F) n m r W ↔
      (Fintype.card F : ℝ) * ((rEnergy (powerRootSet g n) r : ℝ) - W) ≤
        (n : ℝ) ^ (2 * r) := by
  have hidentity := relationAnomaly_sub_budget_eq_rawEnergyDeviation
    g n m r W hg0 hord hm hn hg
  constructor <;> intro h <;> linarith

/-- The raw Gaussian/Wick bound is sufficient for the centered relation target, but G75's iff
shows it is stronger than necessary by the DC allowance `n^(2r)`. -/
theorem relationAnomaly_le_budget_of_rawEnergy_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (W : ℝ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hraw : (rEnergy (powerRootSet g n) r : ℝ) ≤ W) :
    relationAnomaly g n m r ≤ relationAnomalyBudget (F := F) n m r W := by
  rw [relationAnomaly_le_budget_iff_q_mul_rawDeviation_le_dc
    g n m r W hg0 hord hm hn hg]
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hdev : (rEnergy (powerRootSet g n) r : ℝ) - W ≤ 0 := sub_nonpos.mpr hraw
  have hnonpos :
      (Fintype.card F : ℝ) * ((rEnergy (powerRootSet g n) r : ℝ) - W) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq hdev
  exact hnonpos.trans (by positivity)

/-- Failure of the centered target is equivalently raw excess STRICTLY larger than the DC
allowance.  This is the precise falsifier for any proposed signed-discrepancy estimate. -/
theorem relationAnomaly_budget_lt_iff_dc_lt_q_mul_rawDeviation
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (W : ℝ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    relationAnomalyBudget (F := F) n m r W < relationAnomaly g n m r ↔
      (n : ℝ) ^ (2 * r) <
        (Fintype.card F : ℝ) * ((rEnergy (powerRootSet g n) r : ℝ) - W) := by
  have hidentity := relationAnomaly_sub_budget_eq_rawEnergyDeviation
    g n m r W hg0 hord hm hn hg
  constructor <;> intro h <;> linarith

/-- With the concrete Wick scale, G75's centered relation budget is not merely sufficient for the
prize input: it is EXACTLY `DCEnergyBound` on the power-root set. -/
theorem relationAnomaly_le_wickBudget_iff_dcEnergyBound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    relationAnomaly g n m r ≤ relationAnomalyBudget (F := F) n m r
        ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r) ↔
      DCEnergyBound (powerRootSet g n) r := by
  rw [relationAnomaly_le_budget_iff_q_mul_rawDeviation_le_dc
    g n m r ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r)
    hg0 hord hm hn hg]
  unfold DCEnergyBound
  have hcard : (powerRootSet g n).card = n := by
    classical
    unfold powerRootSet
    rw [Finset.card_image_of_injective _
      (power_index_injective_of_orderOf g n hg0 hord), Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  constructor <;> intro h <;> linarith

#print axioms relationAnomaly_sub_budget_eq_shadowDeviation
#print axioms relationAnomaly_sub_budget_eq_rawEnergyDeviation
#print axioms relationAnomaly_le_budget_iff_q_mul_rawDeviation_le_dc
#print axioms relationAnomaly_le_budget_of_rawEnergy_le
#print axioms relationAnomaly_budget_lt_iff_dc_lt_q_mul_rawDeviation
#print axioms relationAnomaly_le_wickBudget_iff_dcEnergyBound

end ArkLib.ProximityGap.Frontier.G75RawDeviationVsRelationAnomaly
