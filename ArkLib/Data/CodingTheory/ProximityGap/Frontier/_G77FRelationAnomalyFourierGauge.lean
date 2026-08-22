/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R367SignedShadowPairDiscrepancy
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# G77: the signed relation route is gauge — its Fourier dual is the wall object, exactly

R367 exhibited the centered relation anomaly as a SIGNED discrepancy over ordered shadow
pairs (`+(q-1)`-weighted colliding mass against `-1`-weighted non-colliding mass), and the
round notes recorded a "signed-cancellation identity" as the sole unclosed off-BGK hope: some
pairing/involution argument might bound the signed sum below the moment route's strength.

This file computes the signed object's Fourier gauge exactly.  Chaining the in-tree
Parseval identity (`DCSubtractedMoment.sum_nonzero_moment`) with the R312 energy
decomposition (`rEnergy = shadowEnergy + shadowCollisionMass`):

```text
relationAnomaly = Σ_{b≠0} ‖η_b‖^{2r}  −  (q−1) · shadowEnergy.
```

Consequences.

* **The total signed value has an exact nonnegative gauge.**  The signed pair discrepancy,
  summed, equals a sum of NONNEGATIVE terms minus the fixed characteristic-zero floor.  In
  particular the negative mass is exactly capped,
  `relationAnomaly ≥ −(q−1)·shadowEnergy` (`relationAnomaly_ge_neg_floor`), with equality
  slack exactly the DC-subtracted moment.
* **Zero-slack transport.**  Any upper bound `T` on the signed discrepancy is verbatim the
  bound `Σ_{b≠0}‖η_b‖^{2r} ≤ T + (q−1)·shadowEnergy` on the DC-subtracted moment and
  conversely (`relationAnomaly_le_iff_dcMoment_le`).  A signed-route estimate beating Wick
  IS a moment estimate beating Wick — the route is a gauge transform of the wall, not a
  lever on it.
* **Sup-norm capture.**  The prize sup norm sits inside the anomaly-plus-floor form:
  `‖η_b‖^{2r} ≤ relationAnomaly + (q−1)·shadowEnergy` for every `b ≠ 0`
  (`sup_pow_le_relationAnomaly_add_floor`).

Together with R366/G75 (anomaly ≤ Wick budget ⟺ `DCEnergyBound`), this proves that the signed
cross-cell target has no weaker quantitative endpoint than the DC-subtracted moment face.
It does **not** rule out proving that endpoint by exploiting the signed representation—for
example with a genuinely new involution or first-incidence estimate.  CORE remains OPEN / ON-BGK.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly
open ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exact-order power-root set has cardinality `n` (as in G75). -/
theorem powerRootSet_card (g : F) (n : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n) :
    (powerRootSet g n).card = n := by
  classical
  unfold powerRootSet
  rw [Finset.card_image_of_injective _
    (power_index_injective_of_orderOf g n hg0 hord), Finset.card_univ, Fintype.card_fin]

/-- **The Fourier gauge of the signed relation route.**  The centered relation anomaly is
exactly the DC-subtracted `2r`-th moment minus `(q−1)` times the characteristic-zero shadow
floor. -/
theorem relationAnomaly_eq_dcMoment_sub_floor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    relationAnomaly g n m r =
      (∑ b ∈ univ.erase (0 : F), ‖eta ψ (powerRootSet g n) b‖ ^ (2 * r)) -
        ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) := by
  have hmom := sum_nonzero_moment hψ (powerRootSet g n) r
  rw [powerRootSet_card g n hg0 hord] at hmom
  have hE := rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g n m r hg0 hord hm hn hg
  have hEcast :
      (rEnergy (powerRootSet g n) r : ℝ) =
        (shadowEnergy n m r : ℝ) + (shadowCollisionMass g n m r : ℝ) := by
    exact_mod_cast hE
  unfold relationAnomaly
  rw [hEcast] at hmom
  linarith [hmom]

/-- The signed pair discrepancy of R367 has the same Fourier gauge. -/
theorem signedShadowPairDiscrepancy_eq_dcMoment_sub_floor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    signedShadowPairDiscrepancy g n m r =
      (∑ b ∈ univ.erase (0 : F), ‖eta ψ (powerRootSet g n) b‖ ^ (2 * r)) -
        ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) := by
  rw [signedShadowPairDiscrepancy_eq_relationAnomaly]
  exact relationAnomaly_eq_dcMoment_sub_floor hψ g n m r hg0 hord hm hn hg

/-- **The cancellation is exhausted.**  The signed discrepancy plus the floor is a sum of
nonnegative terms; no pairing can push the anomaly below `−(q−1)·shadowEnergy`. -/
theorem relationAnomaly_add_floor_nonneg
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    0 ≤ relationAnomaly g n m r +
      ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) := by
  have hgauge := relationAnomaly_eq_dcMoment_sub_floor hψ g n m r hg0 hord hm hn hg
  have hsum : (0 : ℝ) ≤
      ∑ b ∈ univ.erase (0 : F), ‖eta ψ (powerRootSet g n) b‖ ^ (2 * r) :=
    Finset.sum_nonneg fun b _ => by positivity
  linarith

/-- The exact negative floor for the signed route. -/
theorem relationAnomaly_ge_neg_floor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    -(((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ)) ≤
      relationAnomaly g n m r := by
  have h := relationAnomaly_add_floor_nonneg hψ g n m r hg0 hord hm hn hg
  linarith

/-- **Zero-slack transport.**  A signed-route bound `T` and the corresponding DC-subtracted
moment bound are the SAME inequality; the route carries no independent content. -/
theorem relationAnomaly_le_iff_dcMoment_le
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (g : F) (n m r : ℕ) (T : ℝ)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    relationAnomaly g n m r ≤ T ↔
      (∑ b ∈ univ.erase (0 : F), ‖eta ψ (powerRootSet g n) b‖ ^ (2 * r)) ≤
        T + ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) := by
  have hgauge := relationAnomaly_eq_dcMoment_sub_floor hψ g n m r hg0 hord hm hn hg
  constructor <;> intro h <;> linarith

/-- **Sup-norm capture.**  Every nonzero-frequency Gauss-period power is dominated by the
anomaly-plus-floor form: the prize sup norm lives inside the signed route's nonnegative
part. -/
theorem sup_pow_le_relationAnomaly_add_floor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (g : F) (n m r : ℕ) (b : F) (hb : b ≠ 0)
    (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    ‖eta ψ (powerRootSet g n) b‖ ^ (2 * r) ≤
      relationAnomaly g n m r +
        ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) := by
  have hgauge := relationAnomaly_eq_dcMoment_sub_floor hψ g n m r hg0 hord hm hn hg
  have hb' : b ∈ univ.erase (0 : F) := by
    simp [Finset.mem_erase, hb]
  have hle : ‖eta ψ (powerRootSet g n) b‖ ^ (2 * r) ≤
      ∑ c ∈ univ.erase (0 : F), ‖eta ψ (powerRootSet g n) c‖ ^ (2 * r) :=
    Finset.single_le_sum
      (f := fun c : F => ‖eta ψ (powerRootSet g n) c‖ ^ (2 * r))
      (fun c _ => by positivity) hb'
  linarith

end ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge.relationAnomaly_eq_dcMoment_sub_floor
#print axioms
  ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge.signedShadowPairDiscrepancy_eq_dcMoment_sub_floor
#print axioms
  ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge.relationAnomaly_add_floor_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge.relationAnomaly_ge_neg_floor
#print axioms
  ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge.relationAnomaly_le_iff_dcMoment_le
#print axioms
  ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge.sup_pow_le_relationAnomaly_add_floor
