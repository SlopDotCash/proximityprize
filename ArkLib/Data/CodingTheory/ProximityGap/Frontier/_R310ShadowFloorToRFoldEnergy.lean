/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R240GeneralRFoldVariance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R308DepthUniformShadowFloor

/-!
# LANE B2 (#466 round 310): depth shadow floors as `rEnergy` floors

Round 308 isolates the exact integer-shadow floor

```text
  Σ_v NR(v)^2 ≤ Σ_c repRF(c)^2
```

for power-root tuples.  Round 240 is the main arbitrary-depth energy interface:

```text
  rEnergy G r = Σ_c repR(G,r,c)^2.
```

This file is the bridge between the two: once an arithmetic or bookkeeping lemma identifies the
power-root representation count `repRF g n r` with the ambient set representation count
`repR G r`, the char-0 shadow floor is immediately an `rEnergy` floor.  Under the stronger
shadow-injectivity hypothesis from R308, the floor upgrades to exact equality.

Issue #466, round 310, LANE B2.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy

namespace R240 := ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
namespace R306 := ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
namespace R308 := ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor

open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Socket hypothesis: the indexed power-root representation function from R308 is the same
as the ambient `r`-fold representation function of a finset `G`.  The intended concrete
consumer is `G = {g^i | i < n}` with a no-duplicate proof for the indexing map. -/
def PowerShadowRepIdentifies (g : F) (G : Finset F) (n r : ℕ) : Prop :=
  ∀ c : F, R308.repRF g n r c = R240.repR G r c

/-- The char-0 shadow energy at depth `r`. -/
noncomputable def shadowEnergy (n m r : ℕ) : ℕ :=
  ∑ v ∈ R308.keysR n m r, (R308.NR n m r v) ^ 2

/-- If the power-root representation counts identify with `repR`, the R308 char-0 floor
becomes a floor for the R240/R-subgroup `rEnergy`. -/
theorem shadowEnergy_le_rEnergy_of_repIdentifies (g : F) (G : Finset F) (n m r : ℕ)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r) :
    shadowEnergy n m r ≤ rEnergy G r := by
  classical
  calc
    shadowEnergy n m r = ∑ v ∈ R308.keysR n m r, (R308.NR n m r v) ^ 2 := rfl
    _ ≤ ∑ c : F, (R308.repRF g n r c) ^ 2 :=
      R308.shadowR_energy_le_depthR_energy g n m r hm hn hg
    _ = ∑ c : F, (R240.repR G r c) ^ 2 := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hrep c]
    _ = rEnergy G r := (R240.rEnergy_eq_sum_repR_sq G r).symm

/-- Real-valued version of `shadowEnergy_le_rEnergy_of_repIdentifies`, ready for the
DC-gap inequalities. -/
theorem shadowEnergy_le_rEnergy_real_of_repIdentifies (g : F) (G : Finset F) (n m r : ℕ)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r) :
    (shadowEnergy n m r : ℝ) ≤ (rEnergy G r : ℝ) := by
  exact_mod_cast shadowEnergy_le_rEnergy_of_repIdentifies g G n m r hm hn hg hrep

/-- Under R308 shadow injectivity and representation identification, the R240 `rEnergy` is
exactly the char-0 shadow energy. -/
theorem rEnergy_eq_shadowEnergy_of_shadow_injective_and_repIdentifies
    (g : F) (G : Finset F) (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1)
    (hinj :
      ∀ v ∈ R308.keysR n m r, ∀ w ∈ R308.keysR n m r,
        R306.evalVec g m v = R306.evalVec g m w → v = w)
    (hrep : PowerShadowRepIdentifies g G n r) :
    rEnergy G r = shadowEnergy n m r := by
  classical
  calc
    rEnergy G r = ∑ c : F, (R240.repR G r c) ^ 2 :=
      R240.rEnergy_eq_sum_repR_sq G r
    _ = ∑ c : F, (R308.repRF g n r c) ^ 2 := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← hrep c]
    _ = ∑ v ∈ R308.keysR n m r, (R308.NR n m r v) ^ 2 :=
      R308.depthR_energy_eq_of_shadow_injective g n m r hm hn hg hinj
    _ = shadowEnergy n m r := rfl

/-- The nonnegative excess of field-level energy over the char-0 shadow floor. -/
noncomputable def shadowEnergySurplus (G : Finset F) (n m r : ℕ) : ℕ :=
  rEnergy G r - shadowEnergy n m r

/-- The surplus is zero exactly when R308's shadow-injectivity equality applies and the
R308/R240 representation counts have been identified. -/
theorem shadowEnergySurplus_eq_zero_of_shadow_injective_and_repIdentifies
    (g : F) (G : Finset F) (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1)
    (hinj :
      ∀ v ∈ R308.keysR n m r, ∀ w ∈ R308.keysR n m r,
        R306.evalVec g m v = R306.evalVec g m w → v = w)
    (hrep : PowerShadowRepIdentifies g G n r) :
    shadowEnergySurplus G n m r = 0 := by
  unfold shadowEnergySurplus
  rw [rEnergy_eq_shadowEnergy_of_shadow_injective_and_repIdentifies
    g G n m r hm hn hg hinj hrep, Nat.sub_self]

end ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.shadowEnergy_le_rEnergy_of_repIdentifies
#print axioms
  ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.rEnergy_eq_shadowEnergy_of_shadow_injective_and_repIdentifies
