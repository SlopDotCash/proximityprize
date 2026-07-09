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

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The concrete finset of the first `n` powers of `g`. -/
noncomputable def powerRootSet (g : F) (n : ℕ) : Finset F :=
  (Finset.univ : Finset (Fin n)).image (fun i => g ^ (i : ℕ))

/-- Socket hypothesis: the indexed power-root representation function from R308 is the same
as the ambient `r`-fold representation function of a finset `G`.  The intended concrete
consumer is `G = {g^i | i < n}` with a no-duplicate proof for the indexing map. -/
def PowerShadowRepIdentifies (g : F) (G : Finset F) (n r : ℕ) : Prop :=
  ∀ c : F, repRF g n r c = repR G r c

/-- The power tuple associated to an indexed tuple. -/
def powerTuple (g : F) {n r : ℕ} (t : Fin r → Fin n) : Fin r → F :=
  fun i => g ^ ((t i : ℕ))

/-- Indexed power tuples land in the `piFinset` of `powerRootSet`. -/
theorem powerTuple_mem_piFinset (g : F) (n r : ℕ) (t : Fin r → Fin n) :
    powerTuple g t ∈ Fintype.piFinset (fun _ : Fin r => powerRootSet g n) := by
  classical
  rw [Fintype.mem_piFinset]
  intro i
  unfold powerTuple powerRootSet
  exact Finset.mem_image_of_mem (fun j : Fin n => g ^ (j : ℕ)) (Finset.mem_univ (t i))

/-- If the first `n` powers are indexed without duplication, every tuple in the ambient
`piFinset` has a unique indexed preimage. -/
theorem exists_unique_powerTuple_of_mem_piFinset (g : F) (n r : ℕ)
    (hinj : Function.Injective (fun i : Fin n => g ^ (i : ℕ)))
    (v : Fin r → F) (hv : v ∈ Fintype.piFinset (fun _ : Fin r => powerRootSet g n)) :
    ∃! t : Fin r → Fin n, powerTuple g t = v := by
  classical
  rw [Fintype.mem_piFinset] at hv
  choose t ht using fun i => (Finset.mem_image.mp (hv i))
  refine ⟨t, ?_, ?_⟩
  · ext i
    exact ht i
  · intro u hu
    ext i
    apply hinj
    change g ^ ((u i : ℕ)) = g ^ ((t i : ℕ))
    rw [show g ^ ((u i : ℕ)) = powerTuple g u i by rfl, hu]
    exact (ht i).symm

/-- The char-0 shadow energy at depth `r`. -/
noncomputable def shadowEnergy (n m r : ℕ) : ℕ :=
  ∑ v ∈ keysR n m r, (NR n m r v) ^ 2

/-- If the power-root representation counts identify with `repR`, the R308 char-0 floor
becomes a floor for the R240/R-subgroup `rEnergy`. -/
theorem shadowEnergy_le_rEnergy_of_repIdentifies (g : F) (G : Finset F) (n m r : ℕ)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r) :
    shadowEnergy n m r ≤ rEnergy G r := by
  classical
  calc
    shadowEnergy n m r = ∑ v ∈ keysR n m r, (NR n m r v) ^ 2 := rfl
    _ ≤ ∑ c : F, (repRF g n r c) ^ 2 :=
      shadowR_energy_le_depthR_energy g n m r hm hn hg
    _ = ∑ c : F, (repR G r c) ^ 2 := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hrep c]
    _ = rEnergy G r := (rEnergy_eq_sum_repR_sq G r).symm

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
      ∀ v ∈ keysR n m r, ∀ w ∈ keysR n m r,
        ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.evalVec g m v =
          ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.evalVec g m w → v = w)
    (hrep : PowerShadowRepIdentifies g G n r) :
    rEnergy G r = shadowEnergy n m r := by
  classical
  calc
    rEnergy G r = ∑ c : F, (repR G r c) ^ 2 :=
      rEnergy_eq_sum_repR_sq G r
    _ = ∑ c : F, (repRF g n r c) ^ 2 := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← hrep c]
    _ = ∑ v ∈ keysR n m r, (NR n m r v) ^ 2 :=
      depthR_energy_eq_of_shadow_injective g n m r hm hn hg hinj
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
      ∀ v ∈ keysR n m r, ∀ w ∈ keysR n m r,
        ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.evalVec g m v =
          ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.evalVec g m w → v = w)
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
