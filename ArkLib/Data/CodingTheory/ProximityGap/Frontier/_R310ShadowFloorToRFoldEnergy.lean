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

/-- Powers below the multiplicative order of a nonzero field element are distinct. -/
theorem pow_inj_below_order {g : F} (hg0 : g ≠ 0) {N : ℕ} (hN : orderOf g = N) :
    ∀ i, i < N → ∀ j, j < N → g ^ i = g ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → g ^ i = g ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : g ^ i * g ^ (j - i) = g ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : g ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i hg0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-- If `g` has exact order `n`, the first `n` powers are injectively indexed by `Fin n`. -/
theorem power_index_injective_of_orderOf (g : F) (n : ℕ) (hg0 : g ≠ 0)
    (hord : orderOf g = n) :
    Function.Injective (fun i : Fin n => (g ^ (i : ℕ) : F)) := by
  intro i j hij
  ext
  exact pow_inj_below_order hg0 hord i i.isLt j j.isLt hij

/-- The concrete finset of the first `n` powers of `g`. -/
noncomputable def powerRootSet (g : F) (n : ℕ) : Finset F :=
  (Finset.univ : Finset (Fin n)).image (fun i : Fin n => (g ^ (i : ℕ) : F))

/-- Socket hypothesis: the indexed power-root representation function from R308 is the same
as the ambient `r`-fold representation function of a finset `G`.  The intended concrete
consumer is `G = {g^i | i < n}` with a no-duplicate proof for the indexing map. -/
def PowerShadowRepIdentifies (g : F) (G : Finset F) (n r : ℕ) : Prop :=
  ∀ c : F, repRF g n r c = repR G r c

/-- The power tuple associated to an indexed tuple. -/
def powerTuple (g : F) {n r : ℕ} (t : Fin r → Fin n) : Fin r → F :=
  fun i => (g ^ ((t i : ℕ)) : F)

/-- Indexed power tuples land in the `piFinset` of `powerRootSet`. -/
theorem powerTuple_mem_piFinset (g : F) (n r : ℕ) (t : Fin r → Fin n) :
    powerTuple g t ∈ Fintype.piFinset (fun _ : Fin r => powerRootSet g n) := by
  classical
  rw [Fintype.mem_piFinset]
  intro i
  unfold powerTuple powerRootSet
  exact Finset.mem_image_of_mem (fun j : Fin n => (g ^ (j : ℕ) : F))
    (Finset.mem_univ (t i))

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
    exact (ht i).2
  · intro u hu
    ext i
    have hfin : u i = t i := by
      apply hinj
      calc
        (g ^ ((u i : ℕ)) : F) = powerTuple g u i := rfl
        _ = v i := congrFun hu i
        _ = (g ^ ((t i : ℕ)) : F) := (ht i).2.symm
    exact congrArg (fun x : Fin n => (x : ℕ)) hfin

/-- `repR` as the cardinality of the fiber of the `r`-fold sum map. -/
theorem repR_eq_filter_card (G : Finset F) (r : ℕ) (c : F) :
    repR G r c =
      ((Fintype.piFinset (fun _ : Fin r => G)).filter (fun v => ∑ i, v i = c)).card := by
  classical
  unfold repR
  rw [Finset.card_filter]

/-- Concrete bookkeeping bridge: if the first `n` powers of `g` are indexed without
duplication, then the R308 indexed representation count is exactly R240's ambient `repR`
for the concrete power-root set. -/
theorem repRF_eq_repR_powerRootSet (g : F) (n r : ℕ)
    (hinj : Function.Injective (fun i : Fin n => (g ^ (i : ℕ) : F))) (c : F) :
    repRF g n r c = repR (powerRootSet g n) r c := by
  classical
  rw [repR_eq_filter_card]
  unfold repRF
  refine Finset.card_bij
    (i := fun t _ => powerTuple g t) ?mem ?inj ?surj
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨powerTuple_mem_piFinset g n r t, ?_⟩
    simpa [gsumR, powerTuple] using ht.2
  · intro t₁ ht₁ t₂ ht₂ hpow
    ext i
    have hfin : t₁ i = t₂ i := by
      apply hinj
      exact congrFun hpow i
    exact congrArg (fun x : Fin n => (x : ℕ)) hfin
  · intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨t, ht, _huniq⟩ := exists_unique_powerTuple_of_mem_piFinset g n r hinj v hv.1
    refine ⟨t, ?_, ht⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ t, ?_⟩
    have hsum : (∑ i, powerTuple g t i) = c := by
      rw [ht]
      exact hv.2
    simpa [gsumR, powerTuple] using hsum

/-- The concrete power-root set satisfies the R310 representation-identification socket when
the first `n` powers are indexed injectively. -/
theorem powerShadowRepIdentifies_powerRootSet (g : F) (n r : ℕ)
    (hinj : Function.Injective (fun i : Fin n => (g ^ (i : ℕ) : F))) :
    PowerShadowRepIdentifies g (powerRootSet g n) n r :=
  fun c => repRF_eq_repR_powerRootSet g n r hinj c

/-- Exact-order version of `powerShadowRepIdentifies_powerRootSet`. -/
theorem powerShadowRepIdentifies_powerRootSet_of_orderOf (g : F) (n r : ℕ) (hg0 : g ≠ 0)
    (hord : orderOf g = n) :
    PowerShadowRepIdentifies g (powerRootSet g n) n r :=
  powerShadowRepIdentifies_powerRootSet g n r
    (power_index_injective_of_orderOf g n hg0 hord)

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

/-- Exact-order concrete form: the char-0 shadow floor is an `rEnergy` floor for the
power-root set `{g^i | i < n}`. -/
theorem shadowEnergy_le_rEnergy_powerRootSet_of_orderOf (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) :
    shadowEnergy n m r ≤ rEnergy (powerRootSet g n) r :=
  shadowEnergy_le_rEnergy_of_repIdentifies g (powerRootSet g n) n m r hm hn hg
    (powerShadowRepIdentifies_powerRootSet_of_orderOf g n r hg0 hord)

/-- Real-valued exact-order concrete form of the R308 shadow floor. -/
theorem shadowEnergy_le_rEnergy_real_powerRootSet_of_orderOf (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) :
    (shadowEnergy n m r : ℝ) ≤ (rEnergy (powerRootSet g n) r : ℝ) := by
  exact_mod_cast shadowEnergy_le_rEnergy_powerRootSet_of_orderOf g n m r hg0 hord hm hn hg

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

/-- Exact-order concrete equality form: if the R308 shadow map is injective, then the R240
`rEnergy` of the concrete power-root set is exactly the char-0 shadow energy. -/
theorem rEnergy_powerRootSet_eq_shadowEnergy_of_orderOf_and_shadow_injective
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hinj :
      ∀ v ∈ keysR n m r, ∀ w ∈ keysR n m r,
        ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.evalVec g m v =
          ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.evalVec g m w → v = w) :
    rEnergy (powerRootSet g n) r = shadowEnergy n m r :=
  rEnergy_eq_shadowEnergy_of_shadow_injective_and_repIdentifies
    g (powerRootSet g n) n m r hm hn hg hinj
    (powerShadowRepIdentifies_powerRootSet_of_orderOf g n r hg0 hord)

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
  ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.repRF_eq_repR_powerRootSet
#print axioms
  ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.power_index_injective_of_orderOf
#print axioms
  ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.shadowEnergy_le_rEnergy_powerRootSet_of_orderOf
#print axioms
  ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.rEnergy_eq_shadowEnergy_of_shadow_injective_and_repIdentifies
#print axioms
  ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.rEnergy_powerRootSet_eq_shadowEnergy_of_orderOf_and_shadow_injective
