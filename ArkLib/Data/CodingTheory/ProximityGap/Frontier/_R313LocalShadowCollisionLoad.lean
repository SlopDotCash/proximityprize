/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R312ShadowCollisionMassIdentity

/-!
# LANE B2 (#466 round 313): local shadow-collision load

R312 identifies the exact finite-field energy surplus as a weighted off-diagonal collision
mass.  This file localizes that mass at one characteristic-zero shadow key.

For a key `v`, its local load is the total `NR`-weight of distinct keys colliding with `v`.
The global collision mass is exactly

```text
  sum_v NR(v) * localLoad(v).
```

Since `sum_v NR(v) = n^r`, a uniform local bound `localLoad(v) <= K` immediately gives

```text
  shadowCollisionMass <= n^r * K.
```

This is a lossless reduction of the prize arithmetic to a per-relation neighborhood bound.
Issue #466, round 313, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Ordered pairs of distinct shadow keys that collide after evaluation at `g`. -/
noncomputable def shadowCollisionPairs (g : F) (n m r : ℕ) :
    Finset ((Fin m → ℤ) × (Fin m → ℤ)) :=
  (keysR n m r).offDiag.filter
    (fun p => evalVec g m p.1 = evalVec g m p.2)

/-- The exact `NR`-weighted collision load attached to the left endpoint `v`. -/
noncomputable def localShadowCollisionLoad (g : F) (n m r : ℕ)
    (v : Fin m → ℤ) : ℕ :=
  ∑ p ∈ (shadowCollisionPairs g n m r).filter (fun p => p.1 = v),
    NR n m r p.2

/-- The fiberwise definition of R312's collision mass equals one global sum over ordered
colliding shadow pairs. -/
theorem shadowCollisionMass_eq_sum_pairs (g : F) (n m r : ℕ) :
    shadowCollisionMass g n m r =
      ∑ p ∈ shadowCollisionPairs g n m r,
        NR n m r p.1 * NR n m r p.2 := by
  classical
  unfold shadowCollisionMass shadowCollisionPairs
  let S := keysR n m r
  let P := S.offDiag.filter (fun p => evalVec g m p.1 = evalVec g m p.2)
  have hmaps : ∀ p ∈ P, evalVec g m p.1 ∈ (Finset.univ : Finset F) :=
    fun p _ => Finset.mem_univ _
  calc
    (∑ c : F,
      ∑ p ∈ ((keysR n m r).filter (fun v => evalVec g m v = c)).offDiag,
        NR n m r p.1 * NR n m r p.2)
        = ∑ c : F, ∑ p ∈ P.filter (fun p => evalVec g m p.1 = c),
            NR n m r p.1 * NR n m r p.2 := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          congr 1
          ext p
          simp only [S, P, Finset.mem_filter, Finset.mem_offDiag]
          constructor
          · rintro ⟨⟨hp1, hp1c⟩, ⟨hp2, hp2c⟩, hne⟩
            exact ⟨⟨⟨hp1, hp2, hne⟩, hp1c.trans hp2c.symm⟩, hp1c⟩
          · rintro ⟨⟨⟨hp1, hp2, hne⟩, heq⟩, hp1c⟩
            exact ⟨⟨hp1, hp1c⟩, ⟨hp2, heq ▸ hp1c⟩, hne⟩
    _ = ∑ p ∈ P, NR n m r p.1 * NR n m r p.2 :=
      (Finset.sum_fiberwise_of_maps_to
        (g := fun p : (Fin m → ℤ) × (Fin m → ℤ) => evalVec g m p.1)
        (f := fun p : (Fin m → ℤ) × (Fin m → ℤ) =>
          NR n m r p.1 * NR n m r p.2) hmaps)
    _ = ∑ p ∈ (keysR n m r).offDiag.filter
          (fun p => evalVec g m p.1 = evalVec g m p.2),
          NR n m r p.1 * NR n m r p.2 := rfl

/-- The shadow histogram conserves all indexed tuples: its total mass is `n^r`. -/
theorem sum_NR_keysR (n m r : ℕ) :
    ∑ v ∈ keysR n m r, NR n m r v = n ^ r := by
  classical
  unfold keysR NR
  rw [← Finset.card_eq_sum_card_image (tupleVec n m r)
    (Finset.univ : Finset (Fin r → Fin n))]
  simp

/-- Exact localization: global collision mass is the `NR`-weighted sum of local loads. -/
theorem shadowCollisionMass_eq_sum_local_load (g : F) (n m r : ℕ) :
    shadowCollisionMass g n m r =
      ∑ v ∈ keysR n m r, NR n m r v * localShadowCollisionLoad g n m r v := by
  classical
  rw [shadowCollisionMass_eq_sum_pairs]
  unfold localShadowCollisionLoad
  let P := shadowCollisionPairs g n m r
  have hmaps : ∀ p ∈ P, p.1 ∈ keysR n m r := by
    intro p hp
    exact (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).1
  calc
    (∑ p ∈ shadowCollisionPairs g n m r, NR n m r p.1 * NR n m r p.2)
        = ∑ v ∈ keysR n m r,
            ∑ p ∈ P.filter (fun p => p.1 = v),
              NR n m r p.1 * NR n m r p.2 :=
          Finset.sum_fiberwise_of_maps_to
            (g := fun p : (Fin m → ℤ) × (Fin m → ℤ) => p.1)
            (f := fun p : (Fin m → ℤ) × (Fin m → ℤ) =>
              NR n m r p.1 * NR n m r p.2) hmaps |>.symm
    _ = ∑ v ∈ keysR n m r,
          NR n m r v * ∑ p ∈ P.filter (fun p => p.1 = v), NR n m r p.2 := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [Finset.mem_filter] at hp
          rw [hp.2]
    _ = ∑ v ∈ keysR n m r,
          NR n m r v *
            ∑ p ∈ (shadowCollisionPairs g n m r).filter (fun p => p.1 = v),
              NR n m r p.2 := rfl

/-- **LOCAL-TO-GLOBAL COLLISION BOUND.**  If every shadow key has weighted collision
neighborhood at most `K`, then the entire finite-field energy surplus is at most `n^r K`. -/
theorem shadowCollisionMass_le_pow_mul_of_local_load_le
    (g : F) (n m r K : ℕ)
    (hlocal : ∀ v ∈ keysR n m r, localShadowCollisionLoad g n m r v ≤ K) :
    shadowCollisionMass g n m r ≤ n ^ r * K := by
  rw [shadowCollisionMass_eq_sum_local_load]
  calc
    (∑ v ∈ keysR n m r, NR n m r v * localShadowCollisionLoad g n m r v)
        ≤ ∑ v ∈ keysR n m r, NR n m r v * K := by
          exact Finset.sum_le_sum (fun v hv => Nat.mul_le_mul_left _ (hlocal v hv))
    _ = (∑ v ∈ keysR n m r, NR n m r v) * K := by rw [Finset.sum_mul]
    _ = n ^ r * K := by rw [sum_NR_keysR]

/-- Exact-order power-root consumer: a uniform local collision-load bound supplies the full
energy estimate with explicit additive headroom `n^r K`. -/
theorem rEnergy_powerRootSet_le_shadowEnergy_add_pow_mul_of_local_load_le
    (g : F) (n m r K : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hlocal : ∀ v ∈ keysR n m r, localShadowCollisionLoad g n m r v ≤ K) :
    rEnergy (powerRootSet g n) r ≤ shadowEnergy n m r + n ^ r * K := by
  rw [rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g n m r hg0 hord hm hn hg]
  exact Nat.add_le_add_left
    (shadowCollisionMass_le_pow_mul_of_local_load_le g n m r K hlocal) _

end ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad.shadowCollisionMass_eq_sum_pairs
#print axioms ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad.sum_NR_keysR
#print axioms
  ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad.shadowCollisionMass_eq_sum_local_load
#print axioms
  ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad.shadowCollisionMass_le_pow_mul_of_local_load_le
#print axioms
  ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad.rEnergy_powerRootSet_le_shadowEnergy_add_pow_mul_of_local_load_le
