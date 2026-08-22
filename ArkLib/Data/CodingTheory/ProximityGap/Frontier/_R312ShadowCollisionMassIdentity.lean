/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R310ShadowFloorToRFoldEnergy

/-!
# LANE B2 (#466 round 312): exact shadow/collision decomposition of `rEnergy`

R308/R310 prove that the characteristic-`p` energy is at least its characteristic-zero
shadow, with equality under the overly strong hypothesis that the shadow evaluation map is
injective.  At prize scale collisions do occur, so injectivity is not the right endpoint.

This file gives the unconditional exact identity

```text
rEnergy(powerRootSet g n, r)
  = shadowEnergy(n,m,r) + shadowCollisionMass(g,n,m,r).
```

The second term is the weighted ordered off-diagonal mass of pairs of distinct integer
shadows that have the same value after evaluation at `g`.  Thus it is exactly the
wraparound term that the prize argument must control, with no loss and no injectivity
assumption.

Issue #466, round 312, LANE B2.  Axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The square of a finite sum is its diagonal square mass plus its ordered off-diagonal
product mass. -/
theorem sum_sq_eq_sum_sq_add_offDiag {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) ^ 2 =
      (∑ x ∈ s, (f x) ^ 2) + ∑ p ∈ s.offDiag, f p.1 * f p.2 := by
  have hsq : (∑ x ∈ s, f x) ^ 2 = ∑ p ∈ s ×ˢ s, f p.1 * f p.2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [hsq, ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag s)]
  rw [Finset.sum_diag]
  refine congrArg (fun z : ℕ => z + ∑ p ∈ s.offDiag, f p.1 * f p.2) ?_
  exact Finset.sum_congr rfl (fun x _ => (pow_two (f x)).symm)

/-- The exact weighted wraparound mass.  For each field value `c`, take all distinct
characteristic-zero shadow keys that evaluate to `c`, and weight an ordered pair `(v,w)` by
the product of its tuple multiplicities `NR(v) NR(w)`. -/
noncomputable def shadowCollisionMass (g : F) (n m r : ℕ) : ℕ :=
  ∑ c : F,
    ∑ p ∈ ((keysR n m r).filter (fun v => evalVec g m v = c)).offDiag,
      NR n m r p.1 * NR n m r p.2

/-- The indexed field energy is exactly the characteristic-zero shadow energy plus the
weighted wraparound collision mass. -/
theorem depthR_energy_eq_shadowEnergy_add_collisionMass (g : F) (n m r : ℕ)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (∑ c : F, (repRF g n r c) ^ 2) =
      shadowEnergy n m r + shadowCollisionMass g n m r := by
  classical
  have hfiber (c : F) :
      (repRF g n r c) ^ 2 =
        (∑ v ∈ (keysR n m r).filter (fun v => evalVec g m v = c),
          (NR n m r v) ^ 2) +
        ∑ p ∈ ((keysR n m r).filter (fun v => evalVec g m v = c)).offDiag,
          NR n m r p.1 * NR n m r p.2 := by
    rw [repRF_eq_sum_NR g n m r hm hn hg c]
    exact sum_sq_eq_sum_sq_add_offDiag _ _
  rw [Finset.sum_congr rfl (fun c _ => hfiber c), Finset.sum_add_distrib]
  unfold shadowEnergy shadowCollisionMass
  congr 1
  exact Finset.sum_fiberwise_of_maps_to
    (g := fun v => evalVec g m v)
    (f := fun v => (NR n m r v) ^ 2)
    (fun v _ => Finset.mem_univ (evalVec g m v))

/-- R310 representation identification transports the exact decomposition to the ambient
`rEnergy` interface. -/
theorem rEnergy_eq_shadowEnergy_add_collisionMass_of_repIdentifies
    (g : F) (G : Finset F) (n m r : ℕ)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r) :
    rEnergy G r = shadowEnergy n m r + shadowCollisionMass g n m r := by
  classical
  calc
    rEnergy G r = ∑ c : F, (repR G r c) ^ 2 := rEnergy_eq_sum_repR_sq G r
    _ = ∑ c : F, (repRF g n r c) ^ 2 := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hrep c]
    _ = shadowEnergy n m r + shadowCollisionMass g n m r :=
      depthR_energy_eq_shadowEnergy_add_collisionMass g n m r hm hn hg

/-- Exact-order concrete form for the first `n` powers of `g`.  This is the unconditional
replacement for R310's injectivity-conditional equality. -/
theorem rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    rEnergy (powerRootSet g n) r =
      shadowEnergy n m r + shadowCollisionMass g n m r :=
  rEnergy_eq_shadowEnergy_add_collisionMass_of_repIdentifies
    g (powerRootSet g n) n m r hm hn hg
    (powerShadowRepIdentifies_powerRootSet_of_orderOf g n r hg0 hord)

/-- On an exact-order power-root set, the newly isolated collision mass is literally the
energy surplus over the characteristic-zero shadow. -/
theorem shadowCollisionMass_eq_rEnergy_sub_shadowEnergy_of_orderOf
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    shadowCollisionMass g n m r =
      rEnergy (powerRootSet g n) r - shadowEnergy n m r := by
  rw [rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g n m r hg0 hord hm hn hg, Nat.add_sub_cancel_left]

/-- **Exact reduction of an energy headroom target.**  Bounding the full power-root energy
by the shadow plus `B` is equivalent, with no loss, to bounding the weighted wraparound
collision mass by `B`. -/
theorem rEnergy_le_shadowEnergy_add_iff_collisionMass_le_of_orderOf
    (g : F) (n m r B : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    rEnergy (powerRootSet g n) r ≤ shadowEnergy n m r + B ↔
      shadowCollisionMass g n m r ≤ B := by
  rw [rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g n m r hg0 hord hm hn hg]
  omega

/-- The collision mass vanishes under shadow injectivity, recovering the earlier equality
as a special case of the exact decomposition. -/
theorem shadowCollisionMass_eq_zero_of_shadow_injective (g : F) (n m r : ℕ)
    (hinj : ∀ v ∈ keysR n m r, ∀ w ∈ keysR n m r,
      evalVec g m v = evalVec g m w → v = w) :
    shadowCollisionMass g n m r = 0 := by
  classical
  unfold shadowCollisionMass
  apply Finset.sum_eq_zero
  intro c _
  apply Finset.sum_eq_zero
  rintro ⟨v, w⟩ hp
  have hvf := (Finset.mem_offDiag.mp hp).1
  have hwf := (Finset.mem_offDiag.mp hp).2.1
  have hvw := (Finset.mem_offDiag.mp hp).2.2
  rw [Finset.mem_filter] at hvf hwf
  obtain ⟨hv, hvc⟩ := hvf
  obtain ⟨hw, hwc⟩ := hwf
  exact absurd (hinj v hv w hw (hvc.trans hwc.symm)) hvw

end ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity.sum_sq_eq_sum_sq_add_offDiag
#print axioms
  ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity.depthR_energy_eq_shadowEnergy_add_collisionMass
#print axioms
  ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity.rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
#print axioms
  ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity.rEnergy_le_shadowEnergy_add_iff_collisionMass_le_of_orderOf
#print axioms
  ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity.shadowCollisionMass_eq_zero_of_shadow_injective
