/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R388SectorRelationCountBound

/-!
# LANE B2 (#466 round 389): THE CENSUS IDENTITY, MACHINE-CHECKED — collision mass equals
  the sum of char-0 class masses over the vanishing relations

The r305 census computed `excess(p) = Σ_{z ≠ 0, z(g) ≡ 0 (p)} M(z)` numerically and
verified it bit-exact against every scan.  This brick proves the identity in Lean:

* **`classMass`** :  the PRIME-INDEPENDENT char-0 pair mass of a difference class
  `z` — `Σ_{v : v ∈ keys, v − z ∈ keys} NR(v) · NR(v − z)`;
* **`evalVec_sub`** :  the shadow evaluation is additive in the vector;
* **`fiberMass_eq_classMass`** :  for a VANISHING relation (`evalVec g m z = 0`, `z ≠ 0`),
  the collision fiber is the FULL difference class — every realized pair `(v, v−z)`
  collides, and conversely — so `fiberMass z = classMass z` EXACTLY;
* **`sectorMass_eq_sum_classMass`** :  hence each r387 sector mass equals the sum of the
  char-0 class masses of its vanishing relations — the sharp (loss-free) form of the r388
  union bound.

Consequence: the r331 wall scalar `S` (the collision mass) is now IDENTIFIED, not merely
bounded: `S = Σ_{z realized, z(g) ≡ 0} M(z)`, where every `M(z)` is an exactly computable
char-0 constant and the only prime-dependence is WHICH sparse relations vanish — the
divisibility condition `p ∣ Norm(z)` of the FS ledger.  This is the census formula as a
theorem, at every depth `r`, over every finite field.  Issue #466, round 389, LANE B2.
Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition
open ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **prime-independent char-0 class mass** of a difference `z`: the total
`NR`-weighted number of ordered realized pairs at difference exactly `z`. -/
noncomputable def classMass (n m r : ℕ) (z : Fin m → ℤ) : ℕ :=
  ∑ v ∈ (keysR n m r).filter (fun v => (fun j => v j - z j) ∈ keysR n m r),
    NR n m r v * NR n m r (fun j => v j - z j)

/-- The shadow evaluation is additive in the vector argument. -/
theorem evalVec_sub (g : F) (m : ℕ) (v w : Fin m → ℤ) :
    evalVec g m (fun j => v j - w j) = evalVec g m v - evalVec g m w := by
  unfold evalVec
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  rw [sub_smul]

/-- **The exact fiber law**: for a vanishing nonzero relation `z`, the collision fiber at
difference `z` is the full realized difference class, so its mass is the char-0 class
mass. -/
theorem fiberMass_eq_classMass (g : F) (n m r : ℕ) (z : Fin m → ℤ)
    (hz : evalVec g m z = 0) (hz0 : z ≠ 0) :
    fiberMass g n m r z = classMass n m r z := by
  classical
  unfold fiberMass classMass
  refine Finset.sum_nbij'
    (i := fun p => p.1)
    (j := fun v => (v, fun j => v j - z j)) ?_ ?_ ?_ ?_ ?_
  -- forward membership: a fiber pair's left key is a realized class representative
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpair, hdz⟩ := hp
    unfold shadowCollisionPairs at hpair
    rw [Finset.mem_filter, Finset.mem_offDiag] at hpair
    rw [Finset.mem_filter]
    refine ⟨hpair.1.1, ?_⟩
    have : (fun j => p.1 j - z j) = p.2 := by
      funext j
      have hj : p.1 j - p.2 j = z j := congrFun hdz j
      linarith
    rw [this]
    exact hpair.1.2.1
  -- backward membership: a realized class representative gives a colliding pair
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_filter]
    constructor
    · unfold shadowCollisionPairs
      rw [Finset.mem_filter, Finset.mem_offDiag]
      refine ⟨⟨hv.1, hv.2, ?_⟩, ?_⟩
      · -- v ≠ v − z since z ≠ 0
        intro h
        apply hz0
        funext j
        show z j = 0
        have hj : v j = v j - z j := congrFun h j
        linarith
      · -- the evaluations collide because z vanishes
        have := evalVec_sub g m v (fun j => v j - (v j - z j))
        have hzz : (fun j => v j - (v j - z j)) = z := by
          funext j
          ring
        calc evalVec g m v
            = evalVec g m v - evalVec g m z := by rw [hz, sub_zero]
          _ = evalVec g m v
              - (evalVec g m v - evalVec g m (fun j => v j - z j)) := by
              rw [← evalVec_sub g m v (fun j => v j - z j)]
              congr 1
              rw [show (fun j => v j - (v j - z j)) = z from by funext j; ring]
          _ = evalVec g m (fun j => v j - z j) := by ring
    · funext j
      simp only []
      ring
  -- left inverse
  · intro p hp
    rw [Finset.mem_filter] at hp
    have : (fun j => p.1 j - z j) = p.2 := by
      funext j
      have hj : p.1 j - p.2 j = z j := congrFun hp.2 j
      linarith
    exact Prod.ext rfl this
  -- right inverse
  · intro v _
    rfl
  -- weights agree
  · intro p hp
    rw [Finset.mem_filter] at hp
    have : (fun j => p.1 j - z j) = p.2 := by
      funext j
      have hj : p.1 j - p.2 j = z j := congrFun hp.2 j
      linarith
    rw [this]

/-- Every relation in a sector vanishes and is nonzero (extracted from r387/r313
membership). -/
theorem sectorRelations_vanishing (g : F) (n m r s : ℕ) (z : Fin m → ℤ)
    (hz : z ∈ sectorRelations g n m r s) :
    evalVec g m z = 0 ∧ z ≠ 0 := by
  classical
  unfold sectorRelations at hz
  rw [Finset.mem_filter, Finset.mem_image] at hz
  obtain ⟨⟨p, hp, rfl⟩, _⟩ := hz
  unfold shadowCollisionPairs at hp
  rw [Finset.mem_filter, Finset.mem_offDiag] at hp
  constructor
  · rw [evalVec_sub, hp.2, sub_self]
  · intro h
    apply hp.1.2.2
    funext j
    have hj : p.1 j - p.2 j = 0 := by
      have := congrFun h j
      simpa using this
    linarith

/-- **The census identity, per sector**: each sector's mass is EXACTLY the sum of the
char-0 class masses of its vanishing relations. -/
theorem sectorMass_eq_sum_classMass (g : F) (n m r s : ℕ) :
    sectorMass g n m r s
      = ∑ z ∈ sectorRelations g n m r s, classMass n m r z := by
  classical
  set A := (shadowCollisionPairs g n m r).filter
    (fun p => suppCard m (fun j => p.1 j - p.2 j) = s) with hA
  have hmaps : ∀ p ∈ A, (fun j => p.1 j - p.2 j) ∈ sectorRelations g n m r s := by
    intro p hp
    rw [hA, Finset.mem_filter] at hp
    unfold sectorRelations
    rw [Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨p, hp.1, rfl⟩, hp.2⟩
  have hsplit : sectorMass g n m r s
      = ∑ z ∈ sectorRelations g n m r s,
          ∑ p ∈ A.filter (fun p => (fun j => p.1 j - p.2 j) = z),
            NR n m r p.1 * NR n m r p.2 :=
    (Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => NR n m r p.1 * NR n m r p.2)).symm
  have hfiber : ∀ z ∈ sectorRelations g n m r s,
      A.filter (fun p => (fun j => p.1 j - p.2 j) = z)
        = (shadowCollisionPairs g n m r).filter
            (fun p => (fun j => p.1 j - p.2 j) = z) := by
    intro z hz
    unfold sectorRelations at hz
    rw [Finset.mem_filter] at hz
    ext p
    rw [hA, Finset.filter_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hp, _, hdz⟩
      exact ⟨hp, hdz⟩
    · rintro ⟨hp, hdz⟩
      refine ⟨hp, ?_, hdz⟩
      rw [hdz]
      exact hz.2
  rw [hsplit]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [hfiber z hz]
  have hvan := sectorRelations_vanishing g n m r s z hz
  exact fiberMass_eq_classMass g n m r z hvan.1 hvan.2

/-- **The census identity, global**: the collision mass (the r331 wall scalar) is the sum
of prime-independent char-0 class masses over the vanishing relations, summed over
sectors. -/
theorem collisionMass_eq_sum_sum_classMass (g : F) (n m r : ℕ) :
    shadowCollisionMass g n m r
      = ∑ s ∈ Finset.range (m + 1),
          ∑ z ∈ sectorRelations g n m r s, classMass n m r z := by
  rw [collisionMass_eq_sum_sectorMass]
  exact Finset.sum_congr rfl (fun s _ => sectorMass_eq_sum_classMass g n m r s)

end ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber.evalVec_sub
#print axioms ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber.fiberMass_eq_classMass
#print axioms
  ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber.sectorMass_eq_sum_classMass
#print axioms
  ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber.collisionMass_eq_sum_sum_classMass
