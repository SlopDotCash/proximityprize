/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R387SectorSupportDecomposition

/-!
# LANE B2 (#466 round 388): THE FIRST QUANTITATIVE SECTOR BOUND — sector mass ≤
  (number of realized vanishing relations) × char-0 shadow energy

r387 partitioned the collision mass into support sectors.  This brick bounds each sector by
a RELATION COUNT: the mass of any single vanishing relation `z` (its fiber of colliding
pairs) is at most the char-0 shadow energy, because pairs in the fiber are determined by
their left key and `2·NR(v)·NR(v−z) ≤ NR(v)² + NR(v−z)²`.  Hence

* **`sectorRelations`** :  the realized vanishing differences of support exactly `s`;
* **`fiberMass_le_shadowEnergy`** :  each relation's fiber mass is `≤ shadowEnergy n m r`;
* **`sectorMass_le_card_mul_shadowEnergy`** :
  `sectorMass s ≤ (sectorRelations s).card · shadowEnergy n m r`;
* **`collisionMass_le_relCount_mul_shadowEnergy`** :  summing r387's partition,
  `shadowCollisionMass ≤ (Σ_{1 ≤ s ≤ 2r} (sectorRelations s).card) · shadowEnergy`.

This is the union-bound weld: the analytic unknown (collision mass) is now bounded by a
COUNT of realized vanishing sparse relations times an exact char-0 constant — precisely the
quantity the FS annihilator/resultant ledger bounds via norm heights, per sector.  The open
wall becomes: bound the number of realized vanishing `s`-sparse relations at the prize
prime, sector by sector.  Issue #466, round 388, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The realized vanishing differences of support exactly `s`. -/
noncomputable def sectorRelations (g : F) (n m r s : ℕ) : Finset (Fin m → ℤ) :=
  ((shadowCollisionPairs g n m r).image
    (fun p => fun j => p.1 j - p.2 j)).filter (fun z => suppCard m z = s)

/-- The collision mass carried by one fixed difference `z`. -/
noncomputable def fiberMass (g : F) (n m r : ℕ) (z : Fin m → ℤ) : ℕ :=
  ∑ p ∈ (shadowCollisionPairs g n m r).filter
      (fun p => (fun j => p.1 j - p.2 j) = z),
    NR n m r p.1 * NR n m r p.2

/-- **One relation's fiber carries at most the char-0 energy.**  Pairs in the fiber are
determined by their left key, and `2ab ≤ a² + b²`. -/
theorem fiberMass_le_shadowEnergy (g : F) (n m r : ℕ) (z : Fin m → ℤ) :
    fiberMass g n m r z ≤ shadowEnergy n m r := by
  classical
  set P := (shadowCollisionPairs g n m r).filter
    (fun p => (fun j => p.1 j - p.2 j) = z) with hP
  -- both projections are injective on the fiber
  have hinj1 : Set.InjOn (fun p : (Fin m → ℤ) × (Fin m → ℤ) => p.1) ↑P := by
    intro p hp q hq h
    rw [hP, Finset.mem_coe, Finset.mem_filter] at hp hq
    have h2 : p.2 = q.2 := by
      funext j
      have hpz := congrFun hp.2 j
      have hqz := congrFun hq.2 j
      have h1j := congrFun h j
      simp only [] at hpz hqz h1j
      linarith [hpz, hqz]
    exact Prod.ext h h2
  have hinj2 : Set.InjOn (fun p : (Fin m → ℤ) × (Fin m → ℤ) => p.2) ↑P := by
    intro p hp q hq h
    rw [hP, Finset.mem_coe, Finset.mem_filter] at hp hq
    have h1 : p.1 = q.1 := by
      funext j
      have hpz := congrFun hp.2 j
      have hqz := congrFun hq.2 j
      have h2j := congrFun h j
      simp only [] at hpz hqz h2j
      linarith [hpz, hqz]
    exact Prod.ext h1 h
  -- each squared marginal is at most the shadow energy
  have hmem1 : ∀ p ∈ P, p.1 ∈ keysR n m r := by
    intro p hp
    rw [hP, Finset.mem_filter] at hp
    have := hp.1
    unfold shadowCollisionPairs at this
    rw [Finset.mem_filter, Finset.mem_offDiag] at this
    exact this.1.1
  have hmem2 : ∀ p ∈ P, p.2 ∈ keysR n m r := by
    intro p hp
    rw [hP, Finset.mem_filter] at hp
    have := hp.1
    unfold shadowCollisionPairs at this
    rw [Finset.mem_filter, Finset.mem_offDiag] at this
    exact this.1.2.1
  have hsq1 : ∑ p ∈ P, NR n m r p.1 ^ 2 ≤ shadowEnergy n m r := by
    rw [show (∑ p ∈ P, NR n m r p.1 ^ 2)
        = ∑ v ∈ P.image (fun p => p.1), NR n m r v ^ 2 from
      (Finset.sum_image (s := P)
        (g := fun p : (Fin m → ℤ) × (Fin m → ℤ) => p.1)
        (f := fun v => NR n m r v ^ 2) hinj1).symm]
    unfold shadowEnergy
    refine Finset.sum_le_sum_of_subset (fun v hv => ?_)
    rw [Finset.mem_image] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact hmem1 p hp
  have hsq2 : ∑ p ∈ P, NR n m r p.2 ^ 2 ≤ shadowEnergy n m r := by
    rw [show (∑ p ∈ P, NR n m r p.2 ^ 2)
        = ∑ v ∈ P.image (fun p => p.2), NR n m r v ^ 2 from
      (Finset.sum_image (s := P)
        (g := fun p : (Fin m → ℤ) × (Fin m → ℤ) => p.2)
        (f := fun v => NR n m r v ^ 2) hinj2).symm]
    unfold shadowEnergy
    refine Finset.sum_le_sum_of_subset (fun v hv => ?_)
    rw [Finset.mem_image] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact hmem2 p hp
  -- 2·Σ ab ≤ Σ a² + Σ b² ≤ 2·shadowEnergy
  have hAMGM : 2 * fiberMass g n m r z
      ≤ (∑ p ∈ P, NR n m r p.1 ^ 2) + (∑ p ∈ P, NR n m r p.2 ^ 2) := by
    unfold fiberMass
    rw [← hP, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p _ => ?_)
    nlinarith [sq_nonneg (NR n m r p.1 - NR n m r p.2 : ℤ),
      sq_nonneg ((NR n m r p.1 : ℤ)), sq_nonneg ((NR n m r p.2 : ℤ))]
  omega

/-- **The sector union bound**:
`sectorMass s ≤ (sectorRelations s).card · shadowEnergy`. -/
theorem sectorMass_le_card_mul_shadowEnergy (g : F) (n m r s : ℕ) :
    sectorMass g n m r s
      ≤ (sectorRelations g n m r s).card * shadowEnergy n m r := by
  classical
  set A := (shadowCollisionPairs g n m r).filter
    (fun p => suppCard m (fun j => p.1 j - p.2 j) = s) with hA
  -- partition the sector's pairs by their difference
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
  -- each fiber inside `A` is the full fiber (the support condition is implied by `z`)
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
  calc sectorMass g n m r s
      = ∑ z ∈ sectorRelations g n m r s,
          ∑ p ∈ A.filter (fun p => (fun j => p.1 j - p.2 j) = z),
            NR n m r p.1 * NR n m r p.2 := hsplit
    _ = ∑ z ∈ sectorRelations g n m r s, fiberMass g n m r z := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [hfiber z hz]
        rfl
    _ ≤ ∑ _z ∈ sectorRelations g n m r s, shadowEnergy n m r :=
        Finset.sum_le_sum (fun z _ => fiberMass_le_shadowEnergy g n m r z)
    _ = (sectorRelations g n m r s).card * shadowEnergy n m r := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **The global union bound**: summing the r387 partition,
`shadowCollisionMass ≤ (Σ_{s ≤ m} #sectorRelations s) · shadowEnergy`. -/
theorem collisionMass_le_relCount_mul_shadowEnergy (g : F) (n m r : ℕ) :
    shadowCollisionMass g n m r
      ≤ (∑ s ∈ Finset.range (m + 1), (sectorRelations g n m r s).card)
          * shadowEnergy n m r := by
  rw [collisionMass_eq_sum_sectorMass, Finset.sum_mul]
  exact Finset.sum_le_sum (fun s _ => sectorMass_le_card_mul_shadowEnergy g n m r s)

end ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound.fiberMass_le_shadowEnergy
#print axioms
  ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound.sectorMass_le_card_mul_shadowEnergy
#print axioms
  ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound.collisionMass_le_relCount_mul_shadowEnergy
