/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R313LocalShadowCollisionLoad

/-!
# LANE B2 (#466 round 387): SECTOR DECOMPOSITION OF THE COLLISION MASS BY DIFFERENCE
  SUPPORT — the Lean footing for the per-sector control program

The r370b probe found empirically that the depth-3 excess decomposes into SECTORS by the
support signature of the vanishing relation (s3 = subgroup-on-line, s4 = depth-2 shifted
subgroup intersections, s5/s6 = genuine depth-3 Sidon strata), and that "the wall is their
SIMULTANEOUS control".  This brick makes the decomposition a theorem:

* **`sectorMass`** :  the `NR`-weighted collision mass carried by ordered colliding pairs
  whose shadow difference has support size exactly `s`;
* **`collisionMass_eq_sum_sectorMass`** :  `shadowCollisionMass = Σ_{s ≤ m} sectorMass s`
  (exact partition — no loss, no overlap);
* **`sectorMass_zero_eq_zero`** :  the `s = 0` sector is empty (colliding pairs are
  distinct keys, so the difference is nonzero);
* **`suppCard_le_of_mem_keysR`** / **`suppCard_sub_le_two_mul`** :  realized keys have
  support `≤ r`, so every realized difference has support `≤ 2r`; hence
* **`sectorMass_eq_zero_of_gt`** :  only sectors `1 ≤ s ≤ min m (2r)` carry mass.

Consequence: any per-sector bounds `sectorMass s ≤ B_s` sum to a collision-mass bound
feeding the r331 weld directly — each sector can now be attacked with ITS OWN literature
(the depth-2-type sectors by the unconditional Stepanov `r = 2` rung, the Sidon strata by
their own counting).  Does not bound any sector by itself.  Issue #466, round 387,
LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Support size of an integer vector. -/
def suppCard (m : ℕ) (z : Fin m → ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun j => z j ≠ 0)).card

theorem suppCard_le (m : ℕ) (z : Fin m → ℤ) : suppCard m z ≤ m := by
  unfold suppCard
  calc ((Finset.univ : Finset (Fin m)).filter (fun j => z j ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

/-- The collision mass carried by colliding pairs whose shadow difference has support
size exactly `s`. -/
noncomputable def sectorMass (g : F) (n m r s : ℕ) : ℕ :=
  ∑ p ∈ (shadowCollisionPairs g n m r).filter
      (fun p => suppCard m (fun j => p.1 j - p.2 j) = s),
    NR n m r p.1 * NR n m r p.2

/-- **The exact sector partition**: the total collision mass is the sum of the sector
masses over all support sizes `s ≤ m`. -/
theorem collisionMass_eq_sum_sectorMass (g : F) (n m r : ℕ) :
    shadowCollisionMass g n m r
      = ∑ s ∈ Finset.range (m + 1), sectorMass g n m r s := by
  classical
  rw [shadowCollisionMass_eq_sum_pairs]
  unfold sectorMass
  exact (Finset.sum_fiberwise_of_maps_to
    (g := fun p : (Fin m → ℤ) × (Fin m → ℤ) => suppCard m (fun j => p.1 j - p.2 j))
    (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (suppCard_le m _)))
    (fun p => NR n m r p.1 * NR n m r p.2)).symm

/-- **The zero sector is empty**: colliding pairs are distinct keys, so the difference
is a nonzero vector and its support is nonempty. -/
theorem sectorMass_zero_eq_zero (g : F) (n m r : ℕ) :
    sectorMass g n m r 0 = 0 := by
  classical
  unfold sectorMass
  refine Finset.sum_eq_zero (fun p hp => ?_)
  exfalso
  rw [Finset.mem_filter] at hp
  obtain ⟨hpair, hsupp⟩ := hp
  unfold shadowCollisionPairs at hpair
  rw [Finset.mem_filter, Finset.mem_offDiag] at hpair
  have hne : p.1 ≠ p.2 := hpair.1.2.2
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hjmem : j ∈ ((Finset.univ : Finset (Fin m)).filter
      (fun j => p.1 j - p.2 j ≠ 0)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_ne_zero.mpr hj⟩
  have hpos : 0 < suppCard m (fun j => p.1 j - p.2 j) :=
    Finset.card_pos.mpr ⟨j, hjmem⟩
  omega

/-- Realized keys have support at most `r`: a key is the shadow of an `r`-tuple, a sum of
`r` signed unit vectors. -/
theorem suppCard_le_of_mem_keysR (n m r : ℕ) (v : Fin m → ℤ)
    (hv : v ∈ keysR n m r) : suppCard m v ≤ r := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    unfold suppCard
    simp
  unfold keysR at hv
  rw [Finset.mem_image] at hv
  obtain ⟨t, _, rfl⟩ := hv
  have hsub : ((Finset.univ : Finset (Fin m)).filter (fun j => tupleVec n m r t j ≠ 0))
      ⊆ (Finset.univ : Finset (Fin r)).image
          (fun i => (⟨(t i : ℕ) % m, Nat.mod_lt _ hm⟩ : Fin m)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_image]
    by_contra hnot
    apply hj.2
    unfold tupleVec
    refine Finset.sum_eq_zero (fun i _ => ?_)
    unfold vecOf
    have hne : (⟨(t i : ℕ) % m, Nat.mod_lt _ hm⟩ : Fin m) ≠ j := by
      intro h
      exact hnot ⟨i, Finset.mem_univ i, h⟩
    have hjne : (t i : ℕ) % m ≠ (j : ℕ) := by
      intro h
      exact hne (Fin.ext h)
    have hjm := j.isLt
    have h1 : ¬ ((t i : ℕ) = (j : ℕ)) := by
      intro h
      exact hjne (by rw [h]; exact Nat.mod_eq_of_lt hjm)
    have h2 : ¬ ((t i : ℕ) = (j : ℕ) + m) := by
      intro h
      exact hjne (by rw [h, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hjm)
    simp [h1, h2]
  calc suppCard m (tupleVec n m r t)
      ≤ ((Finset.univ : Finset (Fin r)).image
          (fun i => (⟨(t i : ℕ) % m, Nat.mod_lt _ hm⟩ : Fin m))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
    _ = r := by simp

/-- **Every realized difference has support at most `2r`.** -/
theorem suppCard_sub_le_two_mul (n m r : ℕ) (v w : Fin m → ℤ)
    (hv : v ∈ keysR n m r) (hw : w ∈ keysR n m r) :
    suppCard m (fun j => v j - w j) ≤ 2 * r := by
  classical
  have hsub : ((Finset.univ : Finset (Fin m)).filter (fun j => v j - w j ≠ 0))
      ⊆ ((Finset.univ : Finset (Fin m)).filter (fun j => v j ≠ 0))
        ∪ ((Finset.univ : Finset (Fin m)).filter (fun j => w j ≠ 0)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h1 : v j = 0
    · refine Or.inr ⟨Finset.mem_univ _, ?_⟩
      intro h2
      apply hj.2
      rw [h1, h2]
      ring
    · exact Or.inl ⟨Finset.mem_univ _, h1⟩
  calc suppCard m (fun j => v j - w j)
      ≤ (((Finset.univ : Finset (Fin m)).filter (fun j => v j ≠ 0))
          ∪ ((Finset.univ : Finset (Fin m)).filter (fun j => w j ≠ 0))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin m)).filter (fun j => v j ≠ 0)).card
          + ((Finset.univ : Finset (Fin m)).filter (fun j => w j ≠ 0)).card :=
        Finset.card_union_le _ _
    _ ≤ r + r := Nat.add_le_add (suppCard_le_of_mem_keysR n m r v hv)
        (suppCard_le_of_mem_keysR n m r w hw)
    _ = 2 * r := by ring

/-- **The truncated partition**: sectors above `2r` are empty. -/
theorem sectorMass_eq_zero_of_gt (g : F) (n m r s : ℕ) (hs : 2 * r < s) :
    sectorMass g n m r s = 0 := by
  classical
  unfold sectorMass
  refine Finset.sum_eq_zero (fun p hp => ?_)
  exfalso
  rw [Finset.mem_filter] at hp
  obtain ⟨hpair, hsupp⟩ := hp
  unfold shadowCollisionPairs at hpair
  rw [Finset.mem_filter, Finset.mem_offDiag] at hpair
  have := suppCard_sub_le_two_mul n m r p.1 p.2 hpair.1.1 hpair.1.2.1
  omega

end ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition.collisionMass_eq_sum_sectorMass
#print axioms
  ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition.sectorMass_zero_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition.suppCard_sub_le_two_mul
#print axioms
  ArkLib.ProximityGap.Frontier.R387SectorSupportDecomposition.sectorMass_eq_zero_of_gt
