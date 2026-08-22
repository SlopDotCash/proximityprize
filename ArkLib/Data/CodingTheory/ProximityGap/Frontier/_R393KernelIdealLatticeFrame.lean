/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R392RelationCountCapstone

/-!
# LANE B2 (#466 round 393): THE KERNEL-LATTICE FRAME — realized relations are short
  vectors of the evaluation kernel; `K = 0` is an ℓ∞-SVP-type statement

The r392 open Prop counts realized vanishing relations.  This brick pins their ambient
structure:

* **`evalVecHom`** :  the shadow evaluation as an additive group homomorphism
  `(Fin m → ℤ) →+ F` — so its kernel is an additive subgroup (the "ideal lattice"
  `⟨X − g, p⟩ / (X^m + 1)` of lattice cryptography, in coordinates);
* **`sectorRelations_mem_ker`** :  every realized relation lies in the kernel;
* **`sectorRelations_linf_le`** :  and has `ℓ∞ ≤ 2r` (from r391's entry bounds);
* **`relationCount_zero_of_no_short_kernel`** :  if the kernel contains NO nonzero vector
  of `ℓ∞ ≤ 2r` — an ℓ∞ shortest-vector lower bound for the evaluation lattice — then
  `RealizedRelationCountBound g n m r 0` holds, and (via r392) the depth-`r` moment control
  is the unconditional char-0 constant.

This identifies the arc's open Prop at `K = 0` with a shortest-vector statement for a
specific structured modular lattice — the frame in which the census's bad primes are
exactly the primes whose lattice contains an exceptionally short vector (the small-height
norms `c^{φ(n)}+1` etc.), and the Gaussian heuristic predicts genericity.  See the kb note
for the Ring-SIS/ideal-lattice synthesis and its honest limits.  Issue #466, round 393,
LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R393KernelIdealLatticeFrame

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound
open ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber
open ArkLib.ProximityGap.Frontier.R391RelationHeightLedger
open ArkLib.ProximityGap.Frontier.R392RelationCountCapstone

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The shadow evaluation as an additive group homomorphism. -/
def evalVecHom (g : F) (m : ℕ) : (Fin m → ℤ) →+ F where
  toFun := evalVec g m
  map_zero' := by
    unfold evalVec
    simp
  map_add' v w := by
    unfold evalVec
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (v j + w j) • g ^ (j : ℕ) = _
    rw [add_smul]

/-- Every realized relation lies in the kernel of the evaluation homomorphism. -/
theorem sectorRelations_mem_ker (g : F) (n m r s : ℕ) (z : Fin m → ℤ)
    (hz : z ∈ sectorRelations g n m r s) :
    z ∈ (evalVecHom g m).ker := by
  rw [AddMonoidHom.mem_ker]
  exact (sectorRelations_vanishing g n m r s z hz).1

/-- Every realized relation has `ℓ∞ ≤ 2r`. -/
theorem sectorRelations_linf_le (g : F) (n m r s : ℕ) (z : Fin m → ℤ)
    (hz : z ∈ sectorRelations g n m r s) (j : Fin m) :
    |z j| ≤ (2 * r : ℤ) := by
  classical
  unfold sectorRelations at hz
  rw [Finset.mem_filter, Finset.mem_image] at hz
  obtain ⟨⟨q, hq, rfl⟩, _⟩ := hz
  unfold shadowCollisionPairs at hq
  rw [Finset.mem_filter, Finset.mem_offDiag] at hq
  exact abs_sub_le_two_mul n m r q.1 q.2 hq.1.1 hq.1.2.1 j

/-- **The SVP-type sufficient condition**: if the evaluation kernel contains no nonzero
vector of `ℓ∞ ≤ 2r`, then the realized-relation count is ZERO and (r392) the depth-`r`
moment control holds with the unconditional char-0 constant. -/
theorem relationCount_zero_of_no_short_kernel (g : F) (n m r : ℕ)
    (hshort : ∀ z : Fin m → ℤ, z ∈ (evalVecHom g m).ker →
      (∀ j : Fin m, |z j| ≤ (2 * r : ℤ)) → z = 0) :
    RealizedRelationCountBound g n m r 0 := by
  classical
  unfold RealizedRelationCountBound
  rw [Nat.le_zero, Finset.sum_eq_zero_iff]
  intro s _
  rw [Finset.card_eq_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
  have hker := sectorRelations_mem_ker g n m r s z hz
  have hlinf := fun j => sectorRelations_linf_le g n m r s z hz j
  have hz0 := (sectorRelations_vanishing g n m r s z hz).2
  exact hz0 (hshort z hker hlinf)

end ArkLib.ProximityGap.Frontier.R393KernelIdealLatticeFrame

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R393KernelIdealLatticeFrame.sectorRelations_mem_ker
#print axioms ArkLib.ProximityGap.Frontier.R393KernelIdealLatticeFrame.sectorRelations_linf_le
#print axioms
  ArkLib.ProximityGap.Frontier.R393KernelIdealLatticeFrame.relationCount_zero_of_no_short_kernel
