/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R393KernelIdealLatticeFrame
import Mathlib.Data.ZMod.Basic

/-!
# LANE B2 (#466 round 394): THE ℓ1 KERNEL CERTIFICATE — and the first concrete
  machine-checked `K = 0` instance

The r393 ℓ∞ condition is TOO WEAK in practice: at `(n, r, p) = (8, 3, 1409)` the kernel
contains 16 vectors of `ℓ∞ ≤ 6`, yet the census says `K = 0` — because realized relations
satisfy the sharper `ℓ1 ≤ 2r`, and the ℓ1-shortest kernel vector at 1409 has `ℓ1 = 13 > 6`.
This brick lands the correct norm and the first end-to-end instance:

* **`l1_le_of_mem_keysR`** :  realized keys have `ℓ1 ≤ r` (each tuple coordinate
  contributes at most one unit);
* **`sectorRelations_l1_le`** :  realized relations have `ℓ1 ≤ 2r`;
* **`relationCount_zero_of_no_l1_short_kernel`** :  no nonzero kernel vector of
  `ℓ1 ≤ 2r` ⟹ `RealizedRelationCountBound g n m r 0`;
* **`ShortKernelFreeL1`** :  the DECIDABLE box form of that hypothesis, with the bridge
  `shortKernelFreeL1_elim`;
* **`n8_r3_p1409_relationCount_zero`** :  the first concrete certificate —
  `RealizedRelationCountBound (72 : ZMod 1409) 8 4 3 0`, by kernel decision procedure
  (`72` has order 8, `72⁴ = −1`), with NO census input.  Via r392 this gives the depth-3
  moment control at `p = 1409` with the unconditional char-0 constant, entirely inside
  Lean.

This is the certification path the r393 frame promised: per-instance unconditional `K = 0`
by finite enumeration — scalable in principle to deployment-shaped instances.  Issue #466,
round 394, LANE B2.  Axiom-clean (decide-free of `native_decide`; plain kernel `decide`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 400000

open Finset

namespace ArkLib.ProximityGap.Frontier.R394L1KernelCertificate

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound
open ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber
open ArkLib.ProximityGap.Frontier.R392RelationCountCapstone
open ArkLib.ProximityGap.Frontier.R393KernelIdealLatticeFrame

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem l1_vecOf_le_one (n m : ℕ) (a : Fin n) :
    ∑ j : Fin m, |vecOf n m a j| ≤ 1 := by
  classical
  by_cases hm : (a : ℕ) < m
  · rw [Finset.sum_eq_single (⟨(a : ℕ), hm⟩ : Fin m)]
    · unfold vecOf
      split_ifs <;> norm_num
    · intro j _ hj
      unfold vecOf
      have h1 : ¬ ((a : ℕ) = (j : ℕ)) := fun h => hj (Fin.ext h.symm)
      have h2 : ¬ ((a : ℕ) = (j : ℕ) + m) := by
        intro h
        omega
      simp [h1, h2]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · by_cases hm2 : (a : ℕ) < 2 * m
    · have hmm : (a : ℕ) - m < m := by omega
      rw [Finset.sum_eq_single (⟨(a : ℕ) - m, hmm⟩ : Fin m)]
      · unfold vecOf
        split_ifs <;> norm_num
      · intro j _ hj
        unfold vecOf
        have h1 : ¬ ((a : ℕ) = (j : ℕ)) := by omega
        have h2 : ¬ ((a : ℕ) = (j : ℕ) + m) := by
          intro h
          apply hj
          apply Fin.ext
          show (j : ℕ) = (a : ℕ) - m
          omega
        simp [h1, h2]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · -- degenerate: `a ≥ 2m` — every entry vanishes
      have : ∀ j : Fin m, vecOf n m a j = 0 := by
        intro j
        unfold vecOf
        have hj := j.isLt
        have h1 : ¬ ((a : ℕ) = (j : ℕ)) := by omega
        have h2 : ¬ ((a : ℕ) = (j : ℕ) + m) := by omega
        simp [h1, h2]
      rw [Finset.sum_congr rfl (fun j _ => by rw [this j])]
      simp

/-- Realized keys have `ℓ1 ≤ r`. -/
theorem l1_le_of_mem_keysR (n m r : ℕ) (v : Fin m → ℤ)
    (hv : v ∈ keysR n m r) : ∑ j : Fin m, |v j| ≤ (r : ℤ) := by
  classical
  unfold keysR at hv
  rw [Finset.mem_image] at hv
  obtain ⟨t, _, rfl⟩ := hv
  unfold tupleVec
  calc ∑ j : Fin m, |∑ i : Fin r, vecOf n m (t i) j|
      ≤ ∑ j : Fin m, ∑ i : Fin r, |vecOf n m (t i) j| :=
        Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i : Fin r, ∑ j : Fin m, |vecOf n m (t i) j| := Finset.sum_comm
    _ ≤ ∑ _i : Fin r, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => l1_vecOf_le_one n m (t i))
    _ = (r : ℤ) := by simp

/-- Realized relations have `ℓ1 ≤ 2r`. -/
theorem sectorRelations_l1_le (g : F) (n m r s : ℕ) (z : Fin m → ℤ)
    (hz : z ∈ sectorRelations g n m r s) :
    ∑ j : Fin m, |z j| ≤ (2 * r : ℤ) := by
  classical
  unfold sectorRelations at hz
  rw [Finset.mem_filter, Finset.mem_image] at hz
  obtain ⟨⟨q, hq, rfl⟩, _⟩ := hz
  unfold shadowCollisionPairs at hq
  rw [Finset.mem_filter, Finset.mem_offDiag] at hq
  calc ∑ j : Fin m, |q.1 j - q.2 j|
      ≤ ∑ j : Fin m, (|q.1 j| + |q.2 j|) :=
        Finset.sum_le_sum (fun j _ => abs_sub _ _)
    _ = (∑ j : Fin m, |q.1 j|) + ∑ j : Fin m, |q.2 j| := Finset.sum_add_distrib
    _ ≤ (r : ℤ) + (r : ℤ) :=
        add_le_add (l1_le_of_mem_keysR n m r q.1 hq.1.1)
          (l1_le_of_mem_keysR n m r q.2 hq.1.2.1)
    _ = (2 * r : ℤ) := by ring

/-- **The ℓ1 SVP-type sufficient condition** (the correct norm — the r393 ℓ∞ form is
strictly weaker): no nonzero kernel vector of `ℓ1 ≤ 2r` ⟹ zero realized relations. -/
theorem relationCount_zero_of_no_l1_short_kernel (g : F) (n m r : ℕ)
    (hshort : ∀ z : Fin m → ℤ, evalVec g m z = 0 →
      (∑ j : Fin m, |z j|) ≤ (2 * r : ℤ) → z = 0) :
    RealizedRelationCountBound g n m r 0 := by
  classical
  unfold RealizedRelationCountBound
  rw [Nat.le_zero, Finset.sum_eq_zero_iff]
  intro s _
  rw [Finset.card_eq_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
  have hvan := sectorRelations_vanishing g n m r s z hz
  exact hvan.2 (hshort z hvan.1 (sectorRelations_l1_le g n m r s z hz))

/-- The decidable box form: every vector of the `ℓ∞ ≤ R` box with `ℓ1 ≤ R` that kills the
evaluation is zero.  (`R = 2r`; box coordinates shifted to `Fin (2R+1)`.) -/
def ShortKernelFreeL1 (g : F) (m R : ℕ) : Prop :=
  ∀ c : Fin m → Fin (2 * R + 1),
    (∑ j : Fin m, |((c j : ℕ) : ℤ) - (R : ℤ)|) ≤ (R : ℤ) →
    evalVec g m (fun j => ((c j : ℕ) : ℤ) - (R : ℤ)) = 0 →
    ∀ j : Fin m, ((c j : ℕ) : ℤ) = (R : ℤ)

instance (g : F) (m R : ℕ) : Decidable (ShortKernelFreeL1 g m R) := by
  unfold ShortKernelFreeL1
  infer_instance

/-- Bridge: the decidable box form implies the ℓ1 hypothesis. -/
theorem shortKernelFreeL1_elim (g : F) (m r : ℕ)
    (h : ShortKernelFreeL1 g m (2 * r)) :
    ∀ z : Fin m → ℤ, evalVec g m z = 0 →
      (∑ j : Fin m, |z j|) ≤ (2 * r : ℤ) → z = 0 := by
  intro z hker hl1
  have hbound : ∀ j : Fin m, |z j| ≤ (2 * r : ℤ) := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |z j|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ j)) hl1
  have hc : ∀ j : Fin m, ∃ cj : Fin (2 * (2 * r) + 1),
      ((cj : ℕ) : ℤ) = z j + (2 * r : ℤ) := by
    intro j
    have h1 := abs_le.mp (hbound j)
    refine ⟨⟨(z j + (2 * r : ℤ)).toNat, ?_⟩, ?_⟩
    · omega
    · show (((z j + (2 * r : ℤ)).toNat : ℕ) : ℤ) = z j + (2 * r : ℤ)
      omega
  choose c hcz using hc
  have hzc : (fun j => ((c j : ℕ) : ℤ) - ((2 * r : ℕ) : ℤ)) = z := by
    funext j
    rw [hcz j]
    push_cast
    ring
  have h1' : (∑ j : Fin m, |((c j : ℕ) : ℤ) - ((2 * r : ℕ) : ℤ)|)
      ≤ ((2 * r : ℕ) : ℤ) := by
    calc (∑ j : Fin m, |((c j : ℕ) : ℤ) - ((2 * r : ℕ) : ℤ)|)
        = ∑ j : Fin m, |z j| :=
          Finset.sum_congr rfl (fun j _ => by rw [congrFun hzc j])
      _ ≤ (2 * r : ℤ) := hl1
      _ = ((2 * r : ℕ) : ℤ) := by push_cast; ring
  have h2' : evalVec g m (fun j => ((c j : ℕ) : ℤ) - ((2 * r : ℕ) : ℤ)) = 0 := by
    rw [hzc]
    exact hker
  have h3 := h c h1' h2'
  funext j
  have hj := h3 j
  have hcj := hcz j
  show z j = 0
  push_cast at hj hcj
  omega

/-! ## The first concrete instance: `(n, r, p) = (8, 3, 1409)`, `g = 72` (order 8) -/

instance primeFact_R394L1KernelCertificate_1 : Fact (Nat.Prime 1409) := ⟨by norm_num⟩

theorem n8_p1409_g72_pow : (72 : ZMod 1409) ^ 4 = -1 := by decide

theorem n8_r3_p1409_shortKernelFree :
    ShortKernelFreeL1 (72 : ZMod 1409) 4 6 := by decide

/-- **The first concrete machine-checked `K = 0` certificate**: at `p = 1409`, `n = 8`,
depth `r = 3`, there are NO realized vanishing relations — by kernel decision procedure,
with no census input.  Via r392 the depth-3 moment control at this instance holds with the
unconditional char-0 constant. -/
theorem n8_r3_p1409_relationCount_zero :
    RealizedRelationCountBound (72 : ZMod 1409) 8 4 3 0 :=
  relationCount_zero_of_no_l1_short_kernel _ 8 4 3
    (shortKernelFreeL1_elim _ 4 3 n8_r3_p1409_shortKernelFree)

end ArkLib.ProximityGap.Frontier.R394L1KernelCertificate

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R394L1KernelCertificate.l1_le_of_mem_keysR
#print axioms
  ArkLib.ProximityGap.Frontier.R394L1KernelCertificate.relationCount_zero_of_no_l1_short_kernel
#print axioms ArkLib.ProximityGap.Frontier.R394L1KernelCertificate.shortKernelFreeL1_elim
#print axioms
  ArkLib.ProximityGap.Frontier.R394L1KernelCertificate.n8_r3_p1409_relationCount_zero
