/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R371ShadowKernelRotationAction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R394L1KernelCertificate

/-!
# LANE B2 (#466 round 395): ORBIT-COMPRESSED CERTIFICATION — the head-normalized slice
  suffices

The r394 certificate enumerates the whole `ℓ1 ≤ 2r` box.  The r371/r372 rotation-orbit law
compresses it: rotation preserves the kernel (up to the unit `g`), preserves `ℓ1`, and any
nonzero vector has a rotate with NONZERO HEAD (`z 0 ≠ 0`).  So it suffices to check the
head-nonzero slice — a factor-`m` reduction of the certification space, the ideal-lattice
symmetry cashed out as proof-search savings:

* **`iterate_rotZ_apply` / `iterate_rotZ_head`** :  the rotation dynamics on coordinates —
  after `m − j` steps, coordinate `j` arrives at the head with a sign;
* **`exists_iterate_head_ne_zero`** :  every nonzero vector has a rotate (≤ m steps) with
  nonzero head;
* **`l1_rotZ`** :  rotation preserves `ℓ1` exactly;
* **`evalVec_iterate_rotZ`** :  `evalVec (rotZ^[k] z) = g^k · evalVec z` — kernel-stable;
* **`ShortKernelFreeL1Head`** (decidable) + **`relationCount_zero_of_head_certificate`** :
  the head-slice check implies `RealizedRelationCountBound g n m r 0`;
* **`n8_r3_p1409_head_certificate`** :  the r394 instance re-certified through the
  compressed route (kernel `decide`).

Issue #466, round 395, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 400000

open Finset

namespace ArkLib.ProximityGap.Frontier.R395OrbitCompressedCertificate

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction
open ArkLib.ProximityGap.Frontier.R392RelationCountCapstone
open ArkLib.ProximityGap.Frontier.R394L1KernelCertificate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ}

theorem rotZ_head (hm : 0 < m) (w : Fin m → ℤ) :
    rotZ m hm w ⟨0, hm⟩ = -w ⟨m - 1, by omega⟩ := by
  unfold rotZ
  rw [if_pos rfl]

theorem rotZ_tail (hm : 0 < m) (w : Fin m → ℤ) (j : Fin m) (hj : (j : ℕ) ≠ 0) :
    rotZ m hm w j = w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ := by
  unfold rotZ
  rw [if_neg hj]

/-- Rotation dynamics: after `k` steps, coordinate `j` sits at `j + k` (no wrap). -/
theorem iterate_rotZ_apply (hm : 0 < m) (z : Fin m → ℤ) (k : ℕ) (j : ℕ)
    (hjk : j + k < m) :
    ((rotZ m hm)^[k] z) ⟨j + k, hjk⟩ = z ⟨j, by omega⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [rotZ_tail hm _ ⟨j + (k + 1), hjk⟩ (by show j + (k + 1) ≠ 0; omega)]
      rw [show (⟨((⟨j + (k + 1), hjk⟩ : Fin m) : ℕ) - 1, by
          have := (⟨j + (k + 1), hjk⟩ : Fin m).isLt
          omega⟩ : Fin m)
        = ⟨j + k, by omega⟩ from Fin.ext (show j + (k + 1) - 1 = j + k from by omega)]
      exact ih (by omega)

/-- After `m − j` steps, coordinate `j` arrives at the head with a sign flip. -/
theorem iterate_rotZ_head (hm : 0 < m) (z : Fin m → ℤ) (j : ℕ) (hj : j < m) :
    ((rotZ m hm)^[m - j] z) ⟨0, hm⟩ = -z ⟨j, hj⟩ := by
  have hstep : m - j = (m - 1 - j) + 1 := by omega
  rw [hstep, Function.iterate_succ_apply', rotZ_head hm]
  have harr : ((rotZ m hm)^[m - 1 - j] z) ⟨m - 1, by omega⟩ = z ⟨j, hj⟩ := by
    have h0 := iterate_rotZ_apply hm z (m - 1 - j) j (by omega)
    rw [show (⟨j + (m - 1 - j), by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ from
      Fin.ext (show j + (m - 1 - j) = m - 1 from by omega)] at h0
    exact h0
  rw [harr]

/-- Every nonzero vector has a rotate (at most `m` steps) with nonzero head. -/
theorem exists_iterate_head_ne_zero (hm : 0 < m) (z : Fin m → ℤ) (hz0 : z ≠ 0) :
    ∃ k ≤ m, ((rotZ m hm)^[k] z) ⟨0, hm⟩ ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
  refine ⟨m - (j : ℕ), by omega, ?_⟩
  rw [iterate_rotZ_head hm z (j : ℕ) j.isLt]
  simpa using hj

/-- Rotation preserves `ℓ1` exactly. -/
theorem l1_rotZ (hm : 0 < m) (z : Fin m → ℤ) :
    ∑ j : Fin m, |rotZ m hm z j| = ∑ j : Fin m, |z j| := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [← Equiv.sum_comp (finRotate (m' + 1)) (fun j => |rotZ (m' + 1) hm z j|)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j = Fin.last m'
  · rw [hj, finRotate_last]
    rw [show ((0 : Fin (m' + 1))) = ⟨0, hm⟩ from rfl]
    rw [rotZ_head hm]
    rw [show (⟨m' + 1 - 1, by omega⟩ : Fin (m' + 1)) = Fin.last m' from
      Fin.ext (by simp)]
    rw [abs_neg]
  · have hne : ((finRotate (m' + 1)) j : ℕ) = (j : ℕ) + 1 :=
      coe_finRotate_of_ne_last hj
    rw [rotZ_tail hm _ _ (by rw [hne]; omega)]
    congr 1
    apply congrArg
    apply Fin.ext
    show ((finRotate (m' + 1)) j : ℕ) - 1 = (j : ℕ)
    rw [hne]
    omega

/-- Iterated rotation preserves `ℓ1`. -/
theorem l1_iterate_rotZ (hm : 0 < m) (z : Fin m → ℤ) (k : ℕ) :
    ∑ j : Fin m, |((rotZ m hm)^[k] z) j| = ∑ j : Fin m, |z j| := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', l1_rotZ hm]
      exact ih

/-- The evaluation of an iterated rotate is a unit multiple of the original. -/
theorem evalVec_iterate_rotZ (g : F) (hm : 0 < m) (hg : g ^ m = -1)
    (z : Fin m → ℤ) (k : ℕ) :
    evalVec g m ((rotZ m hm)^[k] z) = g ^ k * evalVec g m z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', evalVec_rotZ m g hm hg, ih]
      ring

/-- The DECIDABLE head-slice certificate: every `ℓ1 ≤ R` box vector with NONZERO head
killing the evaluation is impossible. -/
def ShortKernelFreeL1Head (g : F) (m R : ℕ) (hm : 0 < m) : Prop :=
  ∀ c : Fin m → Fin (2 * R + 1),
    (∑ j : Fin m, |((c j : ℕ) : ℤ) - (R : ℤ)|) ≤ (R : ℤ) →
    ((c ⟨0, hm⟩ : ℕ) : ℤ) ≠ (R : ℤ) →
    evalVec g m (fun j => ((c j : ℕ) : ℤ) - (R : ℤ)) ≠ 0

instance (g : F) (m R : ℕ) (hm : 0 < m) :
    Decidable (ShortKernelFreeL1Head g m R hm) := by
  unfold ShortKernelFreeL1Head
  infer_instance

/-- **Orbit-compressed certification**: the head slice suffices — via rotation
normalization, kernel stability, and `ℓ1` invariance. -/
theorem relationCount_zero_of_head_certificate (g : F) (n m r : ℕ) (hm : 0 < m)
    (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (h : ShortKernelFreeL1Head g m (2 * r) hm) :
    RealizedRelationCountBound g n m r 0 := by
  refine relationCount_zero_of_no_l1_short_kernel g n m r ?_
  intro z hker hl1
  by_contra hz0
  obtain ⟨k, _, hhead⟩ := exists_iterate_head_ne_zero hm z hz0
  set w : Fin m → ℤ := (rotZ m hm)^[k] z with hw
  have hwker : evalVec g m w = 0 := by
    rw [hw, evalVec_iterate_rotZ g hm hg z k, hker, mul_zero]
  have hwl1 : (∑ j : Fin m, |w j|) ≤ (2 * r : ℤ) := by
    rw [hw, l1_iterate_rotZ hm z k]
    exact hl1
  -- box coordinates for w (as in r394's bridge)
  have hbound : ∀ j : Fin m, |w j| ≤ (2 * r : ℤ) := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |w j|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ j)) hwl1
  have hc : ∀ j : Fin m, ∃ cj : Fin (2 * (2 * r) + 1),
      ((cj : ℕ) : ℤ) = w j + (2 * r : ℤ) := by
    intro j
    have h1 := abs_le.mp (hbound j)
    refine ⟨⟨(w j + (2 * r : ℤ)).toNat, ?_⟩, ?_⟩
    · omega
    · show (((w j + (2 * r : ℤ)).toNat : ℕ) : ℤ) = w j + (2 * r : ℤ)
      omega
  choose c hcz using hc
  have hzc : (fun j => ((c j : ℕ) : ℤ) - ((2 * r : ℕ) : ℤ)) = w := by
    funext j
    rw [hcz j]
    push_cast
    ring
  refine h c ?_ ?_ ?_
  · calc (∑ j : Fin m, |((c j : ℕ) : ℤ) - ((2 * r : ℕ) : ℤ)|)
        = ∑ j : Fin m, |w j| :=
          Finset.sum_congr rfl (fun j _ => by rw [congrFun hzc j])
      _ ≤ (2 * r : ℤ) := hwl1
      _ = ((2 * r : ℕ) : ℤ) := by push_cast; ring
  · intro heq
    apply hhead
    have h0 := hcz ⟨0, hm⟩
    rw [heq] at h0
    push_cast at h0
    show w ⟨0, hm⟩ = 0
    linarith
  · rw [hzc]
    exact hwker

/-- The r394 instance, re-certified through the orbit-compressed route. -/
theorem n8_r3_p1409_head_certificate :
    RealizedRelationCountBound (72 : ZMod 1409) 8 4 3 0 :=
  relationCount_zero_of_head_certificate (72 : ZMod 1409) 8 4 3 (by norm_num)
    (by decide) (by decide) (by decide)

end ArkLib.ProximityGap.Frontier.R395OrbitCompressedCertificate

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R395OrbitCompressedCertificate.exists_iterate_head_ne_zero
#print axioms ArkLib.ProximityGap.Frontier.R395OrbitCompressedCertificate.l1_rotZ
#print axioms
  ArkLib.ProximityGap.Frontier.R395OrbitCompressedCertificate.relationCount_zero_of_head_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R395OrbitCompressedCertificate.n8_r3_p1409_head_certificate
