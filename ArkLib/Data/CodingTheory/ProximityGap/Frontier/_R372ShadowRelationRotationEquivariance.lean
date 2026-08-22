/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R371ShadowKernelRotationAction

/-!
# LANE B2 (#466 round 372): ROTATION EQUIVARIANCE OF THE SHADOW HISTOGRAM — the
  realizability half of the r369 orbit-quantization law

r371 proved the shadow-evaluation kernel is rotation-stable.  This brick proves the
rotation acts on the REALIZED objects: it is the shadow of the exponent successor, so it
permutes tuple shadows and preserves the char-0 histogram:

* **`rotZ_add` / `rotZ_neg`** :  `rotZ` is additive;
* **`rotZ_vecOf`** :  `rotZ (vecOf a) = vecOf (succN a)` — rotating the shadow of one root
  is the shadow of the NEXT root (`ζ·ζ^a = ζ^{a+1}`, with the `ζ^m = −1` sign wrap);
* **`rotZ_tupleVec`** :  `rotZ (tupleVec t) = tupleVec (succN ∘ t)`;
* **`succN_bijective`** and **`NR_rotZ`** :  hence the histogram is rotation-invariant:
  `NR n m r (rotZ v) = NR n m r v`, and **`keysR_rotZ`**: `rotZ` maps `keysR` into itself.

With r371 (kernel stability) this completes the structural core of r369 piece (a): the
rotation acts on realized keys, preserves multiplicities, and preserves vanishing — so each
vanishing realized relation carries its full rotation orbit with IDENTICAL mass, the
orbit-quantization the census measured.  Issue #466, round 372, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction

variable (n m : ℕ)

/-- The exponent successor on root indices (cyclic). -/
def succN (hn : 0 < n) (a : Fin n) : Fin n :=
  finRotate n a

/-- The exponent predecessor on root indices (cyclic). -/
def predN (hn : 0 < n) (a : Fin n) : Fin n :=
  (finRotate n).symm a

theorem predN_succN (hn : 0 < n) (a : Fin n) : predN n hn (succN n hn a) = a := by
  exact (finRotate n).symm_apply_apply a

theorem succN_predN (hn : 0 < n) (a : Fin n) : succN n hn (predN n hn a) = a := by
  exact (finRotate n).apply_symm_apply a

theorem succN_bijective (hn : 0 < n) : Function.Bijective (succN n hn) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨predN n hn, fun a => predN_succN n hn a, fun a => succN_predN n hn a⟩

/-- `rotZ` is additive. -/
theorem rotZ_add (hm : 0 < m) (v w : Fin m → ℤ) :
    rotZ m hm (fun j => v j + w j) = fun j => rotZ m hm v j + rotZ m hm w j := by
  funext j
  unfold rotZ
  by_cases h : (j : ℕ) = 0 <;> simp [h] <;> ring

/-- **Rotation is the shadow of the successor**: `rotZ (vecOf a) = vecOf (succN a)`
(for `n = 2m`). -/
theorem rotZ_vecOf (hm : 0 < m) (hn : n = 2 * m) (a : Fin n) :
    rotZ m hm (vecOf n m a) = vecOf n m (succN n (by omega) a) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  funext j
  by_cases halastVal : (a : ℕ) = n'
  · have halast : a = Fin.last n' := Fin.ext halastVal
    have hsucc : succN (n' + 1) (by omega) a = 0 := by
      simp [succN, halast]
    rw [hsucc]
    unfold rotZ vecOf
    have hj := j.isLt
    simp only [Fin.val_zero]
    by_cases h : (j : ℕ) = 0 <;> simp only [h, if_true, if_false] <;>
      split_ifs <;> subst a <;> simp only [Fin.val_last] at * <;> omega
  · have halast : a ≠ Fin.last n' := by
      intro h
      exact halastVal (congrArg Fin.val h)
    have hsucc : ((succN (n' + 1) (by omega) a : Fin (n' + 1)) : ℕ) = (a : ℕ) + 1 := by
      exact coe_finRotate_of_ne_last halast
    clear halast
    unfold rotZ vecOf
    have ha := a.isLt
    have hj := j.isLt
    have hmPred : m - 1 < m := Nat.sub_lt hm (by decide)
    have hmEq : m - 1 + 1 = m := by omega
    simp only [hsucc]
    by_cases h : (j : ℕ) = 0 <;> simp only [h, if_true, if_false] <;>
      split_ifs <;> simp_all <;> omega

/-- Rotation equivariance of tuple shadows: `rotZ (tupleVec t) = tupleVec (succN ∘ t)`. -/
theorem rotZ_tupleVec (r : ℕ) (hm : 0 < m) (hn : n = 2 * m) (t : Fin r → Fin n) :
    rotZ m hm (tupleVec n m r t)
      = tupleVec n m r (fun i => succN n (by omega) (t i)) := by
  induction r with
  | zero =>
      funext j
      unfold tupleVec rotZ
      by_cases h : (j : ℕ) = 0 <;> simp [h]
  | succ r ih =>
      have hsplit : tupleVec n m (r + 1) t
          = fun j => tupleVec n m r (fun i : Fin r => t i.castSucc) j
              + vecOf n m (t (Fin.last r)) j := by
        funext j
        unfold tupleVec
        rw [Fin.sum_univ_castSucc]
      rw [hsplit, rotZ_add m hm]
      funext j
      have h1 := congrFun (ih (fun i : Fin r => t i.castSucc)) j
      have h2 := congrFun (rotZ_vecOf n m hm hn (t (Fin.last r))) j
      rw [h1, h2]
      show tupleVec n m r (fun i : Fin r => succN n (by omega) (t i.castSucc)) j
          + vecOf n m (succN n (by omega) (t (Fin.last r))) j
        = tupleVec n m (r + 1) (fun i => succN n (by omega) (t i)) j
      unfold tupleVec
      rw [Fin.sum_univ_castSucc]

/-- **Histogram invariance**: `NR n m r (rotZ v) = NR n m r v`. -/
theorem NR_rotZ (r : ℕ) (hm : 0 < m) (hn : n = 2 * m) (v : Fin m → ℤ) :
    NR n m r (rotZ m hm v) = NR n m r v := by
  unfold NR
  -- tuples with shadow `v` biject with tuples with shadow `rotZ v` via coordinatewise succ
  refine (Finset.card_bij'
    (i := fun t _ => fun i => succN n (by omega) (t i))
    (j := fun t _ => fun i => predN n (by omega) (t i)) ?_ ?_ ?_ ?_).symm
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← rotZ_tupleVec n m r hm hn t, ht.2]
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (rotZ_bijective m hm).1
    rw [rotZ_tupleVec n m r hm hn (fun i => predN n (by omega) (t i))]
    calc
      tupleVec n m r (fun i => succN n (by omega) (predN n (by omega) (t i))) =
          tupleVec n m r t := by
        congr 1
        funext i
        exact succN_predN n (by omega) (t i)
      _ = rotZ m hm v := ht.2
  · intro t _
    funext i
    exact predN_succN n (by omega) (t i)
  · intro t _
    funext i
    exact succN_predN n (by omega) (t i)

/-- `rotZ` maps realized keys to realized keys. -/
theorem keysR_rotZ (r : ℕ) (hm : 0 < m) (hn : n = 2 * m) (v : Fin m → ℤ)
    (hv : v ∈ keysR n m r) : rotZ m hm v ∈ keysR n m r := by
  unfold keysR at hv ⊢
  rw [Finset.mem_image] at hv ⊢
  obtain ⟨t, _, rfl⟩ := hv
  exact ⟨fun i => succN n (by omega) (t i), Finset.mem_univ _,
    (rotZ_tupleVec n m r hm hn t).symm⟩

end ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance.rotZ_vecOf
#print axioms ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance.rotZ_tupleVec
#print axioms ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance.NR_rotZ
#print axioms ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance.keysR_rotZ
