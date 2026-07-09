/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
  ⟨((a : ℕ) + 1) % n, Nat.mod_lt _ hn⟩

/-- The exponent predecessor on root indices (cyclic). -/
def predN (hn : 0 < n) (a : Fin n) : Fin n :=
  ⟨((a : ℕ) + (n - 1)) % n, Nat.mod_lt _ hn⟩

theorem predN_succN (hn : 0 < n) (a : Fin n) : predN n hn (succN n hn a) = a := by
  unfold succN predN
  apply Fin.ext
  have := a.isLt
  simp only []
  omega

theorem succN_predN (hn : 0 < n) (a : Fin n) : succN n hn (predN n hn a) = a := by
  unfold succN predN
  apply Fin.ext
  have := a.isLt
  simp only []
  omega

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
  funext j
  unfold rotZ vecOf succN
  have ha := a.isLt
  have hj := j.isLt
  by_cases h : (j : ℕ) = 0 <;> simp only [h, if_true, if_false, eq_self_iff_true] <;>
    split_ifs <;> omega

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
    have hface : t = fun i => succN n (by omega : 0 < n)
        (predN n (by omega : 0 < n) (t i)) := by
      funext i
      rw [succN_predN]
    have := ht.2
    rw [hface, rotZ_tupleVec n m r hm hn (fun i => predN n (by omega) (t i))] at this
    exact (rotZ_bijective m hm).1 this
  · intro t _
    funext i
    rw [predN_succN]
  · intro t _
    funext i
    rw [succN_predN]

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
