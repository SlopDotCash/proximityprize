/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R314KernelRelationMassDecomposition

/-!
# LANE B2 (#466 round 371): THE ROTATION ACTION ON THE SHADOW KERNEL — piece (a) of the
  r369 orbit-quantization law

r369 measured (exactly, at census scale) that vanishing kernel relations come in full
rotation×Galois orbits, quantizing the collision mass in Θ(n)-size units.  This brick lands
the ROTATION half in Lean: the twist map `rotZ` (the shadow-basis avatar of `z ↦ ζ·z`,
using `ζ^m = −1`):

* **`evalVec_rotZ`** :  `evalVec g m (rotZ z) = g · evalVec g m z`;
* **`rotZ_eval_zero_iff`** :  for `g ≠ 0` the kernel of the shadow evaluation is
  rotation-stable;
* **`rotZ_bijective`** (explicit inverse `rotZinv`) and **`rotZ_ne_zero_iff`**,
  **`rotZ_height_le`** :  the action is by height-preserving bijections on nonzero vectors.

Hence one nonzero vanishing relation yields the whole rotation orbit of nonzero vanishing
relations — the orbits r369 measured.  The realizability/mass-invariance half of piece (a)
is the next brick.  Issue #466, round 371, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable (m : ℕ)

/-- The rotation twist on shadow vectors (`z ↦ ζ·z` in the basis `1, ζ, …, ζ^{m−1}`,
`ζ^m = −1`): coefficients shift up one slot; the top coefficient wraps to slot `0` with a
sign flip. -/
def rotZ (hm : 0 < m) (z : Fin m → ℤ) : Fin m → ℤ :=
  fun j => if (j : ℕ) = 0 then -z ⟨m - 1, by omega⟩
    else z ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩

/-- The inverse rotation (total via `% m`; on the non-wrap branch `(j+1) % m = j+1`). -/
def rotZinv (hm : 0 < m) (z : Fin m → ℤ) : Fin m → ℤ :=
  fun j => if (j : ℕ) = m - 1 then -z ⟨0, hm⟩
    else z ⟨((j : ℕ) + 1) % m, Nat.mod_lt _ hm⟩

theorem rotZinv_rotZ (hm : 0 < m) (z : Fin m → ℤ) : rotZinv m hm (rotZ m hm z) = z := by
  funext j
  simp only [rotZ, rotZinv]
  by_cases h : (j : ℕ) = m - 1
  · rw [if_pos h]
    simp only [if_true, neg_neg]
    exact congrArg z (Fin.ext (by simp [h]))
  · have hlt := j.isLt
    have hmod : ((j : ℕ) + 1) % m = (j : ℕ) + 1 := Nat.mod_eq_of_lt (by omega)
    rw [if_neg h, if_neg (by omega)]
    exact congrArg z (Fin.ext (by simp [hmod]))

theorem rotZ_rotZinv (hm : 0 < m) (z : Fin m → ℤ) : rotZ m hm (rotZinv m hm z) = z := by
  funext j
  simp only [rotZ, rotZinv]
  by_cases h : (j : ℕ) = 0
  · rw [if_pos h]
    simp only [if_true, neg_neg]
    exact congrArg z (Fin.ext (by simp [h]))
  · have hlt := j.isLt
    rw [if_neg h, if_neg (by omega)]
    have hmod : ((j : ℕ) - 1 + 1) % m = (j : ℕ) := by
      have : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
      rw [this, Nat.mod_eq_of_lt hlt]
    exact congrArg z (Fin.ext (by simp [hmod]))

theorem rotZ_bijective (hm : 0 < m) : Function.Bijective (rotZ m hm) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨rotZinv m hm, fun z => rotZinv_rotZ m hm z, fun z => rotZ_rotZinv m hm z⟩

/-- **Rotation twists the evaluation by `g`** (using `g^m = −1`). -/
theorem evalVec_rotZ (g : F) (hm : 0 < m) (hg : g ^ m = -1) (z : Fin m → ℤ) :
    evalVec g m (rotZ m hm z) = g * evalVec g m z := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold evalVec
  rw [Finset.mul_sum]
  -- reindex the LHS by the rotation equivalence `finRotate`
  rw [← Equiv.sum_comp (finRotate (m' + 1))
    (fun j => (rotZ (m' + 1) hm z j : ℤ) • g ^ (j : ℕ))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : j = Fin.last m'
  · -- wrap term: `σ(last) = 0`, and `−z_{m'} • g^0 = g · (z_{m'} • g^{m'})`
    subst h
    rw [finRotate_last]
    have hz0 : rotZ (m' + 1) hm z 0 = -z ⟨m', by omega⟩ := by
      unfold rotZ
      simp only [Fin.val_zero, eq_self_iff_true, if_true]
      exact congrArg (fun x => -z x) (Fin.ext (by simp))
    rw [hz0]
    simp only [zsmul_eq_mul]
    push_cast
    simp only [Fin.val_zero, Fin.val_last, pow_zero, mul_one]
    have hgm : g * g ^ m' = g ^ (m' + 1) := by rw [← pow_succ']
    have hzz : z (Fin.last m') = z ⟨m', by omega⟩ := rfl
    rw [hzz]
    calc (-((z ⟨m', by omega⟩ : ℤ) : F))
        = ((z ⟨m', by omega⟩ : ℤ) : F) * -1 := by ring
      _ = ((z ⟨m', by omega⟩ : ℤ) : F) * (g * g ^ m') := by rw [hgm, hg]
      _ = g * (((z ⟨m', by omega⟩ : ℤ) : F) * g ^ m') := by ring
  · -- generic term: `σ(j) = j+1`, `(rotZ z)_{j+1} = z_j`, `g^{j+1} = g·g^j`
    have hcoe : ((finRotate (m' + 1) j : Fin (m' + 1)) : ℕ) = (j : ℕ) + 1 := by
      rw [coe_finRotate_of_ne_last h]
    have hzj : rotZ (m' + 1) hm z (finRotate (m' + 1) j) = z j := by
      unfold rotZ
      rw [if_neg (by rw [hcoe]; omega)]
      refine congrArg z (Fin.ext ?_)
      show ((finRotate (m' + 1) j : Fin (m' + 1)) : ℕ) - 1 = (j : ℕ)
      rw [hcoe]
      omega
    rw [hzj]
    simp only [zsmul_eq_mul]
    rw [hcoe]
    have hexp : g ^ ((j : ℕ) + 1) = g * g ^ (j : ℕ) := by rw [← pow_succ']
    rw [hexp]
    ring

/-- **Kernel stability**: for `g ≠ 0`, rotation preserves vanishing of the evaluation. -/
theorem rotZ_eval_zero_iff (g : F) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (z : Fin m → ℤ) :
    evalVec g m (rotZ m hm z) = 0 ↔ evalVec g m z = 0 := by
  rw [evalVec_rotZ m g hm hg z, mul_eq_zero]
  simp [hg0]

/-- Rotation preserves nonzeroness of the relation vector. -/
theorem rotZ_ne_zero_iff (hm : 0 < m) (z : Fin m → ℤ) :
    rotZ m hm z ≠ 0 ↔ z ≠ 0 := by
  constructor
  · intro h hz
    apply h
    subst hz
    funext j
    unfold rotZ
    by_cases hj : (j : ℕ) = 0 <;> simp [hj]
  · intro hz h
    apply hz
    have := congrArg (rotZinv m hm) h
    rw [rotZinv_rotZ] at this
    rw [this]
    funext j
    unfold rotZinv
    by_cases hj : (j : ℕ) = m - 1 <;> simp [hj]

/-- Rotation preserves the height bound. -/
theorem rotZ_height_le (hm : 0 < m) (z : Fin m → ℤ) (B : ℤ)
    (hB : ∀ j, |z j| ≤ B) : ∀ j, |rotZ m hm z j| ≤ B := by
  intro j
  unfold rotZ
  by_cases hj : (j : ℕ) = 0
  · rw [if_pos hj, abs_neg]
    exact hB _
  · rw [if_neg hj]
    exact hB _

end ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction.evalVec_rotZ
#print axioms ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction.rotZ_eval_zero_iff
#print axioms ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction.rotZ_bijective
#print axioms ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction.rotZ_ne_zero_iff
#print axioms ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction.rotZ_height_le
