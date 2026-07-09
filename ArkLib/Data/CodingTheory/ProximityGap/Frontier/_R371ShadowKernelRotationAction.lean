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

/-- The inverse rotation. -/
def rotZinv (hm : 0 < m) (z : Fin m → ℤ) : Fin m → ℤ :=
  fun j => if (j : ℕ) = m - 1 then -z ⟨0, hm⟩
    else z ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩

theorem rotZinv_rotZ (hm : 0 < m) (z : Fin m → ℤ) : rotZinv m hm (rotZ m hm z) = z := by
  funext j
  unfold rotZ rotZinv
  by_cases h : (j : ℕ) = m - 1
  · rw [if_pos h, if_pos rfl, neg_neg]
    exact congrArg z (Fin.ext (by simp [h]))
  · rw [if_neg h, if_neg (by simp)]
    exact congrArg z (Fin.ext (by simp))

theorem rotZ_rotZinv (hm : 0 < m) (z : Fin m → ℤ) : rotZ m hm (rotZinv m hm z) = z := by
  funext j
  unfold rotZ rotZinv
  by_cases h : (j : ℕ) = 0
  · rw [if_pos h, if_pos rfl, neg_neg]
    exact congrArg z (Fin.ext (by simp [h]))
  · rw [if_neg h, if_neg (by have := j.isLt; omega)]
    exact congrArg z (Fin.ext (by have := j.isLt; simp; omega))

theorem rotZ_bijective (hm : 0 < m) : Function.Bijective (rotZ m hm) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨rotZinv m hm, fun z => rotZinv_rotZ m hm z, fun z => rotZ_rotZinv m hm z⟩

/-- **Rotation twists the evaluation by `g`** (using `g^m = −1`). -/
theorem evalVec_rotZ (g : F) (hm : 0 < m) (hg : g ^ m = -1) (z : Fin m → ℤ) :
    evalVec g m (rotZ m hm z) = g * evalVec g m z := by
  unfold evalVec rotZ
  rw [Finset.mul_sum]
  rw [show (Finset.univ : Finset (Fin m))
      = insert (⟨0, hm⟩ : Fin m) (Finset.univ.erase ⟨0, hm⟩) by
    rw [Finset.insert_erase (Finset.mem_univ _)]]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  conv_rhs =>
    rw [show (Finset.univ : Finset (Fin m))
        = insert (⟨m - 1, by omega⟩ : Fin m) (Finset.univ.erase ⟨m - 1, by omega⟩) by
      rw [Finset.insert_erase (Finset.mem_univ _)]]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  refine congrArg₂ (· + ·) ?_ ?_
  · -- head terms: (−z_{m−1}) • g^0 = g · (z_{m−1} • g^{m−1})
    rw [if_pos rfl]
    simp only [zsmul_eq_mul]
    push_cast
    have hgm : g * g ^ (m - 1) = g ^ m := by
      rw [← pow_succ']
      congr 1
      omega
    calc (-(z ⟨m - 1, by omega⟩ : ℤ) : F) * g ^ ((⟨0, hm⟩ : Fin m) : ℕ)
        = -((z ⟨m - 1, by omega⟩ : ℤ) : F) := by norm_num
      _ = ((z ⟨m - 1, by omega⟩ : ℤ) : F) * -1 := by ring
      _ = ((z ⟨m - 1, by omega⟩ : ℤ) : F) * (g * g ^ (m - 1)) := by rw [hgm, hg]
      _ = g * (((z ⟨m - 1, by omega⟩ : ℤ) : F)
            * g ^ ((⟨m - 1, by omega⟩ : Fin m) : ℕ)) := by ring
  · -- tails: reindex erase-0 ↔ erase-(m−1) by j ↦ j−1
    refine Finset.sum_nbij'
      (i := fun j => (⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ : Fin m))
      (j := fun j => (⟨((j : ℕ) + 1) % m, Nat.mod_lt _ hm⟩ : Fin m)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_erase] at hj ⊢
      have hj0 : (j : ℕ) ≠ 0 := fun h0 => hj.1 (Fin.ext (by simpa using h0))
      refine ⟨fun hc => ?_, Finset.mem_univ _⟩
      have : (j : ℕ) - 1 = m - 1 := by
        simpa using congrArg (fun x : Fin m => (x : ℕ)) hc
      have := j.isLt
      omega
    · intro j hj
      rw [Finset.mem_erase] at hj ⊢
      have hjm : (j : ℕ) ≠ m - 1 := fun h0 => hj.1 (Fin.ext (by simpa using h0))
      have hlt := j.isLt
      have hmod : ((j : ℕ) + 1) % m = (j : ℕ) + 1 := Nat.mod_eq_of_lt (by omega)
      refine ⟨fun hc => ?_, Finset.mem_univ _⟩
      have : ((j : ℕ) + 1) % m = 0 := by
        simpa using congrArg (fun x : Fin m => (x : ℕ)) hc
      omega
    · intro j hj
      rw [Finset.mem_erase] at hj
      have hj0 : (j : ℕ) ≠ 0 := fun h0 => hj.1 (Fin.ext (by simpa using h0))
      have hlt := j.isLt
      apply Fin.ext
      simp only []
      have : ((j : ℕ) - 1 + 1) % m = (j : ℕ) % m := by
        congr 1
        omega
      rw [this, Nat.mod_eq_of_lt hlt]
    · intro j hj
      rw [Finset.mem_erase] at hj
      have hjm : (j : ℕ) ≠ m - 1 := fun h0 => hj.1 (Fin.ext (by simpa using h0))
      have hlt := j.isLt
      have hmod : ((j : ℕ) + 1) % m = (j : ℕ) + 1 := Nat.mod_eq_of_lt (by omega)
      apply Fin.ext
      simp [hmod]
    · intro j hj
      rw [Finset.mem_erase] at hj
      have hj0 : (j : ℕ) ≠ 0 := fun h0 => hj.1 (Fin.ext (by simpa using h0))
      rw [if_neg hj0]
      simp only [zsmul_eq_mul]
      push_cast
      have hlt := j.isLt
      have hexp : g * g ^ ((j : ℕ) - 1) = g ^ (j : ℕ) := by
        rw [← pow_succ']
        congr 1
        omega
      calc ((z ⟨(j : ℕ) - 1, by omega⟩ : ℤ) : F) * g ^ (j : ℕ)
          = ((z ⟨(j : ℕ) - 1, by omega⟩ : ℤ) : F) * (g * g ^ ((j : ℕ) - 1)) := by
            rw [hexp]
        _ = g * (((z ⟨(j : ℕ) - 1, by omega⟩ : ℤ) : F) * g ^ ((j : ℕ) - 1)) := by ring

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
    funext j
    unfold rotZ
    subst hz
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
