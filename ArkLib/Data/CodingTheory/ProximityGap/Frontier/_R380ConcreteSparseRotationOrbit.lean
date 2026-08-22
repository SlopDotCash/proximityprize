/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R379SparseOrbitSupportBound
import Mathlib.GroupTheory.Perm.Fin

/-!
# R380: the concrete sparse rotation orbit covers every coordinate

The first `m` negacyclic rotations of a nonzero vector move any chosen nonzero coordinate through
all of `Fin m`.  Combined with R378's endpoint-mass invariance and R379's support-cover bound, this
gives the predicted denominator-cleared orbit estimate `m <= orbitSize * endpointL1(d)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R380ConcreteSparseRotationOrbit

open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction
open ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance
open ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound

/-- The finite orbit formed by the first `m` negacyclic rotations. -/
noncomputable def rotationOrbit (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) :
    Finset (Fin m → ℤ) :=
  (Finset.range m).image (fun t => (rotZ m hm)^[t] d)

/-- One vector rotation transports nonzeroness along one coordinate rotation. -/
theorem rotZ_apply_finRotate_ne_zero_iff
    (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) (j : Fin m) :
    rotZ m hm d (finRotate m j) ≠ 0 ↔ d j ≠ 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  by_cases hlast : j = Fin.last m'
  · subst j
    rw [finRotate_last]
    unfold rotZ
    have hind : (⟨m', by omega⟩ : Fin (m' + 1)) = Fin.last m' := rfl
    simp only [Fin.val_zero, if_true, Nat.add_sub_cancel]
    rw [hind, Int.neg_ne_zero]
  · have hcoe : ((finRotate (m' + 1) j : Fin (m' + 1)) : ℕ) = (j : ℕ) + 1 :=
      coe_finRotate_of_ne_last hlast
    unfold rotZ
    rw [if_neg (by rw [hcoe]; omega)]
    have hind :
        (⟨((finRotate (m' + 1) j : Fin (m' + 1)) : ℕ) - 1,
          by have := (finRotate (m' + 1) j).isLt; omega⟩ : Fin (m' + 1)) = j := by
      apply Fin.ext
      change ((finRotate (m' + 1) j : Fin (m' + 1)) : ℕ) - 1 = (j : ℕ)
      omega
    rw [hind]

/-- Iterated vector rotation transports a nonzero coordinate along the corresponding power of
`finRotate`. -/
theorem iterate_rotZ_apply_iterate_finRotate_ne_zero
    (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) (a : Fin m) (ha : d a ≠ 0) (t : ℕ) :
    ((rotZ m hm)^[t] d) (((finRotate m : Fin m ≃ Fin m)^[t]) a) ≠ 0 := by
  induction t with
  | zero => simpa using ha
  | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (rotZ_apply_finRotate_ne_zero_iff m hm _ _).mpr ih

/-- The concrete rotation orbit of a nonzero vector covers every coordinate. -/
theorem rotationOrbit_support_cover
    (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) (hd : d ≠ 0) :
    ∀ j : Fin m, ∃ e ∈ rotationOrbit m hm d, e j ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin m, d a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hd
    funext j
    exact h j
  intro j
  by_cases hm1 : m = 1
  · subst m
    have haj : a = j := Subsingleton.elim _ _
    refine ⟨d, ?_, by simpa [haj] using ha⟩
    rw [rotationOrbit]
    exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
  · have hm2 : 2 ≤ m := by omega
    have hcycle := isCycle_finRotate_of_le hm2
    have hsupp : (finRotate m).support = Finset.univ := support_finRotate_of_le hm2
    have hmove (x : Fin m) : finRotate m x ≠ x := by
      rw [← Equiv.Perm.mem_support, hsupp]
      exact Finset.mem_univ x
    obtain ⟨t, ht⟩ := hcycle.exists_pow_eq (hmove a) (hmove j)
    have hord : orderOf (finRotate m) = m := by
      rw [hcycle.orderOf, hsupp]
      simp
    let u := t % m
    have hu : u < m := Nat.mod_lt _ hm
    have hpow : ((finRotate m : Equiv.Perm (Fin m)) ^ u) a = j := by
      dsimp [u]
      have hmod : t % m = t % orderOf (finRotate m) := by rw [hord]
      rw [hmod, pow_mod_orderOf]
      exact ht
    have hiter : (((finRotate m : Fin m ≃ Fin m)^[u]) a) = j := by
      simpa only [Equiv.Perm.coe_pow] using hpow
    let e := (rotZ m hm)^[u] d
    refine ⟨e, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, rfl⟩
    · rw [← hiter]
      exact iterate_rotZ_apply_iterate_finRotate_ne_zero m hm d a ha u

/-- **Concrete sparse rotation-orbit bound.** -/
theorem card_rotationOrbit_mul_endpointL1_ge
    (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) (hd : d ≠ 0) :
    m ≤ (rotationOrbit m hm d).card * endpointL1 d := by
  apply card_fin_le_family_card_mul_endpointL1 (rotationOrbit m hm d) d
  · intro e he
    rw [rotationOrbit, Finset.mem_image] at he
    obtain ⟨t, ht, rfl⟩ := he
    induction t with
    | zero => rfl
    | succ t ih =>
        rw [Function.iterate_succ_apply', endpointL1_rotZ]
        exact ih (by
          rw [Finset.mem_range] at ht ⊢
          omega)
  · exact rotationOrbit_support_cover m hm d hd

/-- Depth-facing form: an endpoint of `L1 <= 2r` has a rotation orbit of denominator-cleared
size at least `m/(2r)`. -/
theorem card_rotationOrbit_mul_two_mul_r_ge
    (m r : ℕ) (hm : 0 < m) (d : Fin m → ℤ) (hd : d ≠ 0)
    (hL1 : endpointL1 d ≤ 2 * r) :
    m ≤ (rotationOrbit m hm d).card * (2 * r) := by
  exact (card_rotationOrbit_mul_endpointL1_ge m hm d hd).trans
    (Nat.mul_le_mul_left _ hL1)

end ArkLib.ProximityGap.Frontier.R380ConcreteSparseRotationOrbit

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R380ConcreteSparseRotationOrbit.rotationOrbit_support_cover
#print axioms
  ArkLib.ProximityGap.Frontier.R380ConcreteSparseRotationOrbit.card_rotationOrbit_mul_endpointL1_ge
#print axioms
  ArkLib.ProximityGap.Frontier.R380ConcreteSparseRotationOrbit.card_rotationOrbit_mul_two_mul_r_ge
