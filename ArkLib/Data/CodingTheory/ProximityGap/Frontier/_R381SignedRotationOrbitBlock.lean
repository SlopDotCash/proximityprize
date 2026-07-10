/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R380ConcreteSparseRotationOrbit

/-!
# R381: a sparse rotation orbit is one coherent signed discrepancy block

R380 gives a large finite orbit.  This file proves the orbit remains inside the actual doubled-walk
difference family and that every member has exactly the same signed endpoint contribution.  Thus
the orbit sum is its cardinality times one representative's summand.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R381SignedRotationOrbitBlock

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction
open ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance
open ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance
open ArkLib.ProximityGap.Frontier.R380ConcreteSparseRotationOrbit

/-- Rotation commutes with taking a shadow difference. -/
theorem rotZ_shadowDifference (m : ℕ) (hm : 0 < m)
    (p : (Fin m → ℤ) × (Fin m → ℤ)) :
    rotZ m hm (shadowDifference p) =
      shadowDifference (rotZ m hm p.1, rotZ m hm p.2) := by
  funext j
  unfold rotZ shadowDifference
  by_cases hj : (j : ℕ) = 0 <;> simp [hj] <;> ring

/-- One rotation preserves membership in the full shadow-difference family. -/
theorem allShadowDifferences_rotZ
    (m r : ℕ) (hm : 0 < m) {d : Fin m → ℤ}
    (hd : d ∈ allShadowDifferences (2 * m) m r) :
    rotZ m hm d ∈ allShadowDifferences (2 * m) m r := by
  classical
  rw [allShadowDifferences, Finset.mem_image] at hd ⊢
  obtain ⟨p, hp, rfl⟩ := hd
  let q : (Fin m → ℤ) × (Fin m → ℤ) := (rotZ m hm p.1, rotZ m hm p.2)
  refine ⟨q, ?_, (rotZ_shadowDifference m hm p).symm⟩
  rw [Finset.mem_offDiag] at hp ⊢
  refine ⟨keysR_rotZ (2 * m) m r hm rfl p.1 hp.1,
    keysR_rotZ (2 * m) m r hm rfl p.2 hp.2.1, ?_⟩
  intro heq
  apply hp.2.2
  exact (rotZ_bijective m hm).1 heq

/-- Every element of the concrete rotation orbit remains an actual shadow difference. -/
theorem rotationOrbit_subset_allShadowDifferences
    (m r : ℕ) (hm : 0 < m) {d : Fin m → ℤ}
    (hd : d ∈ allShadowDifferences (2 * m) m r) :
    rotationOrbit m hm d ⊆ allShadowDifferences (2 * m) m r := by
  classical
  intro e he
  rw [rotationOrbit, Finset.mem_image] at he
  obtain ⟨t, ht, rfl⟩ := he
  induction t with
  | zero => simpa using hd
  | succ t ih =>
      have ht' : t ∈ Finset.range m := Finset.mem_range.mpr
        (lt_trans (Nat.lt_succ_self t) (Finset.mem_range.mp ht))
      rw [Function.iterate_succ_apply']
      exact allShadowDifferences_rotZ m r hm (ih ht')

/-- Every member of a rotation orbit has the representative's signed summand. -/
theorem signedEndpointSummand_eq_of_mem_rotationOrbit
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) {e : Fin m → ℤ} (he : e ∈ rotationOrbit m hm d) :
    signedEndpointSummand g m r e = signedEndpointSummand g m r d := by
  classical
  rw [rotationOrbit, Finset.mem_image] at he
  obtain ⟨t, ht, rfl⟩ := he
  induction t with
  | zero => rfl
  | succ t ih =>
      have ht' : t ∈ Finset.range m := Finset.mem_range.mpr
        (lt_trans (Nat.lt_succ_self t) (Finset.mem_range.mp ht))
      rw [Function.iterate_succ_apply', signedEndpointSummand_rotZ g m r hm hg hg0, ih ht']

/-- **Orbit block identity.** -/
theorem sum_rotationOrbit_signedEndpointSummand
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    ∑ e ∈ rotationOrbit m hm d, signedEndpointSummand g m r e =
      (rotationOrbit m hm d).card * signedEndpointSummand g m r d := by
  calc
    (∑ e ∈ rotationOrbit m hm d, signedEndpointSummand g m r e) =
        ∑ _e ∈ rotationOrbit m hm d, signedEndpointSummand g m r d := by
      apply Finset.sum_congr rfl
      intro e he
      exact signedEndpointSummand_eq_of_mem_rotationOrbit g m r hm hg hg0 d he
    _ = (rotationOrbit m hm d).card * signedEndpointSummand g m r d := by simp

end ArkLib.ProximityGap.Frontier.R381SignedRotationOrbitBlock

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R381SignedRotationOrbitBlock.rotationOrbit_subset_allShadowDifferences
#print axioms
  ArkLib.ProximityGap.Frontier.R381SignedRotationOrbitBlock.sum_rotationOrbit_signedEndpointSummand
