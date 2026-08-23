/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R322SignedWalkEndpointEnvelope

/-!
# LANE B2 (#466 round 324): collision mass stratified by relation length

R322 bounds a realized relation `d` at its exact cancellation depth

```text
s = r - ‖d‖₁/2,
```

with a factor `m^s`.  This file partitions R314's complete collision mass by that depth,
retaining the full gain instead of replacing every stratum by the worst `m^(r-1)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification

open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope

/-- Cancellation depth read directly from endpoint length. -/
def relationCancellationDepth {m : ℕ} (r : ℕ) (d : Fin m → ℤ) : ℕ :=
  (r + r - endpointL1 d) / 2

/-- Realized relations at one cancellation depth. -/
noncomputable def relationCancellationStratum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) : Finset (Fin m → ℤ) :=
  (shadowKernelRelations g (2 * m) m r).filter
    (fun d => relationCancellationDepth r d = s)

theorem relationCancellationDepth_eq_of_decomposition
    {m r s : ℕ} {d : Fin m → ℤ}
    (h : r + r = 2 * s + endpointL1 d) :
    relationCancellationDepth r d = s := by
  unfold relationCancellationDepth
  omega

theorem relationCancellationDepth_lt
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    relationCancellationDepth r d < r := by
  obtain ⟨s, hs, hdecomp, _⟩ :=
    exists_lt_shadowRelationMass_factorial_envelope g m r hd
  rw [relationCancellationDepth_eq_of_decomposition hdecomp]
  exact hs

/-- Exact partition of the complete collision surplus by cancellation depth. -/
theorem shadowCollisionMass_eq_sum_cancellation_strata
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) :
    shadowCollisionMass g (2 * m) m r =
      ∑ s ∈ Finset.range r,
        ∑ d ∈ relationCancellationStratum g m r s,
          shadowRelationMass g (2 * m) m r d := by
  classical
  rw [shadowCollisionMass_eq_sum_relationMass]
  let R := shadowKernelRelations g (2 * m) m r
  have hmaps : (↑R : Set (Fin m → ℤ)).MapsTo
      (relationCancellationDepth r) (↑(Finset.range r) : Set ℕ) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    exact relationCancellationDepth_lt g m r hd
  rw [show shadowKernelRelations g (2 * m) m r = R from rfl]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr
  · ext d
    simp [R, relationCancellationStratum]
  · intro d hd
    rfl

/-- Membership in stratum `s` recovers the exact endpoint-length decomposition. -/
theorem decomposition_of_mem_relationCancellationStratum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ relationCancellationStratum g m r s) :
    r + r = 2 * s + endpointL1 d := by
  rw [relationCancellationStratum, Finset.mem_filter] at hd
  obtain ⟨s', _hslt, hs'decomp, _⟩ :=
    exists_lt_shadowRelationMass_factorial_envelope g m r hd.1
  have hs'depth := relationCancellationDepth_eq_of_decomposition hs'decomp
  have : s' = s := hs'depth.symm.trans hd.2
  rwa [this] at hs'decomp

/-- Every relation in stratum `s` has mass at most `(2r)! m^s`. -/
theorem shadowRelationMass_le_factorial_mul_pow_of_mem_stratum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ relationCancellationStratum g m r s) :
    shadowRelationMass g (2 * m) m r d ≤ (r + r).factorial * m ^ s := by
  have hdrel : d ∈ shadowKernelRelations g (2 * m) m r :=
    (Finset.mem_filter.mp hd).1
  have hdecomp := decomposition_of_mem_relationCancellationStratum g m r s hd
  have hbound := shadowRelationMass_factorial_envelope g m r s hdrel hdecomp
  let D := s.factorial * ∏ j : Fin m, (d j).natAbs.factorial
  have hD : 1 ≤ D := by
    apply Nat.succ_le_iff.mpr
    dsimp [D]
    positivity
  calc
    shadowRelationMass g (2 * m) m r d
        ≤ shadowRelationMass g (2 * m) m r d * D := by
          simpa using Nat.mul_le_mul_left
            (shadowRelationMass g (2 * m) m r d) hD
    _ ≤ (r + r).factorial * m ^ s := by
      simpa [D, mul_assoc] using hbound

/-- **Weighted sparse-relation census reduction.** The complete collision mass is bounded by
`(2r)!` times the cancellation-depth generating function of the realized relation set. -/
theorem shadowCollisionMass_le_factorial_mul_weighted_stratum_count
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) :
    shadowCollisionMass g (2 * m) m r ≤
      (r + r).factorial *
        ∑ s ∈ Finset.range r, (relationCancellationStratum g m r s).card * m ^ s := by
  rw [shadowCollisionMass_eq_sum_cancellation_strata]
  calc
    (∑ s ∈ Finset.range r,
        ∑ d ∈ relationCancellationStratum g m r s,
          shadowRelationMass g (2 * m) m r d)
        ≤ ∑ s ∈ Finset.range r,
            ∑ _d ∈ relationCancellationStratum g m r s,
              (r + r).factorial * m ^ s := by
          apply Finset.sum_le_sum
          intro s hs
          apply Finset.sum_le_sum
          intro d hd
          exact shadowRelationMass_le_factorial_mul_pow_of_mem_stratum g m r s hd
    _ = ∑ s ∈ Finset.range r,
          (relationCancellationStratum g m r s).card *
            ((r + r).factorial * m ^ s) := by
          apply Finset.sum_congr rfl
          intro s hs
          simp
    _ = (r + r).factorial *
          ∑ s ∈ Finset.range r,
            (relationCancellationStratum g m r s).card * m ^ s := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring

end ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification.shadowCollisionMass_eq_sum_cancellation_strata
#print axioms
  ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification.shadowCollisionMass_le_factorial_mul_weighted_stratum_count
