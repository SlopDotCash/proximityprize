/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKTransversalMomentPartition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKTransversalRepProfile
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance

/-!
# HBK representation-count moments on a transversal

Equal `cosetLabel`s give equal additive representation counts.  Instantiating the generic uniform
coset partition with `repCount` and `repCount²` yields the exact first and second nonzero moment
identities.  Combined with the ordered-profile preservation theorems, these are HBK equations
(9)/(10) before the separate zero-frequency term is restored. Issue #466.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities

open scoped BigOperators
open Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open HBKTransversalMomentPartition
open HBKTransversalRepProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Equal nonzero coset labels give equal representation counts for `μ_n`. -/
theorem repCount_eq_of_cosetLabel_eq
    {n : ℕ} (hn : 0 < n) {t x : F} (ht : t ≠ 0) (hx : x ≠ 0)
    (hlabel : cosetLabel n x = cosetLabel n t) :
    repCount (nthRootsFinset n (1 : F)) x =
      repCount (nthRootsFinset n (1 : F)) t := by
  let G := nthRootsFinset n (1 : F)
  let u := x * t⁻¹
  have hu : u ∈ G := by
    apply ratio_mem_of_cosetLabel_eq hn ht hx
    exact hlabel.symm
  have hGmem : ∀ z : F, z ∈ G ↔ z ^ n = 1 := by
    intro z
    simpa [G] using
      (mem_nthRootsFinset hn (1 : F) : z ∈ nthRootsFinset n (1 : F) ↔ z ^ n = 1)
  have hinv := repCount_mul_mem_eq (show 1 ≤ n by omega) hGmem t hu
  calc
    repCount G x = repCount G (t * u) := by
      congr 1
      dsimp [u]
      field_simp
    _ = repCount G t := hinv

/-- Exact first nonzero moment on a concrete transversal. -/
theorem sum_nonzero_repCount_eq_mul_sum_transversal
    {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {T : Finset F} (hT : IsCosetTransversal n T) :
    (∑ x ∈ nonzeroFreqs F, repCount (nthRootsFinset n (1 : F)) x) =
      n * ∑ t ∈ T, repCount (nthRootsFinset n (1 : F)) t := by
  apply sum_nonzero_eq_card_mul_sum_transversal hζprim hn hT
  intro t ht x hx hlabel
  have ht0 : t ≠ 0 := by
    have := hT.subset ht
    rwa [mem_nonzeroFreqs] at this
  have hx0 : x ≠ 0 := by rwa [mem_nonzeroFreqs] at hx
  exact repCount_eq_of_cosetLabel_eq hn ht0 hx0 hlabel

/-- Exact second nonzero moment on a concrete transversal. -/
theorem sum_nonzero_repCount_sq_eq_mul_sum_transversal
    {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {T : Finset F} (hT : IsCosetTransversal n T) :
    (∑ x ∈ nonzeroFreqs F, repCount (nthRootsFinset n (1 : F)) x ^ 2) =
      n * ∑ t ∈ T, repCount (nthRootsFinset n (1 : F)) t ^ 2 := by
  apply sum_nonzero_eq_card_mul_sum_transversal hζprim hn hT
  intro t ht x hx hlabel
  rw [repCount_eq_of_cosetLabel_eq hn
    (by have := hT.subset ht; rwa [mem_nonzeroFreqs] at this)
    (by rwa [mem_nonzeroFreqs] at hx) hlabel]

/-- Second-moment identity already expressed through the canonical ordered profile. -/
theorem sum_nonzero_repCount_sq_eq_mul_profile_sq
    {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {T : Finset F} (hT : IsCosetTransversal n T) :
    (∑ x ∈ nonzeroFreqs F, repCount (nthRootsFinset n (1 : F)) x ^ 2) =
      n * ∑ i ∈ Finset.range T.card,
        transversalRepProfile (nthRootsFinset n (1 : F)) T i ^ 2 := by
  rw [sum_nonzero_repCount_sq_eq_mul_sum_transversal hζprim hn hT,
    sum_transversalRepProfile_sq]

end ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities

#print axioms
  ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities.repCount_eq_of_cosetLabel_eq
#print axioms
  ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities.sum_nonzero_repCount_sq_eq_mul_profile_sq
