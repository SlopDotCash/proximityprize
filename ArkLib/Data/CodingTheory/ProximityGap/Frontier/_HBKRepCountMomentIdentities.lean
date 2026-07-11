/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKTransversalMomentPartition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKTransversalRepProfile
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicSupplyBound

/-!
# HBK representation-count moments on a transversal

Equal `cosetLabel`s give equal additive representation counts.  Instantiating the generic uniform
coset partition with `repCount` and `repCount²` yields the exact first and second nonzero moment
identities.  Combined with the ordered-profile preservation theorems, these are HBK equations
(9)/(10) before the separate zero-frequency term is restored. Issue #466.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities

open scoped BigOperators
open Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open HBKTransversalMomentPartition
open HBKTransversalRepProfile
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

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

/-- Even-order roots of unity are closed under negation. -/
theorem neg_mem_nthRootsFinset_of_even
    {n : ℕ} (hn : 0 < n) (heven : Even n) {x : F}
    (hx : x ∈ nthRootsFinset n (1 : F)) : -x ∈ nthRootsFinset n (1 : F) := by
  rw [mem_nthRootsFinset hn (1 : F)] at hx ⊢
  simpa [heven.neg_pow] using hx

/-- Total first moment of the representation function. -/
theorem sum_univ_repCount_eq_card_sq (G : Finset F) :
    (∑ s : F, repCount G s) = G.card ^ 2 := by
  classical
  simp_rw [repCount_eq_sum_pairs]
  calc
    (∑ s : F, ∑ a ∈ G, ∑ b ∈ G, if a + b = s then 1 else 0) =
        ∑ a ∈ G, ∑ b ∈ G, ∑ s : F, if a + b = s then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ a ∈ G, ∑ b ∈ G, 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp
    _ = G.card ^ 2 := by simp [pow_two]

/-- **HBK equation (10) on the ordered profile.** -/
theorem sum_transversal_profile_eq_card_sub_one
    {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {T : Finset F} (hT : IsCosetTransversal n T)
    (hneg : ∀ x ∈ nthRootsFinset n (1 : F), -x ∈ nthRootsFinset n (1 : F)) :
    (∑ i ∈ Finset.range T.card,
      transversalRepProfile (nthRootsFinset n (1 : F)) T i) = n - 1 := by
  let G := nthRootsFinset n (1 : F)
  have hGcard : G.card = n := hζprim.card_nthRootsFinset
  have hzero : repCount G 0 = n := by
    rw [repCount_zero_eq_card hneg, hGcard]
  have hglobal := sum_univ_repCount_eq_card_sq G
  have hsplit :
      (∑ s : F, repCount G s) = repCount G 0 +
        ∑ s ∈ nonzeroFreqs F, repCount G s := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : F => s = 0)
      (fun s => repCount G s)]
    congr 1
    · rw [Finset.filter_eq' Finset.univ 0, if_pos (Finset.mem_univ 0), Finset.sum_singleton]
    · apply Finset.sum_congr
      · ext s
        simp [nonzeroFreqs]
      · intro x hx
        rfl
  have hoff := sum_nonzero_repCount_eq_mul_sum_transversal hζprim hn hT
  rw [hsplit, hzero, hoff, hGcard] at hglobal
  rw [sum_transversalRepProfile]
  have hmul : n * (1 + ∑ t ∈ T, repCount (nthRootsFinset n (1 : F)) t) = n * n := by
    nlinarith
  have hcancel : 1 + ∑ t ∈ T, repCount (nthRootsFinset n (1 : F)) t = n :=
    Nat.mul_left_cancel hn hmul
  omega

/-- **HBK equation (9) on the ordered profile.** -/
theorem additiveEnergy_eq_card_sq_add_card_mul_profile_sq
    {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {T : Finset F} (hT : IsCosetTransversal n T)
    (hneg : ∀ x ∈ nthRootsFinset n (1 : F), -x ∈ nthRootsFinset n (1 : F)) :
    additiveEnergy (nthRootsFinset n (1 : F)) = n ^ 2 + n *
      (∑ i ∈ Finset.range T.card,
        transversalRepProfile (nthRootsFinset n (1 : F)) T i ^ 2) := by
  let G := nthRootsFinset n (1 : F)
  have hGcard : G.card = n := hζprim.card_nthRootsFinset
  have hzero : repCount G 0 = n := by
    rw [repCount_zero_eq_card hneg, hGcard]
  rw [additiveEnergy_eq_sum_repCount_sq]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : F => s = 0)
    (fun s => repCount G s ^ 2)]
  have hzeroFilter :
      ∑ s ∈ Finset.univ.filter (fun s : F => s = 0), repCount G s ^ 2 = n ^ 2 := by
    rw [Finset.filter_eq' Finset.univ 0, if_pos (Finset.mem_univ 0), Finset.sum_singleton, hzero]
  rw [hzeroFilter]
  have hnotFilter : Finset.univ.filter (fun s : F => ¬s = 0) = nonzeroFreqs F := by
    ext s
    simp [nonzeroFreqs]
  rw [hnotFilter]
  exact congrArg (n ^ 2 + ·) (sum_nonzero_repCount_sq_eq_mul_profile_sq hζprim hn hT)

/-- Production specialization of HBK equation (10). -/
theorem production_sum_transversal_profile_eq_card_sub_one
    {ζ : F} (hζprim : IsPrimitiveRoot ζ (2 ^ 30))
    {T : Finset F} (hT : IsCosetTransversal (2 ^ 30) T) :
    (∑ i ∈ Finset.range T.card,
      transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T i) = 2 ^ 30 - 1 := by
  apply sum_transversal_profile_eq_card_sub_one hζprim (by norm_num) hT
  intro x hx
  exact neg_mem_nthRootsFinset_of_even (by norm_num) (by norm_num) hx

/-- Production specialization of HBK equation (9). -/
theorem production_additiveEnergy_eq_card_sq_add_card_mul_profile_sq
    {ζ : F} (hζprim : IsPrimitiveRoot ζ (2 ^ 30))
    {T : Finset F} (hT : IsCosetTransversal (2 ^ 30) T) :
    additiveEnergy (nthRootsFinset (2 ^ 30) (1 : F)) =
      (2 ^ 30) ^ 2 + (2 ^ 30) *
        (∑ i ∈ Finset.range T.card,
          transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T i ^ 2) := by
  apply additiveEnergy_eq_card_sq_add_card_mul_profile_sq hζprim (by norm_num) hT
  intro x hx
  exact neg_mem_nthRootsFinset_of_even (by norm_num) (by norm_num) hx

end ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities

#print axioms
  ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities.repCount_eq_of_cosetLabel_eq
#print axioms
  ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities.sum_nonzero_repCount_sq_eq_mul_profile_sq
#print axioms
  ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities.sum_transversal_profile_eq_card_sub_one
#print axioms
  ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities.additiveEnergy_eq_card_sq_add_card_mul_profile_sq
#print axioms
  ArkLib.ProximityGap.Frontier.HBKRepCountMomentIdentities.production_additiveEnergy_eq_card_sq_add_card_mul_profile_sq
