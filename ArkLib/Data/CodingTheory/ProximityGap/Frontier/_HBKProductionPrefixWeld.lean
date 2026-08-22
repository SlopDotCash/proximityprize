/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G118HBKPrefixFromAuxiliary
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKNormalizedIncidenceUnion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKCubeRootIncrementBounds
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKProductionCapMajorization

/-!
# Production HBK prefix weld

This file applies G118 to the *actual* HBK normalized incidence union attached to the top ordered
transversal representatives.  It then converts the cube inequality into the real cube-root cap and
shows that auxiliaries are needed only through the saturation index `4096`; all later prefixes are
bounded by the exact total mass from HBK equation (10).  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKProductionPrefixWeld

open scoped BigOperators
open Polynomial
open ArkLib.CodingTheory.Round6Stepanov
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.I031DilationOrbitReduction
open HBKTransversalRepProfile HBKTransversalTopPrefix HBKNormalizedIncidenceUnion
open HBKRepCountMomentIdentities HBKCubeRootIncrementBounds
open HBKOrderedNatProfile HBKProductionCapMajorization
open G117HBKFloorSafeParameters G118HBKPrefixFromAuxiliary

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- G118 applied to the genuine normalized union: its cardinality is the ordered profile prefix. -/
theorem production_profile_prefix_cube_le_of_auxiliary
    {T : Finset F} (hT : IsCosetTransversal (2 ^ 30) T)
    {k : ℕ} (hk : 0 < k) (hkT : k ≤ T.card) (hkmax : k ≤ 2 ^ 30)
    (hex :
      let E := incidenceUnion (nthRootsFinset (2 ^ 30) (1 : F))
        (topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k)
      let B := ceilCubeRoot (2 * (2 ^ 30) * k)
      let A := roundedA (2 ^ 30) B
      let D := roundedD (2 ^ 30) B
      ∃ Ψ : F[X], Ψ ≠ 0 ∧
        (∀ x ∈ E, D ≤ Ψ.rootMultiplicity x) ∧
        Ψ.natDegree ≤ A + 2 * (2 ^ 30) * B - 1) :
    (∑ i ∈ Finset.range k,
      transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T i) ^ 3 ≤
      64 * ((2 ^ 30) * k) ^ 2 := by
  let E := incidenceUnion (nthRootsFinset (2 ^ 30) (1 : F))
    (topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k)
  have hE := production_card_cube_le_of_auxiliary E hk hkmax hex
  rw [incidenceUnion_topPrefix_card (by norm_num) (by norm_num) hT hkT] at hE
  exact hE

/-- Cube-free coefficient-4 form of the genuine prefix bound. -/
theorem production_profile_prefix_real_le_of_auxiliary
    {T : Finset F} (hT : IsCosetTransversal (2 ^ 30) T)
    {k : ℕ} (hk : 0 < k) (hkT : k ≤ T.card) (hkmax : k ≤ 2 ^ 30)
    (hex :
      let E := incidenceUnion (nthRootsFinset (2 ^ 30) (1 : F))
        (topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k)
      let B := ceilCubeRoot (2 * (2 ^ 30) * k)
      let A := roundedA (2 ^ 30) B
      let D := roundedD (2 ^ 30) B
      ∃ Ψ : F[X], Ψ ≠ 0 ∧
        (∀ x ∈ E, D ≤ Ψ.rootMultiplicity x) ∧
        Ψ.natDegree ≤ A + 2 * (2 ^ 30) * B - 1) :
    ((∑ i ∈ Finset.range k,
      transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T i : ℕ) : ℝ) ≤
      (4 * 2 ^ 20 : ℝ) * natCubeRoot k ^ 2 := by
  let S : ℕ := ∑ i ∈ Finset.range k,
    transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T i
  let C : ℝ := (4 * 2 ^ 20 : ℝ) * natCubeRoot k ^ 2
  have hcubeNat : S ^ 3 ≤ 64 * ((2 ^ 30) * k) ^ 2 :=
    production_profile_prefix_cube_le_of_auxiliary hT hk hkT hkmax hex
  have hCcube : C ^ 3 = (64 : ℝ) * (((2 ^ 30) * k : ℕ) : ℝ) ^ 2 := by
    calc
      C ^ 3 = (4 * 2 ^ 20 : ℝ) ^ 3 * (natCubeRoot k ^ 3) ^ 2 := by
        dsimp [C]
        ring
      _ = (4 * 2 ^ 20 : ℝ) ^ 3 * (k : ℝ) ^ 2 := by rw [natCubeRoot_cube]
      _ = (64 : ℝ) * (((2 ^ 30) * k : ℕ) : ℝ) ^ 2 := by
        push_cast
        norm_num
        ring
  have hcube : (S : ℝ) ^ 3 ≤ C ^ 3 := by
    rw [hCcube]
    exact_mod_cast hcubeNat
  have hS0 : 0 ≤ (S : ℝ) := by positivity
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have : (S : ℝ) ≤ C :=
    (pow_le_pow_iff_left₀ hS0 hC0 (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  exact this

/-- **Only the first 4096 auxiliaries are needed.**  Those give the unsaturated cube-root cap;
every later prefix is at most the total profile mass `2^30-1`, while the cap has saturated at
exactly `2^30`. -/
theorem production_all_prefixes_le_cap_of_auxiliaries_to_4096
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ 30)) {T : Finset F}
    (hT : IsCosetTransversal (2 ^ 30) T) (hTcard : 2 ^ 30 ≤ T.card)
    (haux : ∀ k : ℕ, 0 < k → k ≤ 4096 →
      let E := incidenceUnion (nthRootsFinset (2 ^ 30) (1 : F))
        (topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k)
      let B := ceilCubeRoot (2 * (2 ^ 30) * k)
      let A := roundedA (2 ^ 30) B
      let D := roundedD (2 ^ 30) B
      ∃ Ψ : F[X], Ψ ≠ 0 ∧
        (∀ x ∈ E, D ≤ Ψ.rootMultiplicity x) ∧
        Ψ.natDegree ≤ A + 2 * (2 ^ 30) * B - 1) :
    ∀ i < 2 ^ 30,
      ((∑ j ∈ Finset.range (i + 1),
        transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T j : ℕ) : ℝ) ≤
        ∑ j ∈ Finset.range (i + 1), productionCapIncrement j := by
  intro i hi
  let k := i + 1
  have hk : 0 < k := by omega
  have hkmax : k ≤ 2 ^ 30 := by omega
  have hkT : k ≤ T.card := hkmax.trans hTcard
  by_cases hksat : k ≤ 4096
  · rw [sum_productionCapIncrement hksat]
    exact production_profile_prefix_real_le_of_auxiliary hT hk hkT hkmax
      (haux k hk hksat)
  · have h4096 : 4096 ≤ k := by omega
    rw [sum_productionCapIncrement_eq_full_of_ge h4096]
    have hprefixNat :
        (∑ j ∈ Finset.range k,
          transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T j) ≤ 2 ^ 30 - 1 := by
      calc
        _ ≤ ∑ j ∈ Finset.range T.card,
            transversalRepProfile (nthRootsFinset (2 ^ 30) (1 : F)) T j :=
          Finset.sum_le_sum_of_subset (Finset.range_mono hkT)
        _ = 2 ^ 30 - 1 := sum_transversal_profile_eq_card_sub_one hζ (by norm_num) hT
          (fun x hx => neg_mem_nthRootsFinset_of_even (by norm_num) (by norm_num) hx)
    exact_mod_cast hprefixNat.trans (by omega : 2 ^ 30 - 1 ≤ 2 ^ 30)

/-- **End-to-end HBK anchor theorem.**  Special auxiliaries for only the first `4096` normalized
prefix unions imply the production additive-energy target consumed by G97. -/
theorem production_energy_sq_le_of_auxiliaries_to_4096
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ 30)) {T : Finset F}
    (hT : IsCosetTransversal (2 ^ 30) T) (hTcard : 2 ^ 30 ≤ T.card)
    (haux : ∀ k : ℕ, 0 < k → k ≤ 4096 →
      let E := incidenceUnion (nthRootsFinset (2 ^ 30) (1 : F))
        (topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k)
      let B := ceilCubeRoot (2 * (2 ^ 30) * k)
      let A := roundedA (2 ^ 30) B
      let D := roundedD (2 ^ 30) B
      ∃ Ψ : F[X], Ψ ≠ 0 ∧
        (∀ x ∈ E, D ≤ Ψ.rootMultiplicity x) ∧
        Ψ.natDegree ≤ A + 2 * (2 ^ 30) * B - 1) :
    additiveEnergy (nthRootsFinset (2 ^ 30) (1 : F)) ^ 2 ≤
      128 * (2 ^ 30) ^ 5 := by
  let G := nthRootsFinset (2 ^ 30) (1 : F)
  let a := transversalRepProfile G T
  have hprefix := production_all_prefixes_le_cap_of_auxiliaries_to_4096
    hζ hT hTcard haux
  have haN : a (2 ^ 30) = 0 := by
    by_cases heq : T.card = 2 ^ 30
    · exact transversalRepProfile_boundary G T heq.le
    · change orderedProfile (transversalRepMultiset G T) (2 ^ 30) = 0
      apply orderedProfile_eq_zero_of_sum_lt
      · simpa [transversalRepMultiset_card] using lt_of_le_of_ne hTcard (Ne.symm heq)
      · have hmass := production_sum_transversal_profile_eq_card_sub_one hζ hT
        rw [transversalRepProfile, ← transversalRepMultiset_card,
          sum_orderedProfile] at hmass
        rw [hmass]
        norm_num
  have hadrop : ∀ i < 2 ^ 30, a (i + 1) ≤ a i := by
    intro i _
    exact transversalRepProfile_antitone_succ G T i
  have htail : ∀ i, 2 ^ 30 ≤ i → a i = 0 := by
    intro i hi
    apply Nat.eq_zero_of_le_zero
    calc
      a i ≤ a (2 ^ 30) := orderedProfile_antitone (transversalRepMultiset G T) hi
      _ = 0 := haN
  have hsumsq :
      (∑ i ∈ Finset.range T.card, a i ^ 2) =
        ∑ i ∈ Finset.range (2 ^ 30), a i ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.range_mono hTcard)
    intro i hiT hin
    have hi : 2 ^ 30 ≤ i := by
      by_contra h
      exact hin (Finset.mem_range.mpr (by omega))
    simp [htail i hi]
  have henergy : additiveEnergy G = (2 ^ 30) ^ 2 + (2 ^ 30) *
      (∑ i ∈ Finset.range (2 ^ 30), a i ^ 2) := by
    rw [← hsumsq]
    exact production_additiveEnergy_eq_card_sq_add_card_mul_profile_sq hζ hT
  exact production_energy_sq_le_of_profile a (additiveEnergy G) haN hadrop hprefix henergy

end ArkLib.ProximityGap.Frontier.HBKProductionPrefixWeld

#print axioms ArkLib.ProximityGap.Frontier.HBKProductionPrefixWeld.production_profile_prefix_cube_le_of_auxiliary
#print axioms ArkLib.ProximityGap.Frontier.HBKProductionPrefixWeld.production_profile_prefix_real_le_of_auxiliary
#print axioms ArkLib.ProximityGap.Frontier.HBKProductionPrefixWeld.production_all_prefixes_le_cap_of_auxiliaries_to_4096
#print axioms ArkLib.ProximityGap.Frontier.HBKProductionPrefixWeld.production_energy_sq_le_of_auxiliaries_to_4096
