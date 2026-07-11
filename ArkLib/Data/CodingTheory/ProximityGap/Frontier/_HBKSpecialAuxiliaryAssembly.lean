/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKAuxiliaryMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKSpecializationNonzero
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKProductionPrefixWeld
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Set.Finite.Basic

/-!
# Assembly of the HBK special auxiliary

This file closes the remaining packaging seam in the effective Heath--Brown--Konyagin argument.
It identifies the expanded auxiliary used by the multiplicity calculation with the valuation-block
specialization used by the nonvanishing theorem, proves its degree bound, and combines the concrete
coefficient kernel with both facts.

At the production scale, characteristic at least `2^52` is already far larger than every exponent
and derivative order used by the first `4096` prefix auxiliaries.  The resulting endpoint supplies
those auxiliaries to the ordered-prefix weld and proves the squared additive-energy bound consumed
by the production campaign. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKSpecialAuxiliaryAssembly

open scoped BigOperators
open Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.I031DilationOrbitReduction
open G117HBKFloorSafeParameters HBKSpecialCoefficientKernel HBKSpecializationNonzero
open HBKConcreteConstraintMap HBKAuxiliaryMultiplicity HBKNormalizedIncidenceUnion
open HBKTransversalTopPrefix HBKProductionPrefixWeld

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Every finite field admits a concrete finite transversal for the `cosetLabel` fibers. -/
theorem exists_isCosetTransversal (n : ℕ) :
    ∃ T : Finset F, IsCosetTransversal n T := by
  classical
  let f : F → Finset F := cosetLabel n
  let S : Finset F := nonzeroFreqs F
  let labels : Finset (Finset F) := S.image f
  have hsurj : Set.SurjOn f (S : Set F) (labels : Set (Finset F)) := by
    simpa [labels] using Set.surjOn_image f (S : Set F)
  obtain ⟨T, hTS, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (S : Set F) labels hsurj
  refine ⟨T, ⟨?_, ?_, ?_⟩⟩
  · intro t ht
    exact hTS (by simpa using ht)
  · intro b hb
    have hlabel : f b ∈ labels := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    rw [← himage] at hlabel
    obtain ⟨t, ht, htb⟩ := Finset.mem_image.mp hlabel
    exact ⟨t, ht, htb⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    exact hinj (by simpa using ht₁) (by simpa using ht₂) heq

/-- Reindex the expanded `(a,b,c)` box by the valuation block `c` and the paired index `(a,b)`. -/
private def auxiliaryIndexEquiv (A B : ℕ) :
    (Fin A × Fin B × Fin B) ≃ (Fin B × Fin (A * B)) where
  toFun p := (p.2.2, finProdFinEquiv (p.1, p.2.1))
  invFun q :=
    let ab := finProdFinEquiv.symm q.2
    (ab.1, ab.2, q.1)
  left_inv p := by simp
  right_inv q := by
    rcases q with ⟨c, j⟩
    change (c, finProdFinEquiv (finProdFinEquiv.symm j)) = (c, j)
    rw [Equiv.apply_symm_apply]

@[simp] private theorem auxiliaryIndexEquiv_apply (A B : ℕ)
    (p : Fin A × Fin B × Fin B) :
    auxiliaryIndexEquiv A B p = (p.2.2, finProdFinEquiv (p.1, p.2.1)) := rfl

/-- The expanded and valuation-block presentations are literally the same specialization. -/
theorem expandedAuxiliary_eq_specializedAuxiliary
    (h A B : ℕ) (coeffs : CoeffSpace F A B) :
    expandedAuxiliary h A B coeffs = specializedAuxiliary h A B coeffs := by
  classical
  unfold expandedAuxiliary specializedAuxiliary coefficientBlock
  simp_rw [Finset.mul_sum]
  let g : Fin B × Fin (A * B) → F[X] := fun q =>
    let ab := finProdFinEquiv.symm q.2
    (X - 1) ^ (h * (q.1 : ℕ)) *
      (C (coeffs (ab.1, ab.2, q.1)) * X ^ (ab.1 + h * ab.2))
  calc
    (∑ p : Fin A × Fin B × Fin B,
        C (coeffs p) * X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ)) *
          (X - 1) ^ (h * (p.2.2 : ℕ))) = ∑ q, g q := by
      apply Fintype.sum_equiv (auxiliaryIndexEquiv A B)
      intro p
      rw [auxiliaryIndexEquiv_apply]
      dsimp only [g]
      rw [Equiv.symm_apply_apply]
      rw [pow_add]
      ring
    _ = ∑ c : Fin B, ∑ j : Fin (A * B), g (c, j) := Fintype.sum_prod_type g
    _ = ∑ c : Fin B, ∑ j : Fin (A * B),
        (X - 1) ^ (h * (c : ℕ)) *
          (C (coeffs ((finProdFinEquiv.symm j).1,
            (finProdFinEquiv.symm j).2, c)) * X ^ specializedExponent h A B j) := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [g]
      rw [show specializedExponent h A B j =
        ((finProdFinEquiv.symm j).1 : ℕ) +
          h * ((finProdFinEquiv.symm j).2 : ℕ) by rfl]

/-- Every monomial in the special box has degree at most `A + 2hB - 1`. -/
theorem natDegree_expandedAuxiliary_le
    {h A B : ℕ} (hA : 0 < A) (coeffs : CoeffSpace F A B) :
    (expandedAuxiliary h A B coeffs).natDegree ≤ A + 2 * h * B - 1 := by
  classical
  unfold expandedAuxiliary
  apply natDegree_sum_le_of_forall_le
  intro p _
  have hsub : ((X - (1 : F[X])) ^ (h * (p.2.2 : ℕ))).natDegree ≤
      h * (p.2.2 : ℕ) := by
    calc
      ((X - (1 : F[X])) ^ (h * (p.2.2 : ℕ))).natDegree
          ≤ (h * (p.2.2 : ℕ)) * (X - (1 : F[X])).natDegree := natDegree_pow_le
      _ = h * (p.2.2 : ℕ) := by
        rw [show (1 : F[X]) = C (1 : F) by simp, natDegree_X_sub_C]
        simp
  have hmulTop :
      (X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ)) *
        (X - (1 : F[X])) ^ (h * (p.2.2 : ℕ))).natDegree ≤
        (X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ))).natDegree +
          ((X - (1 : F[X])) ^ (h * (p.2.2 : ℕ))).natDegree :=
    natDegree_mul_le
  have hmulAB :
      ((X : F[X]) ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ))).natDegree ≤
        ((X : F[X]) ^ (p.1 : ℕ)).natDegree +
          ((X : F[X]) ^ (h * (p.2.1 : ℕ))).natDegree := natDegree_mul_le
  rw [show
    C (coeffs p) * X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ)) *
        (X - (1 : F[X])) ^ (h * (p.2.2 : ℕ)) =
      C (coeffs p) *
        (X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ)) *
          (X - (1 : F[X])) ^ (h * (p.2.2 : ℕ))) by ring]
  apply le_trans (natDegree_C_mul_le _ _)
  apply le_trans hmulTop
  apply le_trans (Nat.add_le_add hmulAB hsub)
  rw [natDegree_X_pow, natDegree_X_pow]
  have ha := p.1.isLt
  have hb := p.2.1.isLt
  have hc := p.2.2.isLt
  have hb' : h * (p.2.1 : ℕ) ≤ h * B := Nat.mul_le_mul_left h hb.le
  have hc' : h * (p.2.2 : ℕ) ≤ h * B := Nat.mul_le_mul_left h hc.le
  have hsum : (p.1 : ℕ) + h * (p.2.1 : ℕ) + h * (p.2.2 : ℕ) <
      A + h * B + h * B := by omega
  have heq : A + 2 * h * B = A + h * B + h * B := by ring
  rw [heq]
  omega

/-- A prime characteristic larger than the derivative order makes the relevant factorial a unit. -/
theorem factorial_isUnit_of_lt_charP
    {p D : ℕ} [CharP F p] (hp : p.Prime) (hD : D ≤ p) :
    IsUnit ((((D - 1).factorial : ℕ) : F)) := by
  rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff F p]
  intro hdvd
  have hle : p ≤ D - 1 := (Nat.Prime.dvd_factorial hp).mp hdvd
  have hp2 := hp.two_le
  omega

/-- The abstract HBK dimension gap produces a nonzero, bounded-degree auxiliary with multiplicity
`D` throughout the normalized incidence union. -/
theorem exists_special_auxiliary_of_dimension_gap
    {p h A B D : ℕ} [CharP F p] (hp : p.Prime)
    (hh : 0 < h) (hApos : 0 < A)
    (hA : A ≤ h) (hAB : A * B ≤ h) (hchar : A + h * B ≤ p) (hD : D ≤ p)
    {U : Finset F} (hU0 : ∀ u ∈ U, u ≠ 0)
    (hcount : D * (A + D) * U.card < A * B ^ 2) :
    ∃ Ψ : F[X], Ψ ≠ 0 ∧
      (∀ x ∈ incidenceUnion (nthRootsFinset h (1 : F)) U,
        D ≤ Ψ.rootMultiplicity x) ∧
      Ψ.natDegree ≤ A + 2 * h * B - 1 := by
  let L := constraintMap h A B D U
  obtain ⟨coeffs, hcoeffs, hker⟩ :=
    exists_nonzero_coefficient_kernel hcount L
  refine ⟨expandedAuxiliary h A B coeffs, ?_, ?_,
    natDegree_expandedAuxiliary_le hApos coeffs⟩
  · rw [expandedAuxiliary_eq_specializedAuxiliary]
    exact HBKSpecializationNonzero.specializedAuxiliary_ne_zero_of_charP
      hA hAB hchar hcoeffs
  · intro x hx
    apply le_rootMultiplicity_on_incidenceUnion_of_mem_ker hh hU0
    · rw [expandedAuxiliary_eq_specializedAuxiliary]
      exact HBKSpecializationNonzero.specializedAuxiliary_ne_zero_of_charP
        hA hAB hchar hcoeffs
    · exact factorial_isUnit_of_lt_charP hp hD
    · exact hker
    · exact hx

/-- For every production prefix through `4096`, the floor-safe HBK parameters admit the required
special auxiliary as soon as the prime characteristic is at least `2^52`. -/
theorem production_exists_special_auxiliary
    {p : ℕ} [CharP F p] (hp : p.Prime) (hpLarge : 2 ^ 52 ≤ p)
    {T : Finset F} (hT : IsCosetTransversal (2 ^ 30) T)
    {k : ℕ} (hk : 0 < k) (hkmax : k ≤ 4096) (hkT : k ≤ T.card) :
    let U := topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k
    let B := ceilCubeRoot (2 * (2 ^ 30) * k)
    let A := roundedA (2 ^ 30) B
    let D := roundedD (2 ^ 30) B
    ∃ Ψ : F[X], Ψ ≠ 0 ∧
      (∀ x ∈ incidenceUnion (nthRootsFinset (2 ^ 30) (1 : F)) U,
        D ≤ Ψ.rootMultiplicity x) ∧
      Ψ.natDegree ≤ A + 2 * (2 ^ 30) * B - 1 := by
  dsimp only
  let U := topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k
  let B := ceilCubeRoot (2 * (2 ^ 30) * k)
  let A := roundedA (2 ^ 30) B
  let D := roundedD (2 ^ 30) B
  have hkH : k ≤ 2 ^ 30 := hkmax.trans (by norm_num)
  have hfeas := production_rounded_parameters_feasible hk hkH
  dsimp only at hfeas
  have hBpos : 0 < B := by simp [B, ceilCubeRoot]
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num : 0 < 32)
    (production_roundedA_ge_thirtyTwo hkH)
  have hBbound : B ≤ 2 ^ 16 := by
    have hx : 2 * (2 ^ 30) * k < (2 ^ 16) ^ 3 := by
      calc
        2 * (2 ^ 30) * k ≤ 2 * (2 ^ 30) * 4096 := Nat.mul_le_mul_left _ hkmax
        _ < (2 ^ 16) ^ 3 := by norm_num
    have hroot := (Nat.nthRoot_lt_iff (by norm_num : (3 : ℕ) ≠ 0)).2 hx
    change Nat.nthRoot 3 (2 * (2 ^ 30) * k) + 1 ≤ 2 ^ 16
    exact Nat.succ_le_iff.mpr hroot
  have hAle : A ≤ 2 ^ 30 := by
    calc
      A ≤ A * B := Nat.le_mul_of_pos_right A hBpos
      _ ≤ 2 ^ 30 := hfeas.1
  have hchar : A + (2 ^ 30) * B ≤ p := by
    calc
      A + (2 ^ 30) * B ≤ (2 ^ 30) + (2 ^ 30) * (2 ^ 16) :=
        Nat.add_le_add hAle (Nat.mul_le_mul_left _ hBbound)
      _ ≤ 2 ^ 52 := by norm_num
      _ ≤ p := hpLarge
  have hD : D ≤ p := by
    calc
      D ≤ A := by
        dsimp [D, A]
        exact Nat.sub_le _ _
      _ ≤ A + (2 ^ 30) * B := Nat.le_add_right _ _
      _ ≤ p := hchar
  have hUcard : U.card = k := topPrefix_card _ _ _ hkT
  have hU0 : ∀ u ∈ U, u ≠ 0 := by
    intro u hu
    have huT := topPrefix_subset (nthRootsFinset (2 ^ 30) (1 : F)) T k hu
    exact mem_nonzeroFreqs.mp (hT.subset huT)
  apply exists_special_auxiliary_of_dimension_gap hp (by norm_num) hApos hAle
    hfeas.1 hchar hD hU0
  rw [hUcard]
  exact hfeas.2

/-- **Effective production HBK energy theorem.**  The special auxiliaries are now constructed, so
the `4096`-prefix weld has no remaining auxiliary hypothesis. -/
theorem production_energy_sq_le
    {p : ℕ} [CharP F p] (hp : p.Prime) (hpLarge : 2 ^ 52 ≤ p)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ 30)) {T : Finset F}
    (hT : IsCosetTransversal (2 ^ 30) T) (hTcard : 2 ^ 30 ≤ T.card) :
    additiveEnergy (nthRootsFinset (2 ^ 30) (1 : F)) ^ 2 ≤
      128 * (2 ^ 30) ^ 5 := by
  apply production_energy_sq_le_of_auxiliaries_to_4096 hζ hT hTcard
  intro k hk hkmax
  exact production_exists_special_auxiliary hp hpLarge hT hk hkmax
    (hkmax.trans (by norm_num : 4096 ≤ 2 ^ 30) |>.trans hTcard)

/-- Transversal-free form: a field with at least `(2^30)^2+1` elements has enough multiplicative
cosets to run the effective production HBK bound. -/
theorem production_energy_sq_le_of_card
    {p : ℕ} [CharP F p] (hp : p.Prime) (hpLarge : 2 ^ 52 ≤ p)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ 30))
    (hcard : (2 ^ 30) ^ 2 ≤ Fintype.card F - 1) :
    additiveEnergy (nthRootsFinset (2 ^ 30) (1 : F)) ^ 2 ≤
      128 * (2 ^ 30) ^ 5 := by
  obtain ⟨T, hT⟩ := exists_isCosetTransversal (F := F) (2 ^ 30)
  apply production_energy_sq_le hp hpLarge hζ hT
  rw [transversal_card hζ (by norm_num) hT]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2 ^ 30)).2
  simpa [pow_two] using hcard

end ArkLib.ProximityGap.Frontier.HBKSpecialAuxiliaryAssembly

#print axioms
  ArkLib.ProximityGap.Frontier.HBKSpecialAuxiliaryAssembly.expandedAuxiliary_eq_specializedAuxiliary
#print axioms
  ArkLib.ProximityGap.Frontier.HBKSpecialAuxiliaryAssembly.exists_special_auxiliary_of_dimension_gap
#print axioms
  ArkLib.ProximityGap.Frontier.HBKSpecialAuxiliaryAssembly.production_exists_special_auxiliary
#print axioms
  ArkLib.ProximityGap.Frontier.HBKSpecialAuxiliaryAssembly.production_energy_sq_le
#print axioms
  ArkLib.ProximityGap.Frontier.HBKSpecialAuxiliaryAssembly.production_energy_sq_le_of_card
