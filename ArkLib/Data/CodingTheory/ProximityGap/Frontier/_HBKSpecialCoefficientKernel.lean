/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G117HBKFloorSafeParameters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKTransversalTopPrefix

/-!
# HBK special coefficient kernel

The special trivariate auxiliary has `A B²` coefficients `λ_{a,b,c}`.  Requiring every polynomial
`P_{m,u}(X)` (`m<D`, `u` in a `k`-element representative family) to vanish identically imposes at
most `D(A+D)k` scalar linear equations.  This file packages the exact finite-dimensional kernel
step and instantiates G117's strict inequality for every production prefix through `4096`.

This is the linear-algebra half of HBK Lemma 5; defining the concrete constraint map and proving its
kernel equations imply multiplicity are the next layer. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKSpecialCoefficientKernel

open Polynomial
open G117HBKFloorSafeParameters
open HBKTransversalTopPrefix
open ArkLib.ProximityGap.I031DilationOrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Abstract HBK coefficient space: the box `0≤a<A`, `0≤b,c<B`. -/
abbrev CoeffSpace (F : Type*) (A B : ℕ) := Fin A × Fin B × Fin B → F

/-- Abstract HBK constraint space: derivative order, polynomial coefficient, representative. -/
abbrev ConstraintSpace (F : Type*) (A D : ℕ) (U : Finset F) :=
  Fin D × Fin (A + D) × U → F

/-- More unknown coefficients than scalar equations force a nonzero coefficient tensor in the
kernel of *any* linear constraint map of the HBK shape. -/
theorem exists_nonzero_coefficient_kernel
    {A B D : ℕ} {U : Finset F}
    (hcount : D * (A + D) * U.card < A * B ^ 2)
    (L : CoeffSpace F A B →ₗ[F] ConstraintSpace F A D U) :
    ∃ coeffs : CoeffSpace F A B, coeffs ≠ 0 ∧ L coeffs = 0 := by
  classical
  have hdim : Module.finrank F (ConstraintSpace F A D U) <
      Module.finrank F (CoeffSpace F A B) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    simpa [pow_two, mul_assoc] using hcount
  have hni : ¬ Function.Injective L := by
    intro hinj
    exact (Nat.not_le_of_lt hdim) (LinearMap.finrank_le_finrank_of_injective hinj)
  rw [← LinearMap.ker_eq_bot] at hni
  obtain ⟨coeffs, hker, hne⟩ := (Submodule.ne_bot_iff _).mp hni
  exact ⟨coeffs, hne, LinearMap.mem_ker.mp hker⟩

/-- G117 supplies the strict dimension gap for the actual top-prefix representative family. -/
theorem production_exists_nonzero_coefficient_kernel
    {T : Finset F} (hT : IsCosetTransversal (2 ^ 30) T)
    {k : ℕ} (hk : 0 < k) (hkmax : k ≤ 4096) (hkT : k ≤ T.card)
    (L :
      let B := ceilCubeRoot (2 * (2 ^ 30) * k)
      let A := roundedA (2 ^ 30) B
      let D := roundedD (2 ^ 30) B
      CoeffSpace F A B →ₗ[F]
        ConstraintSpace F A D (topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k)) :
    let B := ceilCubeRoot (2 * (2 ^ 30) * k)
    let A := roundedA (2 ^ 30) B
    let D := roundedD (2 ^ 30) B
    ∃ coeffs : CoeffSpace F A B, coeffs ≠ 0 ∧ L coeffs = 0 := by
  dsimp only at L ⊢
  let B := ceilCubeRoot (2 * (2 ^ 30) * k)
  let A := roundedA (2 ^ 30) B
  let D := roundedD (2 ^ 30) B
  have hfeas := production_rounded_parameters_feasible hk
    (hkmax.trans (by norm_num : 4096 ≤ 2 ^ 30))
  dsimp only at hfeas
  have hcard :
      (topPrefix (nthRootsFinset (2 ^ 30) (1 : F)) T k).card = k :=
    topPrefix_card _ _ _ hkT
  apply exists_nonzero_coefficient_kernel
  rw [hcard]
  exact hfeas.2

end ArkLib.ProximityGap.Frontier.HBKSpecialCoefficientKernel

#print axioms ArkLib.ProximityGap.Frontier.HBKSpecialCoefficientKernel.exists_nonzero_coefficient_kernel
#print axioms ArkLib.ProximityGap.Frontier.HBKSpecialCoefficientKernel.production_exists_nonzero_coefficient_kernel
