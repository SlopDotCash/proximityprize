/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DiscriminantFactorSplit
import ArkLib.Research.ProximityGap.Frontier.TameLogarithmicDVR
import ArkLib.Research.ProximityGap.Frontier.UnramifiedDerivationDVR
import ArkLib.Research.ProximityGap.Frontier.GenericDifferentialFunctionField
import ArkLib.Research.ProximityGap.Frontier.HeightOneNormalization
import ArkLib.Research.ProximityGap.Frontier.RepeatedSectionSpecialization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable

/-! # Branchwise regularity of logarithmic derivations on plane curves

This module implements Worker Packet L1b for the purely algebraic logarithmic section-height
engine:
1. Base derivations `∂_Z` (`partialZ`), `∂_X` (`partialX`), and the logarithmic derivations
   `δ₁ = H̃ ∂_Z` (`logDerivZ`) and `δ₂ = U (H̃_X ∂_Z - H̃_Z ∂_X)` (`logDerivJac`) on `K[X][X]`.
2. Proof that `δ₁` and `δ₂` preserve every prime divisor `p ∣ V(Z) * U(X) * H(X, Z)` when
   `H̃ = V(Z) * H(X, Z)`.
3. Lifting any base derivation `δ` on `K[X][X]` to the function field `Curve F` via
   `GenericDifferentialFunctionField.{fractionDifferential, adjointDifferential}` and proving
   `HeightOneNormalization.regularOnPlaneBranches F D` whenever `δ` is logarithmic on every
   prime divisor of `F.discr`, using `UnramifiedDerivationDVR.unramified_lift` off `F.discr`
   and `TameLogarithmicDVR.tame_logarithmic_lift` on `p ∣ F.discr`.
4. Explicit section-denominator divisibility corollaries for `D₁` and `D₂` on every simple
   section `(z, q)` of `F`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial IsDedekindDomain
open ArkLib.ProximityGap.NormalizedSectionSpecialization
open ArkLib.ProximityGap.HeightOneNormalization
open ArkLib.ProximityGap.RepeatedSectionSpecialization
open ArkLib.ProximityGap.Frontier.DiscriminantFactorSplit
open ArkLib.ProximityGap.Frontier.GenericDifferentialFunctionField
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.PlaneBranchRegularity

/-! ## Section 1: Base logarithmic derivations on `K[X][X]` -/

section BaseDerivations

variable {K : Type*} [Field K]

/-- Scalar differentiation `∂_Z` on `K[X][X]` (outer polynomial variable). -/
def partialZ (K : Type*) [Field K] : Derivation ℤ K[X][X] K[X][X] :=
  scalarDerivative K[X]

/-- Coordinate differentiation `∂_X` on `K[X][X]` (acting coefficientwise on `K[X]`). -/
def partialX (K : Type*) [Field K] : Derivation ℤ K[X][X] K[X][X] :=
  let _ : Differential K[X] := ⟨Polynomial.derivative'.restrictScalars ℤ⟩
  Differential.mapCoeffs

@[simp] theorem partialZ_apply (P : K[X][X]) : partialZ K P = P.derivative := rfl

@[simp] theorem coeff_partialX (P : K[X][X]) (i : ℕ) :
    (partialX K P).coeff i = (P.coeff i).derivative := by
  let _ : Differential K[X] := ⟨Polynomial.derivative'.restrictScalars ℤ⟩
  exact Differential.coeff_mapCoeffs P i

@[simp] theorem partialX_C (u : K[X]) : partialX K (C u) = C u.derivative := by
  ext i
  rw [coeff_partialX, coeff_C, coeff_C]
  split_ifs <;> simp

@[simp] theorem partialX_X : partialX K (X : K[X][X]) = 0 := by
  ext i
  rw [coeff_partialX, coeff_X, coeff_zero]
  split_ifs <;> simp

@[simp] theorem partialX_map_C (v : K[X]) : partialX K (v.map C) = 0 := by
  apply Polynomial.ext
  intro i
  rw [coeff_partialX, coeff_map, derivative_C, coeff_zero]

@[simp] theorem partialZ_C (u : K[X]) : partialZ K (C u) = 0 := by
  rw [partialZ_apply, derivative_C]

theorem eval_partialX_C (P : K[X][X]) (z : K) :
    (partialX K P).eval (C z) = (P.eval (C z)).derivative := by
  induction P using Polynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n u ih =>
    rw [pow_succ, ← mul_assoc, (partialX K).leibniz, partialX_X, smul_eq_mul, smul_eq_mul,
      mul_zero, zero_add, eval_mul, eval_mul, eval_X, ih, derivative_mul, derivative_C,
      mul_zero, add_zero, mul_comm]

theorem swap_partialX (P : K[X][X]) :
    Bivariate.swap (partialX K P) = (Bivariate.swap P).derivative := by
  induction P using Polynomial.induction_on with
  | C u =>
    rw [partialX_C, Bivariate.swap_C, Bivariate.swap_C, derivative_map]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | monomial n u ih =>
    rw [pow_succ, ← mul_assoc, (partialX K).leibniz, partialX_X, smul_eq_mul, smul_eq_mul,
      mul_zero, zero_add, map_mul (Bivariate.swap (R := K)), map_mul (Bivariate.swap (R := K)),
      ih, derivative_mul]
    have hswapX : (Bivariate.swap (X : K[X][X])).derivative = 0 := by
      rw [Bivariate.swap_Y, derivative_C]
    rw [hswapX, mul_zero, add_zero, mul_comm]

/-- First base logarithmic derivation `δ₁ = H̃ ∂_Z`. -/
def logDerivZ (Htilde : K[X][X]) : Derivation ℤ K[X][X] K[X][X] :=
  Htilde • partialZ K

/-- Second base logarithmic derivation `δ₂ = U (H̃_X ∂_Z - H̃_Z ∂_X)`. -/
def logDerivJac (U : K[X]) (Htilde : K[X][X]) : Derivation ℤ K[X][X] K[X][X] :=
  C U • (partialX K Htilde • partialZ K - partialZ K Htilde • partialX K)

@[simp] theorem logDerivZ_apply (Htilde P : K[X][X]) :
    logDerivZ Htilde P = Htilde * P.derivative := rfl

@[simp] theorem logDerivJac_apply (U : K[X]) (Htilde P : K[X][X]) :
    logDerivJac U Htilde P =
      C U * (partialX K Htilde * P.derivative - Htilde.derivative * partialX K P) := rfl

/-- `δ₁ = (V(Z) H(X, Z)) ∂_Z` is logarithmic on every prime dividing `V(Z) U(X) H(X, Z)`. -/
theorem dvd_logDerivZ_of_dvd_split {V U : K[X]} {H p : K[X][X]}
    (hU : U ≠ 0) (hp : Prime p) (hdvd : p ∣ V.map C * C U * H) :
    p ∣ logDerivZ (V.map C * H) p := by
  have hdvd' : p ∣ (V.map C * H) * C U := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdvd
  rcases hp.dvd_or_dvd hdvd' with h1 | h2
  · rw [logDerivZ_apply]
    exact dvd_mul_of_dvd_left h1 _
  · have hdeg : p.natDegree = 0 := by
      have hle := natDegree_le_of_dvd h2 (C_ne_zero.mpr hU)
      rw [natDegree_C] at hle
      omega
    have hp0 : p.derivative = 0 := by
      rw [eq_C_of_natDegree_eq_zero hdeg, derivative_C]
    rw [logDerivZ_apply, hp0, mul_zero]
    exact dvd_zero p

/-- `δ₂ = U (H̃_X ∂_Z - H̃_Z ∂_X)` is logarithmic on every prime dividing `V(Z) U(X) H(X, Z)`. -/
theorem dvd_logDerivJac_of_dvd_split {V U : K[X]} {H p : K[X][X]}
    (hp : Prime p) (hdvd : p ∣ V.map C * C U * H) :
    p ∣ logDerivJac U (V.map C * H) p := by
  have hdvd' : p ∣ (V.map C * H) * C U := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdvd
  rcases hp.dvd_or_dvd hdvd' with ⟨Q, hQ⟩ | h2
  · rw [logDerivJac_apply, hQ, (partialX K).leibniz, derivative_mul]
    simp only [smul_eq_mul]
    refine ⟨C U * (partialX K Q * p.derivative - Q.derivative * partialX K p), ?_⟩
    ring
  · rw [logDerivJac_apply]
    exact dvd_mul_of_dvd_left h2 _

/-- Chain rule for `∂_X` along a specialization `z : K`, `q : K[X]`. -/
theorem section_chain_partialX (F : K[X][X][X]) (z : K) (q : K[X]) :
    ((F.map (evalRingHom (C z))).eval q).derivative =
      ((coefficientDerivative (partialX K) F).map (evalRingHom (C z))).eval q +
        ((F.derivative.map (evalRingHom (C z))).eval q) * q.derivative := by
  have h := coefficient_chain (evalRingHom (C z)) (partialX K)
    (Polynomial.derivative'.restrictScalars ℤ) (fun c => (eval_partialX_C c z).symm) q F
  simpa only [eval_map, Derivation.restrictScalars_apply, derivative'_apply] using h

end BaseDerivations

/-! ## Section 2: Lifting base derivations and proving `regularOnPlaneBranches` -/

section PlaneRegularity

attribute [local instance high] Algebra.toSMul

variable {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L] [IsFractionRing R L]

private noncomputable abbrev polyFracAlg (k : Type*) [Field k] :
    Algebra k[X] (FractionRing k[X]) := inferInstance

local instance planeFracAlg : Algebra R[X] (FractionRing L[X]) :=
  (genericCoeffs (R := R) (L := L)).toAlgebra

omit [IsDomain R] in
private theorem planeFrac : IsFractionRing R[X] (FractionRing L[X]) := by
  let _ : Algebra R[X] L[X] := Polynomial.algebra R L
  let _ : Algebra L[X] (FractionRing L[X]) := polyFracAlg L
  let _ : Algebra R[X] (FractionRing L[X]) := planeFracAlg
  let _ : IsScalarTower R[X] L[X] (FractionRing L[X]) := IsScalarTower.of_algebraMap_eq' rfl
  let M := (nonZeroDivisors R).map (Polynomial.C : R →+* R[X])
  let _ : IsLocalization M L[X] := Polynomial.isLocalization _ _
  have hi : Function.Injective (algebraMap R[X] L[X]) :=
    Polynomial.map_injective _ (IsFractionRing.injective R L)
  have hm : (nonZeroDivisors L[X]).comap (algebraMap R[X] L[X]) = nonZeroDivisors R[X] :=
    le_antisymm (comap_nonZeroDivisors_le_of_injective hi)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hi)
  rw [IsFractionRing, ← hm]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors L[X]) _ fun _ h ↦ h.mem_nonZeroDivisors

attribute [local instance] planeFrac

local instance curveFin (F : R[X][X])
    [h : Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))] :
    FiniteDimensional (FractionRing L[X]) (Curve (L := L) F) :=
  (AdjoinRoot.powerBasis h.out.ne_zero).finite

/-- Gauss's lemma: an irreducible polynomial `F : K[X][X][X]` of positive `Y`-degree remains
irreducible over `FractionRing L[X]`. -/
theorem irreducible_map_genericCoeffs {K L : Type*} [Field K] [Field L]
    [Algebra K[X] L] [IsFractionRing K[X] L]
    (F : K[X][X][X]) (hFirr : Irreducible F) (hpos : 0 < F.natDegree) :
    Irreducible (F.map (genericCoeffs (R := K[X]) (L := L))) := by
  have hprim : F.IsPrimitive := hFirr.isPrimitive hpos.ne'
  exact (hprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing L[X])).mp hFirr

private def castIntDerivation {E : Type*} [CommRing E] {a₁ a₂ : Algebra ℤ E}
    (D : @Derivation ℤ E E _ _ _ a₁ _ _) : @Derivation ℤ E E _ _ _ a₂ _ _ :=
  Subsingleton.elim a₁ a₂ ▸ D

private lemma castIntDerivation_apply {E : Type*} [CommRing E] {a₁ a₂ : Algebra ℤ E}
    (D : @Derivation ℤ E E _ _ _ a₁ _ _) (x : E) :
    castIntDerivation (a₂ := a₂) D x = D x := by
  obtain rfl : a₁ = a₂ := Subsingleton.elim a₁ a₂
  rfl

omit [IsDomain R] in
/-- Separability of `Curve F / FractionRing L[X]` from `F.derivative ≠ 0`. -/
theorem curveSeparable_of_derivative_ne_zero (F : R[X][X])
    [h : Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    (hder : F.derivative ≠ 0) :
    Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F) := by
  let i := genericCoeffs (R := R) (L := L)
  have hi : Function.Injective i := IsFractionRing.injective R[X] (FractionRing L[X])
  have hs : (F.map i).Separable := (Polynomial.separable_iff_derivative_ne_zero h.out).mpr (by
    intro hz
    rw [Polynomial.derivative_map, Polynomial.map_eq_zero_iff hi] at hz
    exact hder hz)
  have hy : AdjoinRoot.root (F.map i) ∈ separableClosure (FractionRing L[X]) (Curve (L := L) F) :=
    mem_separableClosure_iff.mpr (hs.of_dvd (minpoly.dvd _ _
      (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])))
  constructor
  intro x
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := F.map i) x
  apply mem_separableClosure_iff.mp
  rw [← AdjoinRoot.aeval_eq]
  exact Algebra.adjoin_singleton_le (S := (separableClosure _ _).toSubalgebra) hy
    (g.aeval_mem_adjoin_singleton _ _)

/-- Lift any base derivation `δ : Derivation ℤ R[X] R[X]` to `Curve F` when `F.derivative ≠ 0`. -/
theorem liftBaseDerivation (F : R[X][X])
    [h : Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    (hder : F.derivative ≠ 0) (δ : Derivation ℤ R[X] R[X]) :
    ∃ D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F),
      ∀ c : R[X], D (planeBase (L := L) F c) = planeBase (L := L) F (δ c) := by
  let _ : Differential R[X] := ⟨δ⟩
  let _ : Differential (FractionRing L[X]) := fractionDifferential R[X] (FractionRing L[X])
  have hi : Function.Injective (genericCoeffs (R := R) (L := L)) :=
    IsFractionRing.injective R[X] (FractionRing L[X])
  have hFder : (F.map (genericCoeffs (R := R) (L := L))).derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    exact (Polynomial.map_ne_zero_iff hi).mpr hder
  let dCurve : Differential (Curve (L := L) F) := adjointDifferential _ hFder
  refine ⟨castIntDerivation (a₁ := Ring.toIntAlgebra _) dCurve.deriv, fun c => ?_⟩
  rw [castIntDerivation_apply]
  let _ : Differential (Curve (L := L) F) := dCurve
  change (algebraMap (FractionRing L[X]) (Curve (L := L) F)
    (algebraMap R[X] (FractionRing L[X]) c))′ = _
  rw [adjoint_deriv_algebraMap, fraction_deriv_algebraMap R[X] (FractionRing L[X]) c]
  rfl

/-- Helper: `F.derivative ≠ 0` when `2 ≤ F.natDegree` and `(F.natDegree : K) ≠ 0`. -/
theorem derivative_ne_zero_of_char {K : Type*} [Field K] (F : K[X][X][X])
    (hb : 2 ≤ F.natDegree) (hchar : (F.natDegree : K) ≠ 0) : F.derivative ≠ 0 := by
  intro hz
  have hlead : F.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (n := 0) (by omega))
  have hcoeff := congrArg (fun p : K[X][X][X] => p.coeff (F.natDegree - 1)) hz
  rw [coeff_derivative, coeff_zero, show F.natDegree - 1 + 1 = F.natDegree by omega] at hcoeff
  have hcast : ((F.natDegree - 1 : ℕ) + 1 : K[X][X]) = C (C (F.natDegree : K)) := by
    rw [← Nat.cast_add_one, show F.natDegree - 1 + 1 = F.natDegree by omega]
    simp
  rw [hcast] at hcoeff
  exact mul_ne_zero hlead (C_ne_zero.mpr (C_ne_zero.mpr hchar)) hcoeff

/-- **Main L1b Regularity Theorem**: any base derivation `δ` on `K[X][X]` that is logarithmic on
every prime dividing `F.discr` lifts to a derivation `D` on `Curve F` satisfying
`HeightOneNormalization.regularOnPlaneBranches F D`. -/
theorem regularOnPlaneBranches_of_log_on_discr
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K[X] L] [IsFractionRing K[X] L]
    (F : K[X][X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := K[X]) (L := L))))]
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (hchar : ∀ r : ℕ, 0 < r → r ≤ F.natDegree → (r : K) ≠ 0)
    (δ : Derivation ℤ K[X][X] K[X][X])
    (hlog_discr : ∀ p : K[X][X], Prime p → p ∣ F.discr → p ∣ δ p) :
    ∃ D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F),
      (∀ c, D (planeBase (L := L) F c) = planeBase (L := L) F (δ c)) ∧
      regularOnPlaneBranches F D := by
  have hder : F.derivative ≠ 0 :=
    derivative_ne_zero_of_char F hb (hchar F.natDegree (by omega) le_rfl)
  let _ : Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F) :=
    curveSeparable_of_derivative_ne_zero F hder
  obtain ⟨D, hδ⟩ := liftBaseDerivation (L := L) F hder δ
  refine ⟨D, hδ, ?_⟩
  intro p hp w x hx
  obtain ⟨hBdvr, hBfrac, hRloc, hRBlocal, hres_sep, A, hAfin, S, hSloc,
      u, e, v, π, hu, he_unit, hπB_eq, hπ_fac, hcompat⟩ :=
    branch_tame_and_separable (R := K[X]) (L := L) (K := K) F p hp w hchar
  obtain ⟨hbase, hlog_of_dvd⟩ := hcompat δ D hδ
  change D (⟨x, hx⟩ : branchSubring (R := K[X]) (L := L) (F := F) hp w) ∈
    branchSubring (R := K[X]) (L := L) (F := F) hp w
  let D' := castIntDerivation (a₂ := Ring.toIntAlgebra _) D
  have hD'_eq : ∀ y, D' y = D y := castIntDerivation_apply D
  have hbase' : ∀ r : baseSubring (R := K[X]) (L := L) (F := F) hp w,
      D' ((r : branchSubring (R := K[X]) (L := L) (F := F) hp w) : Curve (L := L) F) ∈
        branchSubring (R := K[X]) (L := L) (F := F) hp w := fun r => by
    rw [hD'_eq]; exact hbase r
  rw [← hD'_eq]
  by_cases hpd : p ∣ F.discr
  · have hlog := hlog_of_dvd (hlog_discr p hp hpd)
    have hlog' : ∃ c : baseSubring (R := K[X]) (L := L) (F := F) hp w,
        D' ((π : branchSubring (R := K[X]) (L := L) (F := F) hp w) : Curve (L := L) F) =
          ((π : branchSubring (R := K[X]) (L := L) (F := F) hp w) : Curve (L := L) F) *
            ((c : branchSubring (R := K[X]) (L := L) (F := F) hp w) : Curve (L := L) F) := by
      simpa only [hD'_eq] using hlog
    exact (ArkLib.ProximityGap.TameLogarithmicDVR.tame_logarithmic_lift
      (B := branchSubring (R := K[X]) (L := L) (F := F) hp w) D'
      (baseSubring (R := K[X]) (L := L) (F := F) hp w) A S u hu e v he_unit π hπ_fac hbase'
      hlog').1 ⟨x, hx⟩
  · obtain ⟨u', v', π', hu', _, hπ'_fac⟩ :=
      branch_unramified_of_not_dvd_discr (R := K[X]) (L := L) (K := K) F hFirr hb p hp hpd w
    exact ArkLib.ProximityGap.UnramifiedDerivationDVR.unramified_lift
      (B := branchSubring (R := K[X]) (L := L) (F := F) hp w) D'
      (baseSubring (R := K[X]) (L := L) (F := F) hp w) A S u' hu' π' v' hπ'_fac hbase' ⟨x, hx⟩

/-- Existence of the branch-regular first logarithmic derivation `D₁` lifting `H̃ ∂_Z`. -/
theorem exists_regular_logDerivZ
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K[X] L] [IsFractionRing K[X] L]
    (F : K[X][X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := K[X]) (L := L))))]
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (hchar : ∀ r : ℕ, 0 < r → r ≤ F.natDegree → (r : K) ≠ 0)
    {V U : K[X]} {H : K[X][X]} (hU : U ≠ 0)
    (hsplit : ∀ p : K[X][X], Prime p → p ∣ F.discr → p ∣ V.map C * C U * H) :
    ∃ D₁ : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F),
      (∀ c, D₁ (planeBase (L := L) F c) = planeBase (L := L) F ((V.map C * H) * c.derivative)) ∧
      regularOnPlaneBranches F D₁ :=
  regularOnPlaneBranches_of_log_on_discr F hFirr hb hchar (logDerivZ (V.map C * H))
    (fun p hp hdvd => dvd_logDerivZ_of_dvd_split hU hp (hsplit p hp hdvd))

/-- Existence of the branch-regular second logarithmic derivation `D₂` lifting
`U (H̃_X ∂_Z - H̃_Z ∂_X)`. -/
theorem exists_regular_logDerivJac
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K[X] L] [IsFractionRing K[X] L]
    (F : K[X][X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := K[X]) (L := L))))]
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (hchar : ∀ r : ℕ, 0 < r → r ≤ F.natDegree → (r : K) ≠ 0)
    {V U : K[X]} {H : K[X][X]}
    (hsplit : ∀ p : K[X][X], Prime p → p ∣ F.discr → p ∣ V.map C * C U * H) :
    ∃ D₂ : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F),
      (∀ c, D₂ (planeBase (L := L) F c) =
        planeBase (L := L) F (logDerivJac U (V.map C * H) c)) ∧
      regularOnPlaneBranches F D₂ :=
  regularOnPlaneBranches_of_log_on_discr F hFirr hb hchar (logDerivJac U (V.map C * H))
    (fun p hp hdvd => dvd_logDerivJac_of_dvd_split hp (hsplit p hp hdvd))

/-! ## Section 3: Section denominator divisibility from `D₁` and `D₂` -/

/-- For any simple section `(z, q)` of `F` and anchor `a : K[X][X]` with `Y ≠ a`, regularity of
`D₁` (lifting `H̃ ∂_Z`) implies `D_z ∣ (F.eval a)(X, z) * H̃(X, z)` for the reduced tangent
denominator `D_z = (tangentPair F z q).2`. -/
theorem tangentPair_den_dvd_of_logDerivZ
    {K L : Type*} [Field K] [Field L] [Algebra K[X] L] [IsFractionRing K[X] L]
    (F : K[X][X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := K[X]) (L := L))))]
    (Htilde : K[X][X])
    (D₁ : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hD₁ : regularOnPlaneBranches F D₁)
    (hδ₁ : ∀ c, D₁ (planeBase (L := L) F c) = planeBase (L := L) F (Htilde * c.derivative))
    (z : K) (q : K[X])
    (hl : F.leadingCoeff.eval (C z) ≠ 0)
    (h₀ : (F.map (evalRingHom (C z))).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom (C z))).eval q ≠ 0)
    (a : K[X][X]) (ha : AdjoinRoot.root _ ≠ planeBase (L := L) F a) :
    (tangentPair (L := L) F z q).2 ∣ (F.eval a).eval (C z) * Htilde.eval (C z) := by
  have hdiv := implicit_derivative_divides_of_regular_at_branches F (C z) q hl h₀ h₁
    D₁ hD₁ (logDerivZ Htilde) hδ₁ a ha
  have hcd : coefficientDerivative (logDerivZ Htilde) F =
      C Htilde * coefficientDerivative (scalarDerivative K[X]) F := by
    ext j; rw [coeff_C_mul]; rfl
  rw [hcd, Polynomial.map_mul, map_C, eval_mul, eval_C] at hdiv
  let t := (F.derivative.map (evalRingHom (C z))).eval q
  let w := ((coefficientDerivative (scalarDerivative K[X]) F).map (evalRingHom (C z))).eval q
  let v := -algebraMap K[X] L w / algebraMap K[X] L t
  have hcop : IsCoprime (tangentPair (L := L) F z q).2 (tangentPair (L := L) F z q).1 :=
    (IsFractionRing.num_den_reduced K[X] v).symm.isCoprime
  have hrel : t * (tangentPair (L := L) F z q).1 = -w * (tangentPair (L := L) F z q).2 := by
    apply IsFractionRing.injective K[X] L
    change algebraMap K[X] L (t * IsFractionRing.num K[X] v) =
      algebraMap K[X] L (-w * (IsFractionRing.den K[X] v : K[X]))
    have h := (IsFractionRing.num_mul_den_eq_num_iff_eq (A := K[X]) (x := v) (y := v)).mpr rfl
    have htL : algebraMap K[X] L t ≠ 0 := by
      simpa using (IsFractionRing.injective K[X] L).ne h₁
    rw [map_mul, map_mul, map_neg, ← h]
    dsimp only [v]
    field_simp
  obtain ⟨k, hk⟩ := hdiv
  have hmul : (tangentPair (L := L) F z q).2 ∣
      ((F.eval a).eval (C z) * Htilde.eval (C z)) * (tangentPair (L := L) F z q).1 := by
    refine ⟨-k, ?_⟩
    apply mul_left_cancel₀ h₁
    change t * (((F.eval a).eval (C z) * Htilde.eval (C z)) * (tangentPair (L := L) F z q).1) =
      t * ((tangentPair (L := L) F z q).2 * (-k))
    have hk' : (F.eval a).eval (C z) * (Htilde.eval (C z) * w) = t * k := hk
    linear_combination ((F.eval a).eval (C z) * Htilde.eval (C z)) * hrel -
      (tangentPair (L := L) F z q).2 * hk'
  exact hcop.dvd_of_dvd_mul_right hmul

/-- For any simple section `(z, q)` of `F` and anchor `a : K[X][X]` with `Y ≠ a`, regularity of
`D₂` (lifting `U (H̃_X ∂_Z - H̃_Z ∂_X)`) implies
`D_z ∣ (F.eval a)(X, z) * U * (∂_X H̃)(X, z)` for `D_z = (tangentPair F z q).2`. -/
theorem tangentPair_den_dvd_of_logDerivJac
    {K L : Type*} [Field K] [Field L] [Algebra K[X] L] [IsFractionRing K[X] L]
    (F : K[X][X][X])
    [Fact (Irreducible (F.map (genericCoeffs (R := K[X]) (L := L))))]
    (U : K[X]) (Htilde : K[X][X])
    (D₂ : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hD₂ : regularOnPlaneBranches F D₂)
    (hδ₂ : ∀ c, D₂ (planeBase (L := L) F c) = planeBase (L := L) F (logDerivJac U Htilde c))
    (z : K) (q : K[X])
    (hl : F.leadingCoeff.eval (C z) ≠ 0)
    (h₀ : (F.map (evalRingHom (C z))).eval q = 0)
    (h₁ : (F.derivative.map (evalRingHom (C z))).eval q ≠ 0)
    (a : K[X][X]) (ha : AdjoinRoot.root _ ≠ planeBase (L := L) F a) :
    (tangentPair (L := L) F z q).2 ∣
      (F.eval a).eval (C z) * (U * (partialX K Htilde).eval (C z)) := by
  have hdiv := implicit_derivative_divides_of_regular_at_branches F (C z) q hl h₀ h₁
    D₂ hD₂ (logDerivJac U Htilde) hδ₂ a ha
  have hcd : coefficientDerivative (logDerivJac U Htilde) F =
      C (C U * partialX K Htilde) * coefficientDerivative (scalarDerivative K[X]) F -
        C (C U * Htilde.derivative) * coefficientDerivative (partialX K) F := by
    apply Polynomial.ext
    intro j
    rw [coeff_sub, coeff_C_mul, coeff_C_mul]
    change C U * (partialX K Htilde * (F.coeff j).derivative -
      Htilde.derivative * partialX K (F.coeff j)) =
      C U * partialX K Htilde * (F.coeff j).derivative -
        C U * Htilde.derivative * partialX K (F.coeff j)
    ring
  rw [hcd, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C,
    eval_sub, eval_mul, eval_mul, eval_C, eval_C] at hdiv
  have hchain := section_chain_partialX F z q
  rw [h₀, derivative_zero] at hchain
  let t := (F.derivative.map (evalRingHom (C z))).eval q
  let w := ((coefficientDerivative (scalarDerivative K[X]) F).map (evalRingHom (C z))).eval q
  let fx := ((coefficientDerivative (partialX K) F).map (evalRingHom (C z))).eval q
  have hfx : fx = -(t * q.derivative) := by
    linear_combination -hchain
  have hdiv' : t ∣ (F.eval a).eval (C z) * (U * (partialX K Htilde).eval (C z)) * w := by
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k - (F.eval a).eval (C z) * (U * Htilde.derivative.eval (C z)) * q.derivative, ?_⟩
    have h1 : (C U * partialX K Htilde).eval (C z) = U * (partialX K Htilde).eval (C z) := by
      simp
    have h2 : (C U * Htilde.derivative).eval (C z) = U * Htilde.derivative.eval (C z) := by
      simp
    change (F.eval a).eval (C z) * ((C U * partialX K Htilde).eval (C z) * w -
      (C U * Htilde.derivative).eval (C z) * fx) = t * k at hk
    rw [h1, h2, hfx] at hk
    linear_combination hk
  let v := -algebraMap K[X] L w / algebraMap K[X] L t
  have hcop : IsCoprime (tangentPair (L := L) F z q).2 (tangentPair (L := L) F z q).1 :=
    (IsFractionRing.num_den_reduced K[X] v).symm.isCoprime
  have hrel : t * (tangentPair (L := L) F z q).1 = -w * (tangentPair (L := L) F z q).2 := by
    apply IsFractionRing.injective K[X] L
    change algebraMap K[X] L (t * IsFractionRing.num K[X] v) =
      algebraMap K[X] L (-w * (IsFractionRing.den K[X] v : K[X]))
    have h := (IsFractionRing.num_mul_den_eq_num_iff_eq (A := K[X]) (x := v) (y := v)).mpr rfl
    have htL : algebraMap K[X] L t ≠ 0 := by
      simpa using (IsFractionRing.injective K[X] L).ne h₁
    rw [map_mul, map_mul, map_neg, ← h]
    dsimp only [v]
    field_simp
  obtain ⟨k, hk⟩ := hdiv'
  have hmul : (tangentPair (L := L) F z q).2 ∣
      ((F.eval a).eval (C z) * (U * (partialX K Htilde).eval (C z))) *
        (tangentPair (L := L) F z q).1 := by
    refine ⟨-k, ?_⟩
    apply mul_left_cancel₀ h₁
    linear_combination
      ((F.eval a).eval (C z) * (U * (partialX K Htilde).eval (C z))) * hrel -
        (tangentPair (L := L) F z q).2 * hk
  exact hcop.dvd_of_dvd_mul_right hmul

end PlaneRegularity

#print axioms dvd_logDerivZ_of_dvd_split
#print axioms dvd_logDerivJac_of_dvd_split
#print axioms irreducible_map_genericCoeffs
#print axioms regularOnPlaneBranches_of_log_on_discr
#print axioms exists_regular_logDerivZ
#print axioms exists_regular_logDerivJac
#print axioms tangentPair_den_dvd_of_logDerivZ
#print axioms tangentPair_den_dvd_of_logDerivJac

end ArkLib.ProximityGap.Frontier.PlaneBranchRegularity
