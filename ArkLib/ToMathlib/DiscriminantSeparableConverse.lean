/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DiscriminantSeparable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.GaussLemma
import ArkLib.Data.Polynomial.Prelims

/-!
# Separable ⇒ nonzero discriminant (the converse bridge), and the perfect-field discharge

The in-tree `ArkLib/ToMathlib/DiscriminantSeparable.lean` proves
`discr ≠ 0 → Separable` over a field. This file supplies the **converse** and its
consequences, which turn the per-factor separability *residual* of the Hab25 §3 Step S5
(`discr R ≠ 0` in `GSDiscriminantOverRatFunc.lean`) into a **theorem** whenever the relevant
fraction field is perfect — in particular in characteristic zero:

* `Polynomial.discr_ne_zero_of_separable` — over a field, a separable polynomial of positive
  degree has `discr ≠ 0`. Proof: separability is coprimality with the derivative, so the
  default-size resultant is nonzero (`resultant_ne_zero`); padding the size up to
  `natDegree f − 1` (`resultant_add_right_deg`, costing a power of the surviving leading
  coefficient) matches the discriminant–resultant identity `resultant_deriv`, whose right side
  `± lc · discr` then cannot vanish.

* `Polynomial.discr_ne_zero_of_separable_map` — domain version: if the image of `f` under an
  injective hom into a field is separable, the discriminant of `f` itself (over the domain) is
  nonzero, via the specialization commutation `discr_map_of_natDegree_preserved`.

* `Polynomial.discr_ne_zero_of_irreducible_of_perfectField_fractionRing` — the payoff: over a
  domain `A` with perfect fraction field, every irreducible `f : A[X]` of positive degree has
  `discr f ≠ 0`. Gauss's lemma transports irreducibility to `FractionRing A`
  (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`; irreducible nonconstant
  polynomials are primitive), perfectness gives separability, and the converse bridge lands.

With `A = K[X]`, `K = F(Z)`, `F` of characteristic zero, `FractionRing A = K(X)` is perfect
(`PerfectField.ofCharZero`), so **every positive-`Y`-degree irreducible factor of the GS
interpolant has nonzero `Y`-discriminant** — the S5 separability residual is discharged
(`GSSeparabilityCharZero.lean`). In characteristic `p` the same statement holds for the
separable factors; the inseparable `R(X, Y^{p^f})` descent remains the deep S4→S6 content.

* `Univariate.discriminant_mul_leadingCoeff_pow_eq` /
  `Univariate.discriminant_eq_neg_one_pow_mul_discr` — the **sign/normalization bridge** for
  the historical `Univariate.discriminant f := lc(f)⁻¹ · resultant f f'`, retained here
  after pinned ArkLib switched to `Polynomial.discr`. This formula omits the sign
  `(-1)^(n(n-1)/2)` and uses the default-size resultant. When `deg f' < n - 1`
  (characteristic dividing `n`), that resultant
  differs from the size-`(n-1)` one by a power of `lc(f)`.  For `0 < deg f` with
  `n := natDegree f`, `discriminant f · lc(f)^((n-1) - deg f') = (-1)^(n(n-1)/2) · discr f`;
  in particular `discriminant f = (-1)^(n(n-1)/2) · discr f` when `deg f' = n - 1`.  E.g. over
  `ℚ`, `discriminant (X² - 1) = -4` while `discr (X² - 1) = 4` (checked below).  The
  discrepancy is a unit in positive degree, so nonvanishing is unaffected. For the
  conventional discriminant and its separability criterion on nonzero polynomials, use
  `Polynomial.discr` and `Univariate.separable_iff_discr_ne_zero`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace Polynomial

open scoped Polynomial

/-- **Separable ⇒ nonzero discriminant**, over a field (converse of
`separable_of_discr_ne_zero`). -/
theorem discr_ne_zero_of_separable {K : Type*} [Field K] {f : K[X]}
    (hdeg : 0 < f.natDegree) (hsep : f.Separable) : f.discr ≠ 0 := by
  have hf0 : f ≠ 0 := fun h => by simp [h] at hdeg
  have hlc : f.coeff f.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hf0
  -- coprimality gives a nonzero resultant at the default sizes
  have hres : resultant f f.derivative ≠ 0 :=
    resultant_ne_zero f f.derivative hsep
  -- pad the derivative-side size up to `natDegree f − 1`
  have hd : f.derivative.natDegree ≤ f.natDegree - 1 := natDegree_derivative_le f
  have hpad := resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree
    ((f.natDegree - 1) - f.derivative.natDegree) le_rfl
  rw [show f.derivative.natDegree + ((f.natDegree - 1) - f.derivative.natDegree) =
      f.natDegree - 1 by omega] at hpad
  have hres' : resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
    rw [hpad]
    exact mul_ne_zero (pow_ne_zero _ hlc) hres
  -- match against the discriminant–resultant identity
  have hrd := resultant_deriv (natDegree_pos_iff_degree_pos.mp hdeg)
  intro h0
  rw [h0, mul_zero] at hrd
  exact hres' hrd

/-- **Domain version of the converse bridge.** If the image of `f` under an injective ring
hom into a field is separable (and `f` has positive degree), then `discr f ≠ 0` already over
the domain — via the specialization commutation `discr_map_of_natDegree_preserved`. -/
theorem discr_ne_zero_of_separable_map {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [Field B] {φ : A →+* B} (hinj : Function.Injective φ) {f : A[X]}
    (hdeg : 0 < f.natDegree) (hsep : (f.map φ).Separable) : f.discr ≠ 0 := by
  have hmap : (f.map φ).natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  have h1 : (f.map φ).discr ≠ 0 :=
    discr_ne_zero_of_separable (by rw [hmap]; exact hdeg) hsep
  rw [discr_map_of_natDegree_preserved hdeg hmap] at h1
  intro h0
  exact h1 (by rw [h0, map_zero])

/-- **The perfect-fraction-field discharge of the separability residual.** Over a domain `A`
with `NormalizedGCDMonoid` structure whose fraction field is perfect (e.g. any domain of
characteristic zero), every irreducible polynomial of positive degree has nonzero
discriminant: Gauss transports irreducibility to `FractionRing A`, perfectness yields
separability there, and the converse bridge pulls `discr ≠ 0` back to `A`. -/
theorem discr_ne_zero_of_irreducible_of_perfectField_fractionRing
    {A : Type*} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
    [PerfectField (FractionRing A)]
    {f : A[X]} (hirr : Irreducible f) (hdeg : 0 < f.natDegree) :
    f.discr ≠ 0 := by
  have hprim : f.IsPrimitive := hirr.isPrimitive hdeg.ne'
  have hirr' : Irreducible (f.map (algebraMap A (FractionRing A))) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hsep : (f.map (algebraMap A (FractionRing A))).Separable :=
    PerfectField.separable_of_irreducible hirr'
  exact discr_ne_zero_of_separable_map (IsFractionRing.injective A (FractionRing A)) hdeg hsep

end Polynomial

namespace Univariate

open Polynomial

/-- The historical default-size resultant normalization, without the degree-dependent sign, from
`ArkLib/Data/Polynomial/Prelims.lean` (Katerina Hristova and Ilia Vlasov). -/
noncomputable def discriminant {F : Type} [Field F] [Inhabited F] (f : F[X]) : F :=
  1 / f.leadingCoeff * Polynomial.resultant f (Polynomial.derivative f)

/-- **Normalization bridge for the custom `Univariate.discriminant`.**  For `0 < deg f`, the
custom value `lc(f)⁻¹ · resultant f f'` (default resultant sizes) relates to Mathlib's
conventional `Polynomial.discr` by the sign `(-1)^(n(n-1)/2)` and the size-padding factor
`lc(f)^((n-1) - deg f')`, where `n = natDegree f`. -/
theorem discriminant_mul_leadingCoeff_pow_eq {F : Type} [Field F] [Inhabited F] {f : F[X]}
    (hf : 0 < f.degree) :
    discriminant f * f.leadingCoeff ^ ((f.natDegree - 1) - f.derivative.natDegree) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  have hf0 : f ≠ 0 := ne_zero_of_degree_gt hf
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hd : f.derivative.natDegree ≤ f.natDegree - 1 := natDegree_derivative_le f
  have hpad := resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree
    ((f.natDegree - 1) - f.derivative.natDegree) le_rfl
  rw [show f.derivative.natDegree + ((f.natDegree - 1) - f.derivative.natDegree) =
      f.natDegree - 1 by omega, resultant_deriv hf, coeff_natDegree] at hpad
  unfold discriminant
  have hres : resultant f f.derivative =
      resultant f f.derivative f.natDegree f.derivative.natDegree := rfl
  rw [hres, show 1 / f.leadingCoeff * f.resultant f.derivative f.natDegree f.derivative.natDegree *
        f.leadingCoeff ^ ((f.natDegree - 1) - f.derivative.natDegree) =
      f.leadingCoeff⁻¹ * (f.leadingCoeff ^ ((f.natDegree - 1) - f.derivative.natDegree) *
        f.resultant f.derivative f.natDegree f.derivative.natDegree) by ring, ← hpad]
  field_simp

/-- **The custom discriminant is the conventional one up to the omitted sign**, whenever the
derivative has full degree `n - 1` (e.g. in characteristic zero):
`discriminant f = (-1)^(n(n-1)/2) · discr f`. -/
theorem discriminant_eq_neg_one_pow_mul_discr {F : Type} [Field F] [Inhabited F] {f : F[X]}
    (hf : 0 < f.degree) (hd : f.derivative.natDegree = f.natDegree - 1) :
    discriminant f = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  simpa [hd] using discriminant_mul_leadingCoeff_pow_eq hf

/-- Quadratic sanity check: the custom value for `X² - 1` over `ℚ` is `-4`, the negative of the
conventional discriminant `discr (X² - 1) = 4`. -/
example : discriminant ((X ^ 2 - 1 : ℚ[X])) = -4 := by
  have hnd : (X ^ 2 - 1 : ℚ[X]).natDegree = 2 := by compute_degree!
  have hdeg : 0 < (X ^ 2 - 1 : ℚ[X]).degree := by
    rw [degree_eq_natDegree (by intro h; simp [h] at hnd), hnd]; norm_num
  have hder : (derivative (X ^ 2 - 1 : ℚ[X])).natDegree = 1 := by
    simp
  rw [discriminant_eq_neg_one_pow_mul_discr hdeg (by rw [hder, hnd]), hnd]
  rw [discr_of_degree_eq_two (by rw [degree_eq_natDegree (by intro h; simp [h] at hnd), hnd]; rfl)]
  have h2 : (X ^ 2 - 1 : ℚ[X]).coeff 2 = 1 := by simp [coeff_X_pow, coeff_one]
  have h1 : (X ^ 2 - 1 : ℚ[X]).coeff 1 = 0 := by simp [coeff_X_pow, coeff_one]
  have h0 : (X ^ 2 - 1 : ℚ[X]).coeff 0 = -1 := by simp [coeff_X_pow, coeff_one]
  rw [h0, h1, h2]; norm_num

end Univariate

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Polynomial.discr_ne_zero_of_separable
#print axioms Polynomial.discr_ne_zero_of_separable_map
#print axioms Polynomial.discr_ne_zero_of_irreducible_of_perfectField_fractionRing
#print axioms Univariate.discriminant_mul_leadingCoeff_pow_eq
#print axioms Univariate.discriminant_eq_neg_one_pow_mul_discr
