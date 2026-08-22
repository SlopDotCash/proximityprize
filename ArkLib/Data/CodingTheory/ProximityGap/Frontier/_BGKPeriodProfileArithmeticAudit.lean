/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The actual period profile: Galois rigidity, moment congruences, and the remaining gap

`_BGKLowerMomentOrbitSpikeNoGo` gives a nonnegative orbit profile for
`s_i = |eta_i|^2` which has the exact Parseval mass and even satisfies hypothetical Wick ceilings
through depth six, but misses the depth-seven target by 15--16 bits.  That profile deliberately
forgets that the `eta_i` are the conjugates of one Gaussian period.  This file audits the strongest
elementary consequences of putting that arithmetic structure back.

## 1. The literal spike is not a Galois orbit

If one conjugate of an element of a number field is rational, injectivity of that embedding forces
the element itself to be rational.  Consequently every conjugate has the same value.  Applied to
`eta^2`, this says that a single rational squared period forces the complete squared-period profile
to be constant.  Since

`m * 2^53 != q - n`,

the literal `2^53` integer spike cannot occur in the actual period orbit.  This is a genuine joint
constraint which scalar moment cones miss; `rational_squared_spike_incompatible_with_sum`
formalizes it without postulating irreducibility separately.

This exact exclusion is not yet quantitative: it says nothing about an irrational conjugate lying
arbitrarily close to `2^53`.  A prize proof needs a separation theorem with a useful archimedean
radius, not merely the fact that the radius is nonzero.

## 2. The period-polynomial congruence also kills the literal spike

For the period polynomial `P`, all periods reduce to `n` at the ramified prime, so
`P(X) = (X-n)^m (mod q)`.  Equivalently, the distinct-period moment law gives the necessary
congruence

`q | n * sum_i s_i^r + n^(2*r)`.

The literal spike already violates this at `r=2`; its nonzero residue lies in `[2^136,2^137)`.
The strengthened nonzero integral profile below also violates it.  Thus simultaneous moment
congruences are a real arithmetic socket absent from the scalar countermodel.  A single congruence
is much too coarse at depth seven, however: the public orbit target contains exactly `2^198`
whole `q`-steps.

## 3. Integrality, trace, norm-nonvanishing, and Newton data still do not suffice

We give a second exact production profile, now at the signed `eta` level.  It consists of

* one `+2^26` spike (so `s = 2^52`),
* `productionBulkCount` copies of `±2^15`, with signed excess `-2048`,
* `productionHalfCount` copies of `±2^14`, equally split, and
* one `-1`.

Every entry is a nonzero algebraic integer, the number of entries is exactly `m`, the signed trace
is exactly `-1`, and the squared trace is exactly `q-n`.  Hence its monic root polynomial has
integer coefficients, nonzero integer norm, and the usual integral Newton power sums.  It still
satisfies every granted Wick ceiling through depth six and exceeds the seventh target by more than
eight bits.  Therefore integrality, nonzero norm, trace, second moment, and lower moment bounds do
not replace the genuinely transitive Galois/ramification constraint.

## 4. Discriminant, Jacobi determinant, and valuation audit

The conductor--discriminant datum supplies `|disc K| = q^(m-1)`.  Fekete/Vandermonde turns this
into a *lower* bound on the house.  At production its binary logarithmic contribution per conjugate
is less than `2^-120` (`production_discriminant_log_budget`), so it gives no upper exclusion around
the spike.

The 2026 revision of Wu--Wang--Pan, arXiv:2506.14316, proves that a determinant of an
`(m-1) x (m-1)` Jacobi-sum matrix equals `m^(m-2)` times the linear coefficient of the Gaussian
period minimal polynomial.  This controls one cofactor symmetric function
`e_(m-1) = Norm(eta) * sum_i eta_i^-1`; without lower bounds for the other conjugates it does not
upper-bound one conjugate.  Wu--Ji, arXiv:2605.27169, concerns products of real Jacobi parts for the
quadratic-character matrix and does not supply a growing-index individual-period estimate.
Do Duc--Leung--Schmidt, arXiv:1903.07314, gives norm bounds for short cyclotomic integers; at this
cone it recovers the already-known no-wrap norm threshold, exponentially below the production
moment regime.  Finally, the `q`-adic Newton polygon is the fixed ramification/Eisenstein polygon;
it carries no archimedean upper radius.

The honest surviving target is therefore a **quantitative simultaneous-conjugate theorem**:
combine the ramified congruence of all coefficients (or all moment residues) with archimedean
separation strongly enough to bound the seventh power sum.  None of the audited scalar product,
determinant, discriminant, or valuation identities supplies that coupling by itself.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192

namespace ArkLib.ProximityGap.Frontier.BGKPeriodProfileArithmeticAudit

open scoped BigOperators

/-! ## Production parameters and the previously audited literal spike -/

/-- Production subgroup size. -/
def productionN : Nat := 2 ^ 30

/-- Number of distinct nonzero-frequency multiplicative orbits. -/
def productionM : Nat := 2 ^ 128 + 192

/-- Production field cardinality. -/
def productionQ : Nat := productionN * productionM + 1

/-- Literal scalar-countermodel spike from `_BGKLowerMomentOrbitSpikeNoGo`. -/
def productionSpike : Nat := 2 ^ 53

/-- Number of baseline orbits in that literal scalar countermodel. -/
def productionLiteralBulkOrbits : Nat := productionM - 2 ^ 23 - 1

/-- Orbit-level power moment of the literal scalar countermodel. -/
def literalOrbitPowerMoment (r : Nat) : Nat :=
  productionSpike ^ r + 1 + productionLiteralBulkOrbits * productionN ^ r

/-- Wick coefficient `(2r-1)!!`. -/
def wickCoefficient (r : Nat) : Nat := Nat.doubleFactorial (2 * r - 1)

/-! ## Galois rigidity of a rational conjugate -/

/-- If one algebra embedding sends an element to a rational number, the element was that rational
number already.  This is just injectivity of the embedding, but it is the load-bearing reason an
isolated rational value cannot occur in a transitive conjugate profile. -/
theorem eq_rational_of_algEmbedding_eq_rational
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (sigma : K →ₐ[ℚ] L) (x : K) (r : ℚ)
    (h : sigma x = algebraMap ℚ L r) :
    x = algebraMap ℚ K r := by
  apply sigma.injective
  simpa using h

/-- Once one embedding of `x` is rational, every other embedding has the same value. -/
theorem every_embedding_eq_rational_of_one
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (sigma tau : K →ₐ[ℚ] L) (x : K) (r : ℚ)
    (h : sigma x = algebraMap ℚ L r) :
    tau x = algebraMap ℚ L r := by
  rw [eq_rational_of_algEmbedding_eq_rational sigma x r h]
  exact tau.commutes r

/-- Squared-conjugate form used for `s_i = sigma_i(eta^2)`. -/
theorem squared_conjugates_eq_of_one_rational
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (sigma tau : K →ₐ[ℚ] L) (eta : K) (r : ℚ)
    (h : sigma (eta ^ 2) = algebraMap ℚ L r) :
    tau (eta ^ 2) = algebraMap ℚ L r :=
  every_embedding_eq_rational_of_one sigma tau (eta ^ 2) r h

/-- The production spike is not the average forced by the exact squared-period trace. -/
theorem productionSpike_not_profile_average :
    productionM * productionSpike ≠ productionQ - productionN := by
  norm_num [productionM, productionSpike, productionQ, productionN]

/-- **Exact Galois exclusion of the literal spike.**  If `sigma i (eta^2)` are `m` embeddings of
one field element and their sum is the exact Parseval trace `q-n`, no coordinate can equal the
rational integer `2^53`.  One such coordinate would force all embeddings to equal `2^53`, whose
sum has the wrong value. -/
theorem rational_squared_spike_incompatible_with_sum
    {K : Type*} [Field K] [Algebra ℚ K]
    (eta : K) (sigma : Fin productionM → K →ₐ[ℚ] ℂ)
    (hsum : ∑ i, sigma i (eta ^ 2) = ((productionQ - productionN : Nat) : ℂ)) :
    ∀ i, sigma i (eta ^ 2) ≠ (productionSpike : ℂ) := by
  intro i hi
  have hiq : sigma i (eta ^ 2) = algebraMap ℚ ℂ (productionSpike : ℚ) := by
    simpa using hi
  have hall : ∀ j, sigma j (eta ^ 2) = (productionSpike : ℂ) := by
    intro j
    simpa using
      (squared_conjugates_eq_of_one_rational (sigma i) (sigma j) eta
        (productionSpike : ℚ) hiq)
  have hconst : ∑ j, sigma j (eta ^ 2) = ∑ _j : Fin productionM, (productionSpike : ℂ) := by
    exact Finset.sum_congr rfl (fun j _ => hall j)
  have hbad : (productionM : ℂ) * (productionSpike : ℂ)
      = ((productionQ - productionN : Nat) : ℂ) := by
    calc
      (productionM : ℂ) * (productionSpike : ℂ)
          = ∑ _j : Fin productionM, (productionSpike : ℂ) := by simp
      _ = ∑ j, sigma j (eta ^ 2) := hconst.symm
      _ = ((productionQ - productionN : Nat) : ℂ) := hsum
  have hre := congrArg Complex.re hbad
  norm_num [productionM, productionSpike, productionQ, productionN] at hre

/-! ## Applicability boundary for the 2026 Jacobi-determinant identity -/

open Polynomial

/-- A monic reciprocal quartic used to audit what one linear-coefficient determinant can see:

`X^4 + X^3 + (1-A(A+1))X^2 + X + 1`.

Its trace coefficient, linear coefficient, and norm are all `1`, independently of `A`.  Modulo
two it is always the fifth cyclotomic polynomial, hence it is irreducible over `ℤ`; nevertheless
it has a real root in `[A/2,A]`. -/
noncomputable def jacobiDeterminantBlindPoly (A : Nat) : ℤ[X] :=
  X ^ 4 + X ^ 3 + C (1 - (A : Int) * ((A : Int) + 1)) * X ^ 2 + X + 1

/-- The family is monic. -/
theorem jacobiDeterminantBlindPoly_monic (A : Nat) :
    (jacobiDeterminantBlindPoly A).Monic := by
  rw [jacobiDeterminantBlindPoly]
  rw [show
      X ^ 4 + X ^ 3 + C (1 - (A : Int) * ((A : Int) + 1)) * X ^ 2 + X + 1 =
        X ^ 4 + (X ^ 3 + C (1 - (A : Int) * ((A : Int) + 1)) * X ^ 2 + X + 1) by ring]
  apply (monic_X_pow (R := ℤ) 4).add_of_left
  have hrest :
      (X ^ 3 + C (1 - (A : Int) * ((A : Int) + 1)) * X ^ 2 + X + 1 : ℤ[X]).degree ≤ 3 := by
    compute_degree
  rw [degree_X_pow]
  exact lt_of_le_of_lt hrest (by norm_num)

/-- Fixed norm/constant coefficient. -/
theorem jacobiDeterminantBlindPoly_coeff_zero (A : Nat) :
    (jacobiDeterminantBlindPoly A).coeff 0 = 1 := by
  simp [jacobiDeterminantBlindPoly]

/-- Fixed Wu--Wang--Pan determinant coordinate: the coefficient of `X` is always `1`. -/
theorem jacobiDeterminantBlindPoly_coeff_one (A : Nat) :
    (jacobiDeterminantBlindPoly A).coeff 1 = 1 := by
  have hterm :
      (C (1 - (A : Int) * ((A : Int) + 1)) * X ^ 2 : ℤ[X]).coeff 1 = 0 := by
    rw [coeff_C_mul_X_pow]
    norm_num
  rw [jacobiDeterminantBlindPoly]
  simp only [coeff_add, hterm]
  norm_num [coeff_X_pow, coeff_X, coeff_one]

/-- Fixed trace coefficient: the coefficient of `X^3` is always `1`, hence root trace `-1`. -/
theorem jacobiDeterminantBlindPoly_coeff_three (A : Nat) :
    (jacobiDeterminantBlindPoly A).coeff 3 = 1 := by
  have hterm :
      (C (1 - (A : Int) * ((A : Int) + 1)) * X ^ 2 : ℤ[X]).coeff 3 = 0 := by
    rw [coeff_C_mul_X_pow]
    norm_num
  rw [jacobiDeterminantBlindPoly]
  simp only [coeff_add, hterm]
  norm_num [coeff_X_pow, coeff_X, coeff_one]

/-- Modulo two the parameter disappears because `A(A+1)` is even, leaving `Phi_5`. -/
theorem jacobiDeterminantBlindPoly_mod_two (A : Nat) :
    (jacobiDeterminantBlindPoly A).map (Int.castRingHom (ZMod 2)) =
      cyclotomic 5 (ZMod 2) := by
  have hdvd : 2 ∣ A * (A + 1) :=
    even_iff_two_dvd.mp (Nat.even_mul_succ_self A)
  have hprodNat : ((A * (A + 1) : Nat) : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hprod : ((A : ZMod 2) * ((A : ZMod 2) + 1)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hprodNat
  have hcoef : Int.castRingHom (ZMod 2) (1 - (A : Int) * ((A : Int) + 1)) = 1 := by
    simp only [map_sub, map_one, map_mul, Int.coe_castRingHom, Int.cast_natCast,
      Int.cast_add, Int.cast_one]
    rw [hprod]
    simp
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  calc
    (jacobiDeterminantBlindPoly A).map (Int.castRingHom (ZMod 2)) =
        X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
          rw [jacobiDeterminantBlindPoly]
          simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
            Polynomial.map_C, Polynomial.map_one]
          change X ^ 4 + X ^ 3 + C
              (Int.castRingHom (ZMod 2) (1 - (A : Int) * ((A : Int) + 1))) * X ^ 2
              + X + 1 = X ^ 4 + X ^ 3 + X ^ 2 + X + 1
          rw [hcoef, C_1, one_mul]
    _ = cyclotomic 5 (ZMod 2) := by
      rw [cyclotomic_prime (ZMod 2) 5]
      norm_num [Finset.sum_range_succ]
      ring

/-- The mod-two polynomial `Phi_5` is irreducible: the order of `2` modulo `5` is `4`. -/
theorem cyclotomic_five_irreducible_mod_two :
    Irreducible (cyclotomic 5 (ZMod 2)) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hpn : ¬ 2 ∣ 5 := by norm_num
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5) hpn
  · exact dvd_refl (cyclotomic 5 (ZMod 2))
  · have hcop : Nat.Coprime 2 5 := by norm_num
    have horder : orderOf (ZMod.unitOfCoprime 2 hcop) = 4 := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime]
      rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide, fun k hk hk0 => ?_⟩
      interval_cases k <;> decide
    rw [natDegree_cyclotomic]
    simpa using horder.symm

/-- The whole integer family is irreducible, not merely an arbitrary reducible root profile. -/
theorem jacobiDeterminantBlindPoly_irreducible (A : Nat) :
    Irreducible (jacobiDeterminantBlindPoly A) := by
  apply (jacobiDeterminantBlindPoly_monic A).irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 2))
  rw [jacobiDeterminantBlindPoly_mod_two]
  exact cyclotomic_five_irreducible_mod_two

/-- Real evaluation form of the determinant-blind quartic. -/
def jacobiDeterminantBlindValue (A x : ℝ) : ℝ :=
  x ^ 4 + x ^ 3 + (1 - A * (A + 1)) * x ^ 2 + x + 1

/-- At the right endpoint `x=A`, the value is positive. -/
theorem jacobiDeterminantBlindValue_at_right (A : ℝ) :
    jacobiDeterminantBlindValue A A = A ^ 2 + A + 1 := by
  unfold jacobiDeterminantBlindValue
  ring

/-- At `x=A/2` the value is negative for `A≥2`. -/
theorem jacobiDeterminantBlindValue_at_half_neg (A : ℝ) (hA : 2 ≤ A) :
    jacobiDeterminantBlindValue A (A / 2) < 0 := by
  have hA0 : 0 ≤ A := by linarith
  have hcubic : 0 ≤ 3 * A ^ 3 + 8 * A ^ 2 + 12 * A + 16 := by positivity
  have hprod : 0 ≤ (A - 2) * (3 * A ^ 3 + 8 * A ^ 2 + 12 * A + 16) :=
    mul_nonneg (by linarith) hcubic
  have hid :
      16 * jacobiDeterminantBlindValue A (A / 2) =
        -((A - 2) * (3 * A ^ 3 + 8 * A ^ 2 + 12 * A + 16) + 16) := by
    unfold jacobiDeterminantBlindValue
    ring
  nlinarith

/-- **Sharp determinant applicability no-go.** For every integer `A≥2`, the irreducible monic
integer polynomial above has fixed trace coefficient `1`, fixed norm `1`, and fixed linear
coefficient `1`, yet has a real root between `A/2` and `A`.  Thus even an exact evaluation of the
Wu--Wang--Pan Jacobi determinant (the linear coefficient), combined with trace, norm and
irreducibility, cannot upper-bound the house.  What is missing is quantitative control of the
*other* conjugates (and, for the period application, their total-real ramified profile). -/
theorem exists_large_real_root_of_fixed_jacobi_coefficient (A : Nat) (hA : 2 ≤ A) :
    ∃ x : ℝ, (A : ℝ) / 2 ≤ x ∧ x ≤ (A : ℝ) ∧
      jacobiDeterminantBlindValue (A : ℝ) x = 0 := by
  let f : ℝ → ℝ := fun x => jacobiDeterminantBlindValue (A : ℝ) x
  have hab : (A : ℝ) / 2 ≤ (A : ℝ) := by
    have hA0 : (0 : ℝ) ≤ A := by positivity
    linarith
  have hleft : f ((A : ℝ) / 2) < 0 :=
    jacobiDeterminantBlindValue_at_half_neg (A : ℝ) (by exact_mod_cast hA)
  have hright : 0 < f (A : ℝ) := by
    dsimp only [f]
    rw [jacobiDeterminantBlindValue_at_right]
    positivity
  have hf : Continuous f := by
    dsimp only [f, jacobiDeterminantBlindValue]
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (f ((A : ℝ) / 2)) (f (A : ℝ)) := ⟨hleft.le, hright.le⟩
  obtain ⟨x, hx, hfx⟩ :=
    (intermediate_value_Icc hab hf.continuousOn hzero :
      ∃ x ∈ Set.Icc ((A : ℝ) / 2) (A : ℝ), f x = 0)
  exact ⟨x, hx.1, hx.2, hfx⟩

/-! ## The exact period-power congruence and the literal spike -/

/-- Necessary residue condition supplied by the distinct-period moment law:
`q | n * sum_i |eta_i|^(2r) + n^(2r)`. -/
def PeriodPowerCongruence (r moment : Nat) : Prop :=
  productionQ ∣ productionN * moment + productionN ^ (2 * r)

/-- The literal orbit spike's depth-two residue. -/
def literalDepthTwoResidue : Nat :=
  (productionN * literalOrbitPowerMoment 2 + productionN ^ 4) % productionQ

/-- Exact nonzero residue of the literal spike at depth two. -/
theorem literalDepthTwoResidue_eq :
    literalDepthTwoResidue = 87113604775161076552801107946821851807744 := by
  norm_num [literalDepthTwoResidue, literalOrbitPowerMoment, productionSpike,
    productionLiteralBulkOrbits,
    productionQ, productionM, productionN]

/-- The residue is a 137-bit integer. -/
theorem literalDepthTwoResidue_bit_window :
    2 ^ 136 < literalDepthTwoResidue ∧ literalDepthTwoResidue < 2 ^ 137 := by
  rw [literalDepthTwoResidue_eq]
  norm_num

/-- The literal spike violates an exact necessary period-polynomial congruence already at `r=2`. -/
theorem literal_spike_fails_depthTwo_periodCongruence :
    ¬ PeriodPowerCongruence 2 (literalOrbitPowerMoment 2) := by
  rw [PeriodPowerCongruence, Nat.dvd_iff_mod_eq_zero]
  change literalDepthTwoResidue ≠ 0
  rw [literalDepthTwoResidue_eq]
  norm_num

/-! ## A nonzero integral signed spike satisfying trace and lower moments -/

/-- Squared amplitude of the integral spike, `(2^26)^2`. -/
def integralSpikeSquared : Nat := 2 ^ 52

/-- Its size relative to the baseline squared amplitude `n`: `2^52 = 2^22*n`. -/
def integralSpikeScale : Nat := 2 ^ 22

/-- Four equal half-amplitude blocks.  The identity `3 * ((2^22-1)/3) = 2^22-1` is what makes
the squared trace exact without zero entries. -/
def productionHalfCount : Nat := 4 * ((integralSpikeScale - 1) / 3)

/-- Number of baseline-amplitude entries. -/
def productionBulkCount : Nat := productionM - productionHalfCount - 2

/-- The orbit-level even power sum of the nonzero integral signed profile. -/
def integralOrbitPowerMoment (r : Nat) : Nat :=
  integralSpikeSquared ^ r + productionBulkCount * productionN ^ r
    + productionHalfCount * (productionN / 4) ^ r + 1

/-- Positive and negative bulk counts, with signed excess `-2048`. -/
def productionBulkPositive : Nat := (productionBulkCount - 2048) / 2
def productionBulkNegative : Nat := (productionBulkCount + 2048) / 2

/-- The half-amplitude block is sign-balanced. -/
def productionHalfPositive : Nat := productionHalfCount / 2
def productionHalfNegative : Nat := productionHalfCount / 2

/-- The bucket counts make exactly `m` conjugate slots. -/
theorem integral_profile_orbit_count :
    1 + productionBulkPositive + productionBulkNegative
      + productionHalfPositive + productionHalfNegative + 1 = productionM := by
  norm_num [productionBulkPositive, productionBulkNegative, productionHalfPositive,
    productionHalfNegative, productionBulkCount, productionHalfCount, integralSpikeScale,
    productionM]

/-- Every amplitude used by the strengthened profile is nonzero. -/
theorem integral_profile_has_no_zero_amplitude :
    0 < 2 ^ 26 ∧ 0 < 2 ^ 15 ∧ 0 < 2 ^ 14 ∧ 0 < (1 : Nat) := by
  norm_num

/-- Signed trace certificate: the spike is cancelled by the `-2048` bulk excess, the half block
is sign-balanced, and the final unit contributes the exact period trace `-1`. -/
theorem integral_profile_signed_trace :
    (2 ^ 26 : Int)
      + (productionBulkPositive : Int) * 2 ^ 15
      - (productionBulkNegative : Int) * 2 ^ 15
      + (productionHalfPositive : Int) * 2 ^ 14
      - (productionHalfNegative : Int) * 2 ^ 14
      - 1 = -1 := by
  norm_num [productionBulkPositive, productionBulkNegative, productionHalfPositive,
    productionHalfNegative, productionBulkCount, productionHalfCount, integralSpikeScale,
    productionM]

/-- Exact squared trace `sum_i eta_i^2 = q-n`. -/
theorem integral_profile_squared_trace :
    integralOrbitPowerMoment 1 = productionQ - productionN := by
  norm_num [integralOrbitPowerMoment, integralSpikeSquared, productionBulkCount,
    productionHalfCount, integralSpikeScale, productionQ, productionM, productionN]

/-- Depth-two Wick ceiling. -/
theorem integral_profile_moment_two_le_wick :
    integralOrbitPowerMoment 2
      ≤ productionQ * wickCoefficient 2 * productionN ^ 1 := by
  norm_num [integralOrbitPowerMoment, integralSpikeSquared, productionBulkCount,
    productionHalfCount, integralSpikeScale, productionQ, productionM, productionN,
    wickCoefficient, Nat.doubleFactorial]

/-- Depth-three Wick ceiling. -/
theorem integral_profile_moment_three_le_wick :
    integralOrbitPowerMoment 3
      ≤ productionQ * wickCoefficient 3 * productionN ^ 2 := by
  norm_num [integralOrbitPowerMoment, integralSpikeSquared, productionBulkCount,
    productionHalfCount, integralSpikeScale, productionQ, productionM, productionN,
    wickCoefficient, Nat.doubleFactorial]

/-- Depth-four Wick ceiling. -/
theorem integral_profile_moment_four_le_wick :
    integralOrbitPowerMoment 4
      ≤ productionQ * wickCoefficient 4 * productionN ^ 3 := by
  norm_num [integralOrbitPowerMoment, integralSpikeSquared, productionBulkCount,
    productionHalfCount, integralSpikeScale, productionQ, productionM, productionN,
    wickCoefficient, Nat.doubleFactorial]

/-- Depth-five Wick ceiling. -/
theorem integral_profile_moment_five_le_wick :
    integralOrbitPowerMoment 5
      ≤ productionQ * wickCoefficient 5 * productionN ^ 4 := by
  norm_num [integralOrbitPowerMoment, integralSpikeSquared, productionBulkCount,
    productionHalfCount, integralSpikeScale, productionQ, productionM, productionN,
    wickCoefficient, Nat.doubleFactorial]

/-- Depth-six Wick ceiling. -/
theorem integral_profile_moment_six_le_wick :
    integralOrbitPowerMoment 6
      ≤ productionQ * wickCoefficient 6 * productionN ^ 5 := by
  norm_num [integralOrbitPowerMoment, integralSpikeSquared, productionBulkCount,
    productionHalfCount, integralSpikeScale, productionQ, productionM, productionN,
    wickCoefficient, Nat.doubleFactorial]

/-- Orbit-level public seventh-moment target.  Multiplication by the orbit size `n` recovers the
field-frequency target `q*2^18*n^7`. -/
def productionOrbitSeventhTarget : Nat := productionQ * 2 ^ 18 * productionN ^ 6

/-- Even after imposing nonzero integral amplitudes and the exact signed trace, the profile exceeds
the seventh target by more than eight bits. -/
theorem integral_profile_eight_bit_target_failure :
    2 ^ 8 * productionOrbitSeventhTarget < integralOrbitPowerMoment 7 := by
  norm_num [productionOrbitSeventhTarget, integralOrbitPowerMoment, integralSpikeSquared,
    productionBulkCount, productionHalfCount, integralSpikeScale, productionQ, productionM,
    productionN]

/-- The strengthened profile's failure is below nine bits. -/
theorem integral_profile_target_failure_lt_nine_bits :
    integralOrbitPowerMoment 7 < 2 ^ 9 * productionOrbitSeventhTarget := by
  norm_num [productionOrbitSeventhTarget, integralOrbitPowerMoment, integralSpikeSquared,
    productionBulkCount, productionHalfCount, integralSpikeScale, productionQ, productionM,
    productionN]

/-- The strengthened integral profile still fails the actual period congruence at depth two. -/
theorem integral_profile_fails_depthTwo_periodCongruence :
    ¬ PeriodPowerCongruence 2 (integralOrbitPowerMoment 2) := by
  rw [PeriodPowerCongruence, Nat.dvd_iff_mod_eq_zero]
  norm_num [integralOrbitPowerMoment, integralSpikeSquared, productionBulkCount,
    productionHalfCount, integralSpikeScale, productionQ, productionM, productionN]

/-- A single seventh-moment congruence has `2^198` complete residue steps below the public orbit
target, so congruence information without an archimedean coupling is far too coarse. -/
theorem production_seventh_congruence_step_count :
    productionOrbitSeventhTarget / productionQ = 2 ^ 198 := by
  norm_num [productionOrbitSeventhTarget, productionQ, productionM, productionN]

/-! ## Production size of the discriminant/capacity information -/

/-- The field cardinality lies in its exact binary window. -/
theorem productionQ_binary_window : 2 ^ 158 < productionQ ∧ productionQ < 2 ^ 159 := by
  norm_num [productionQ, productionM, productionN]

/-- The class-field discriminant contribution has binary logarithm per conjugate below `2^-120`:
`log_2(q)/m < 159/m < 2^-120`.  This is why the Fekete/discriminant datum gives only an essentially
unit lower bound and cannot exclude an archimedean `2^52` squared spike. -/
theorem production_discriminant_log_budget :
    (159 : Rat) / productionM < 1 / (2 ^ 120 : Rat) := by
  norm_num [productionM]

/-! ## Consolidated boundary -/

/-- The exact package proved by this audit.  It records both sides of the boundary: Galois and
period-congruence structure really do exclude the literal scalar spike, while a stronger nonzero
integral/trace-correct profile continues to pass all scalar lower-moment tests and fail depth seven.
The missing theorem must use the Galois/congruence data quantitatively, not merely assert it. -/
theorem period_profile_arithmetic_boundary
    {K : Type*} [Field K] [Algebra ℚ K]
    (eta : K) (sigma : Fin productionM → K →ₐ[ℚ] ℂ)
    (hsum : ∑ i, sigma i (eta ^ 2) = ((productionQ - productionN : Nat) : ℂ)) :
    (∀ i, sigma i (eta ^ 2) ≠ (productionSpike : ℂ)) ∧
    ¬ PeriodPowerCongruence 2 (literalOrbitPowerMoment 2) ∧
    integralOrbitPowerMoment 1 = productionQ - productionN ∧
    integralOrbitPowerMoment 6
      ≤ productionQ * wickCoefficient 6 * productionN ^ 5 ∧
    2 ^ 8 * productionOrbitSeventhTarget < integralOrbitPowerMoment 7 := by
  exact ⟨rational_squared_spike_incompatible_with_sum eta sigma hsum,
    literal_spike_fails_depthTwo_periodCongruence,
    integral_profile_squared_trace,
    integral_profile_moment_six_le_wick,
    integral_profile_eight_bit_target_failure⟩

end ArkLib.ProximityGap.Frontier.BGKPeriodProfileArithmeticAudit

/-! ## Axiom audit (expected: standard axioms only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKPeriodProfileArithmeticAudit.jacobiDeterminantBlindPoly_irreducible
#print axioms
  ArkLib.ProximityGap.Frontier.BGKPeriodProfileArithmeticAudit.exists_large_real_root_of_fixed_jacobi_coefficient
#print axioms
  ArkLib.ProximityGap.Frontier.BGKPeriodProfileArithmeticAudit.period_profile_arithmetic_boundary
