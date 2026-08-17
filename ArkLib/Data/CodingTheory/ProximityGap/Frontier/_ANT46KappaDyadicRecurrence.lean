/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# The dyadic recurrence behind the ANT46 cyclotomic-unit signature

For `kappa n x = (x - 1)^n`, inversion identifies the two roots in an inversion class.
When the order doubles, old classes simply square their old signatures.  The new primitive
classes form a genuinely new half-angle channel.  Writing `t = x + x⁻¹` gives the exact law

`kappa (2*n) x = x^n * (t - 2)^n`.

Thus the old channel (`x^n = 1`) has sign `+1`, while the primitive channel
(`x^n = -1`) has sign `-1`.  Pairing primitive traces `t` and `-t` gives the quadratic factor

`T^2 + ((t-2)^n + (t+2)^n)T + (t^2-4)^n`.

The coefficient in this factor has a square-and-subtract recurrence.  This is the small
arithmetic circuit behind the exact resultant recurrence; it also records why the scalar
polynomial `K_n` alone is not a closed state under doubling.

The final section certifies the exact dimensions at the two production primes.  Although the
trace and coefficient circuits have only 28 dyadic steps, the final primitive norm has degree
`2^28`, and the full canonical polynomial has degree `2^29 - 1`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence

variable {F : Type*} [Field F]

/-- The ANT46 cyclotomic-unit signature. -/
def kappa (n : ℕ) (x : F) : F := (x - 1) ^ n

/-- On doubling the exponent, every old signature is squared. -/
theorem kappa_two_mul (n : ℕ) (x : F) :
    kappa (2 * n) x = (kappa n x) ^ 2 := by
  simp only [kappa, pow_two]
  rw [← pow_add]
  congr 1
  omega

/-- The elementary trace identity from which both dyadic channels follow. -/
theorem sub_one_sq_eq_mul_trace (x : F) (hx : x ≠ 0) :
    (x - 1) ^ 2 = x * (x + x⁻¹ - 2) := by
  field_simp
  ring

/-- Trace form of the doubled signature. -/
theorem kappa_two_mul_eq_pow_trace (n : ℕ) (x : F) (hx : x ≠ 0) :
    kappa (2 * n) x = x ^ n * (x + x⁻¹ - 2) ^ n := by
  rw [kappa, show 2 * n = 2 * n from rfl, pow_mul, sub_one_sq_eq_mul_trace x hx, mul_pow]

/-- Old `n`-th roots contribute the positive trace channel. -/
theorem kappa_two_mul_of_pow_eq_one (n : ℕ) (x : F) (hx : x ≠ 0)
    (hpow : x ^ n = 1) :
    kappa (2 * n) x = (x + x⁻¹ - 2) ^ n := by
  rw [kappa_two_mul_eq_pow_trace n x hx, hpow, one_mul]

/-- New primitive `2*n`-th roots contribute the negative trace channel. -/
theorem kappa_two_mul_of_pow_eq_neg_one (n : ℕ) (x : F) (hx : x ≠ 0)
    (hpow : x ^ n = -1) :
    kappa (2 * n) x = -(x + x⁻¹ - 2) ^ n := by
  rw [kappa_two_mul_eq_pow_trace n x hx, hpow, neg_one_mul]

/-- Even signatures are invariant under inversion on the root-of-unity locus. -/
theorem kappa_inv_of_even {n : ℕ} (hn : Even n) (x : F) (hx : x ≠ 0)
    (hpow : x ^ n = 1) :
    kappa n x⁻¹ = kappa n x := by
  have hrewrite : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by
    field_simp
    ring
  rw [kappa, kappa, hrewrite, mul_pow, hn.neg_pow,
    inv_pow, hpow, inv_one, mul_one]

/-- The coefficient appearing after pairing the primitive traces `t` and `-t`. -/
def pairedTraceCoefficient (n : ℕ) (t : F) : F :=
  (t - 2) ^ n + (t + 2) ^ n

/-- Exact quadratic factor contributed by a primitive trace pair. -/
theorem primitive_trace_pair_factor {n : ℕ} (_hn : Even n) (t T : F) :
    (T + (t - 2) ^ n) * (T + (t + 2) ^ n) =
      T ^ 2 + pairedTraceCoefficient n t * T + (t ^ 2 - 4) ^ n := by
  rw [pairedTraceCoefficient]
  have hprod : (t - 2) ^ n * (t + 2) ^ n = (t ^ 2 - 4) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (T + (t - 2) ^ n) * (T + (t + 2) ^ n) =
        T ^ 2 + ((t - 2) ^ n + (t + 2) ^ n) * T +
          (t - 2) ^ n * (t + 2) ^ n := by ring
    _ = T ^ 2 + ((t - 2) ^ n + (t + 2) ^ n) * T + (t ^ 2 - 4) ^ n := by
      rw [hprod]

/-- Square-and-subtract recurrence for the paired-trace coefficient. -/
theorem pairedTraceCoefficient_two_mul (n : ℕ) (t : F) :
    pairedTraceCoefficient (2 * n) t =
      (pairedTraceCoefficient n t) ^ 2 - 2 * (t ^ 2 - 4) ^ n := by
  rw [pairedTraceCoefficient, pairedTraceCoefficient]
  have hprod : (t - 2) ^ n * (t + 2) ^ n = (t ^ 2 - 4) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (t - 2) ^ (2 * n) + (t + 2) ^ (2 * n) =
        ((t - 2) ^ n + (t + 2) ^ n) ^ 2 -
          2 * ((t - 2) ^ n * (t + 2) ^ n) := by
      rw [mul_comm 2 n]
      simp only [pow_mul]
      ring
    _ = ((t - 2) ^ n + (t + 2) ^ n) ^ 2 - 2 * (t ^ 2 - 4) ^ n := by
      rw [hprod]

section SeparationProduct

variable {A : Type*} [DecidableEq A] [DecidableEq F]

/-- An ordered discriminant-times-self-value product.  Compared with the usual discriminant,
the pair factors are duplicated and may differ by a unit; its nonvanishing predicate is exactly
the same and avoids choosing an ordering of the source classes. -/
def orderedSeparationProduct (S : Finset A) (f : A → F) (self : F) : F :=
  (∏ x ∈ S, (self - f x)) *
    ∏ x ∈ S, ∏ y ∈ S.erase x, (f x - f y)

/-- Exact nonvanishing criterion for the discriminant-times-self-value surrogate. -/
theorem orderedSeparationProduct_ne_zero_iff (S : Finset A) (f : A → F) (self : F) :
    orderedSeparationProduct S f self ≠ 0 ↔
      (∀ x ∈ S, f x ≠ self) ∧
        (∀ x ∈ S, ∀ y ∈ S, y ≠ x → f x ≠ f y) := by
  simp only [orderedSeparationProduct, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_erase, sub_ne_zero]
  constructor
  · rintro ⟨hself, hpairs⟩
    constructor
    · intro x hx h
      exact hself x hx h.symm
    · intro x hx y hy hyx h
      exact hpairs x hx y ⟨hyx, hy⟩ h
  · rintro ⟨hself, hpairs⟩
    constructor
    · intro x hx h
      exact hself x hx h.symm
    · intro x hx y hy h
      exact hpairs x hx y hy.2 hy.1 h

end SeparationProduct

/-! ## Exact production dimensions -/

abbrev productionOrder : ℕ := 2 ^ 30
abbrev canonicalDegree : ℕ := productionOrder / 2 - 1

theorem productionOrder_eq : productionOrder = 1073741824 := by norm_num
theorem canonicalDegree_eq : canonicalDegree = 536870911 := by norm_num

theorem canonicalCoefficientCount_eq : canonicalDegree + 1 = 536870912 := by norm_num

theorem unorderedPairCount_eq : canonicalDegree * (canonicalDegree - 1) / 2 =
    144115187270549505 := by norm_num

theorem discriminantSylvesterOrder_eq : 2 * canonicalDegree - 1 = 1073741821 := by norm_num

theorem finalPrimitiveFactorDegree_eq : productionOrder / 4 = 268435456 := by norm_num

theorem finalPairedTraceDegree_eq : productionOrder / 8 = 134217728 := by norm_num

theorem dyadicStepCount_eq : 30 - 2 = 28 := by norm_num

theorem firstPrime_shape :
    ArkLib.ProximityGap.PrizeShapePrimeP30.P =
      productionOrder * (2 ^ 128 + 192) + 1 := by norm_num

theorem firstPrime_cofactor_eq :
    (ArkLib.ProximityGap.PrizeShapePrimeP30.P - 1) / productionOrder =
      340282366920938463463374607431768211648 := by norm_num

theorem firstPrime_mod_order :
    ArkLib.ProximityGap.PrizeShapePrimeP30.P % productionOrder = 1 := by norm_num

theorem secondPrime_shape :
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.P =
      productionOrder * (2 * 2 ^ 128 + 13) + 1 := by norm_num

theorem secondPrime_cofactor_eq :
    (ArkLib.ProximityGap.PrizeShapePrimeP30Second.P - 1) / productionOrder =
      680564733841876926926749214863536422925 := by norm_num

theorem secondPrime_mod_order :
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.P % productionOrder = 1 := by norm_num

end ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence.kappa_inv_of_even
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence.primitive_trace_pair_factor
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence.pairedTraceCoefficient_two_mul
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence.orderedSeparationProduct_ne_zero_iff
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence.firstPrime_shape
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaDyadicRecurrence.secondPrime_shape
