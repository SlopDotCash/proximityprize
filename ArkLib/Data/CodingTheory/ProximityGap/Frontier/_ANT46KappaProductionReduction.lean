/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ANT46RungTwoAccidentOrbit

/-!
# Exact production reductions for the ANT46 cyclotomic-unit signature

The depth-two marked-overlap residual is empty if

`kappa_n(x) = (x - 1)^n`

is injective on the nontrivial `n`-th roots modulo inversion.  This file records two exact
ways to present that remaining arithmetic question.

First, after choosing one representative from every non-self inversion orbit, injectivity is
equivalent to one nonvanishing product: the ordered discriminant of the representative
signatures times the value at the self-inverse class.  For `n = 2^30` the corresponding monic
polynomial has degree `2^29 - 1 = 536870911`; its discriminant has Sylvester order
`2^30 - 3 = 1073741821`.  Thus a literal polynomial-gcd or discriminant computation is still a
billion-scale state, not a logarithmic certificate.

Second, a prime divisor `r` of the cofactor `(P-1)/n` gives a sufficient character projection.
Raising every signature to `((P-1)/n)/r` sends it into `mu_r`; injectivity after this projection
implies the original injectivity.  For the two certified production primes we use their largest
already-certified cofactor prime:

* first prime: `r = 462478642316479903` (59 bits), projected exponent has 100 bits;
* second prime: `r = 90308905535905320959` (67 bits), projected exponent has 93 bits.

Both target groups are much larger than the `2^29` inversion classes.  This removes the many
small CRT components of the cofactor, but does not prove projected injectivity: that remains a
prime-specific power-residue separation problem.  In particular, the existing Lucas primality
and order certificates prove the ambient group shapes below, not the nonvanishing separation
product.  Issue #466.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.ANT46KappaProductionReduction

open ANT46RungTwoAccidentOrbit

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## A representative-free statement of the canonical discriminant criterion -/

/-- `S` contains one representative from each non-self inversion class of `H`, while `self`
is the unique class represented separately.  The last condition rules out putting both `x` and
`x⁻¹` in `S`. -/
def IsInversionTransversal (H S : Finset F) (self : F) : Prop :=
  self ∈ H ∧ self ≠ 1 ∧ self⁻¹ = self ∧
    (∀ x ∈ S, x ∈ H ∧ x ≠ 1 ∧ x ≠ self) ∧
    (∀ x ∈ S, ∀ y ∈ S, y = x⁻¹ → y = x) ∧
    ∀ x ∈ H, x ≠ 1 → x = self ∨ ∃ a ∈ S, x = a ∨ x = a⁻¹

/-- The canonical ordered discriminant-times-self-value certificate.  If
`K(T) = product_(x in S) (T-kappa_n(x))`, this differs from
`Disc(K) * K(kappa_n(self))` only by a nonzero sign and by duplicating every pair factor. -/
def kappaSeparationCertificate (S : Finset F) (n : Nat) (self : F) : F :=
  (∏ x ∈ S, (differenceSignature n self - differenceSignature n x)) *
    ∏ x ∈ S, ∏ y ∈ S.erase x,
      (differenceSignature n x - differenceSignature n y)

/-- Nonvanishing of the explicit certificate says exactly that the self value is separate and
that all representative values are pairwise distinct. -/
theorem kappaSeparationCertificate_ne_zero_iff (S : Finset F) (n : Nat) (self : F) :
    kappaSeparationCertificate S n self ≠ 0 ↔
      (∀ x ∈ S, differenceSignature n x ≠ differenceSignature n self) ∧
        (∀ x ∈ S, ∀ y ∈ S, y ≠ x →
          differenceSignature n x ≠ differenceSignature n y) := by
  simp only [kappaSeparationCertificate, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
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

/-- Even cyclotomic-unit signatures are invariant under inversion on the `n`-th-root locus. -/
theorem differenceSignature_inv_of_even {n : Nat} (hn : Even n) (x : F) (hx : x ≠ 0)
    (hpow : x ^ n = 1) :
    differenceSignature n x⁻¹ = differenceSignature n x := by
  have hrewrite : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by
    field_simp
    ring
  rw [differenceSignature, differenceSignature, hrewrite, mul_pow, hn.neg_pow,
    inv_pow, hpow, inv_one, mul_one]

/-- The exact canonical criterion: on a complete inversion transversal, ANT46 signature
injectivity is equivalent to nonvanishing of one discriminant-times-self-value product. -/
theorem differenceSignatureInjectiveModInversion_iff_separationCertificate_ne_zero
    {H S : Finset F} {n : Nat} {self : F}
    (hnpos : 0 < n) (hneven : Even n)
    (hpow : ∀ x ∈ H, x ^ n = 1)
    (htrans : IsInversionTransversal H S self) :
    DifferenceSignatureInjectiveModInversion H n ↔
      kappaSeparationCertificate S n self ≠ 0 := by
  rcases htrans with ⟨hselfH, hself1, hselfInv, hSH, hnoInvDup, hcover⟩
  rw [kappaSeparationCertificate_ne_zero_iff]
  constructor
  · intro hinjective
    constructor
    · intro x hxS hxeq
      rcases hSH x hxS with ⟨hxH, hx1, hxself⟩
      rcases hinjective x hxH hx1 self hselfH hself1 hxeq with h | h
      · exact hxself h.symm
      · apply hxself
        calc
          x = (x⁻¹)⁻¹ := (inv_inv x).symm
          _ = self⁻¹ := congrArg Inv.inv h.symm
          _ = self := hselfInv
    · intro x hxS y hyS hyx hxy
      rcases hSH x hxS with ⟨hxH, hx1, _hxself⟩
      rcases hSH y hyS with ⟨hyH, hy1, _hyself⟩
      rcases hinjective x hxH hx1 y hyH hy1 hxy with h | h
      · exact hyx h
      · exact hyx (hnoInvDup x hxS y hyS h)
  · rintro ⟨hselfSep, hpairSep⟩
    intro x hxH hx1 y hyH hy1 hxy
    have signature_inv (z : F) (hzH : z ∈ H) :
        differenceSignature n z⁻¹ = differenceSignature n z := by
      have hzpow := hpow z hzH
      have hz0 : z ≠ 0 := by
        intro hz
        subst z
        simpa [zero_pow hnpos.ne'] using hzpow
      exact differenceSignature_inv_of_even hneven z hz0 hzpow
    have signature_of_representative (z a : F) (haS : a ∈ S)
        (hza : z = a ∨ z = a⁻¹) :
        differenceSignature n z = differenceSignature n a := by
      rcases hza with hza | hza
      · exact congrArg (differenceSignature n) hza
      · exact (congrArg (differenceSignature n) hza).trans
          (signature_inv a (hSH a haS).1)
    rcases hcover x hxH hx1 with hxself | ⟨a, haS, hxa⟩
    · rcases hcover y hyH hy1 with hyself | ⟨b, hbS, hyb⟩
      · exact Or.inl (hyself.trans hxself.symm)
      · have hybSig := signature_of_representative y b hbS hyb
        exact (hselfSep b hbS (hybSig.symm.trans (hxy.symm.trans
          (congrArg (differenceSignature n) hxself)))).elim
    · rcases hcover y hyH hy1 with hyself | ⟨b, hbS, hyb⟩
      · have hxaSig := signature_of_representative x a haS hxa
        exact (hselfSep a haS (hxaSig.symm.trans (hxy.trans
          (congrArg (differenceSignature n) hyself)))).elim
      · have hxaSig := signature_of_representative x a haS hxa
        have hybSig := signature_of_representative y b hbS hyb
        have habSig : differenceSignature n a = differenceSignature n b :=
          hxaSig.symm.trans (hxy.trans hybSig)
        have hab : a = b := by
          by_contra hab
          exact hpairSep a haS b hbS (fun hba ↦ hab hba.symm) habSig
        rcases hxa with hxa | hxa <;> rcases hyb with hyb | hyb
        · exact Or.inl (hyb.trans (hab.symm.trans hxa.symm))
        · apply Or.inr
          exact hyb.trans (congrArg Inv.inv (hab.symm.trans hxa.symm))
        · apply Or.inr
          calc
            y = b := hyb
            _ = a := hab.symm
            _ = (a⁻¹)⁻¹ := (inv_inv a).symm
            _ = x⁻¹ := (congrArg Inv.inv hxa).symm
        · apply Or.inl
          exact hyb.trans ((congrArg Inv.inv hab.symm).trans hxa.symm)

/-! ## Prime-factor character projections -/

/-- Raise the ANT46 signature through a selected cofactor quotient. -/
def projectedDifferenceSignature (n e : Nat) (x : F) : F :=
  (differenceSignature n x) ^ e

/-- Injectivity modulo inversion after a power projection of the signature. -/
def ProjectedDifferenceSignatureInjectiveModInversion
    (H : Finset F) (n e : Nat) : Prop :=
  ∀ x ∈ H, x ≠ 1 → ∀ y ∈ H, y ≠ 1 →
    projectedDifferenceSignature n e x = projectedDifferenceSignature n e y →
      y = x ∨ y = x⁻¹

/-- Separation after any power projection is a sufficient certificate for the original ANT46
signature injectivity. -/
theorem differenceSignatureInjectiveModInversion_of_projected
    {H : Finset F} {n e : Nat}
    (hprojected : ProjectedDifferenceSignatureInjectiveModInversion H n e) :
    DifferenceSignatureInjectiveModInversion H n := by
  intro x hxH hx1 y hyH hy1 hxy
  apply hprojected x hxH hx1 y hyH hy1
  exact congrArg (fun z : F ↦ z ^ e) hxy

/-! ## Exact production arithmetic -/

abbrev productionN : Nat := 2 ^ 30

abbrev firstP : Nat := ArkLib.ProximityGap.PrizeShapePrimeP30.P
abbrev firstProjectionOrder : Nat := 462478642316479903
abbrev firstProjectionPower : Nat := 735779635609808324416
abbrev firstProjectedExponent : Nat := 790037368001730942548819574784

abbrev secondP : Nat := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
abbrev secondProjectionOrder : Nat := 90308905535905320959
abbrev secondProjectionPower : Nat := 7535964806608089075
abbrev secondProjectedExponent : Nat := 8091680597047176816544972800

theorem first_projection_exact_shape :
    firstP - 1 = productionN * firstProjectionPower * firstProjectionOrder ∧
      productionN * firstProjectionPower = firstProjectedExponent := by
  norm_num [firstP, productionN, firstProjectionPower, firstProjectionOrder,
    firstProjectedExponent, ArkLib.ProximityGap.PrizeShapePrimeP30.P]

theorem second_projection_exact_shape :
    secondP - 1 = productionN * secondProjectionPower * secondProjectionOrder ∧
      productionN * secondProjectionPower = secondProjectedExponent := by
  norm_num [secondP, productionN, secondProjectionPower, secondProjectionOrder,
    secondProjectedExponent, ArkLib.ProximityGap.PrizeShapePrimeP30Second.P]

theorem first_projection_order_prime : Nat.Prime firstProjectionOrder := by
  exact ArkLib.ProximityGap.PrizeShapePrimeP30.prime_462478642316479903

theorem second_projection_order_prime : Nat.Prime secondProjectionOrder := by
  exact ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_90308905535905320959

/-- Both selected prime-order targets are larger than the entire production inversion quotient. -/
theorem projection_orders_exceed_inversion_class_count :
    productionN / 2 < firstProjectionOrder ∧
      productionN / 2 < secondProjectionOrder := by
  norm_num [productionN, firstProjectionOrder, secondProjectionOrder]

/-- Exact state dimensions of the literal canonical polynomial certificate. -/
theorem production_canonical_state_dimensions :
    productionN / 2 - 1 = 536870911 ∧
      2 * (productionN / 2 - 1) - 1 = 1073741821 ∧
      (productionN / 2 - 1) * (productionN / 2 - 2) / 2 = 144115187270549505 := by
  norm_num [productionN]

local instance firstPrimeFact : Fact (Nat.Prime firstP) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance secondPrimeFact : Fact (Nat.Prime secondP) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- First-prime production adapter: the 59-bit prime-factor projection is sufficient for the
original signature socket. -/
theorem firstPrime_differenceSignatureInjectiveModInversion_of_projection
    {H : Finset (ZMod firstP)}
    (hprojected : ProjectedDifferenceSignatureInjectiveModInversion
      H productionN firstProjectionPower) :
    DifferenceSignatureInjectiveModInversion H productionN :=
  differenceSignatureInjectiveModInversion_of_projected hprojected

/-- Second-prime production adapter: the 67-bit prime-factor projection is sufficient for the
original signature socket. -/
theorem secondPrime_differenceSignatureInjectiveModInversion_of_projection
    {H : Finset (ZMod secondP)}
    (hprojected : ProjectedDifferenceSignatureInjectiveModInversion
      H productionN secondProjectionPower) :
    DifferenceSignatureInjectiveModInversion H productionN :=
  differenceSignatureInjectiveModInversion_of_projected hprojected

end ArkLib.ProximityGap.Frontier.ANT46KappaProductionReduction

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaProductionReduction.differenceSignatureInjectiveModInversion_iff_separationCertificate_ne_zero
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaProductionReduction.differenceSignatureInjectiveModInversion_of_projected
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaProductionReduction.first_projection_exact_shape
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaProductionReduction.second_projection_exact_shape
#print axioms ArkLib.ProximityGap.Frontier.ANT46KappaProductionReduction.production_canonical_state_dimensions
