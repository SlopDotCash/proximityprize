/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R395PairMultiplicitySixRootReduction

/-!
# R396: simultaneous cyclotomic Bezout certificates

For two collision polynomials `f,g`, the relevant arithmetic object is the ideal
`(Phi_n,f,g)`, not the gcd of the two separate integer norms.  This file gives the exact certificate
interface: an identity

`A*f + B*g + C*Phi = const D`

forces every common root modulo `p` to satisfy `p | D`.  Hence `0 < |D| < p` excludes a simultaneous
root. This is the consumer needed for the R395 three-support obstruction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.R396SimultaneousCyclotomicBezoutCertificate

/-- An explicit integer generator in the simultaneous ideal `(phi,f,g)`. -/
def SimultaneousBezoutCertificate (phi f g : ℤ[X]) (D : ℤ) : Prop :=
  ∃ A B C : ℤ[X], A * f + B * g + C * phi = Polynomial.C D

/-- A simultaneous Bezout certificate forces its integer constant to vanish at every common root
after mapping to an arbitrary commutative ring. -/
theorem intCast_eq_zero_of_common_root
    {R : Type*} [CommRing R] (algebraMap : ℤ →+* R)
    {phi f g : ℤ[X]} {D : ℤ} (hcert : SimultaneousBezoutCertificate phi f g D)
    {x : R} (hphi : Polynomial.eval₂ algebraMap x phi = 0)
    (hf : Polynomial.eval₂ algebraMap x f = 0)
    (hg : Polynomial.eval₂ algebraMap x g = 0) :
    algebraMap D = 0 := by
  obtain ⟨A, B, C, hbez⟩ := hcert
  have h := congrArg (Polynomial.eval₂ algebraMap x) hbez
  have h' : 0 = Polynomial.eval₂ algebraMap x (Polynomial.C D) := by
    simpa [map_add, map_mul, hphi, hf, hg] using h
  rw [Polynomial.eval₂_C] at h'
  exact h'.symm

/-- Over `ZMod p`, a simultaneous common root forces `p` to divide the certificate integer. -/
theorem prime_dvd_of_common_root
    {p : ℕ} [Fact p.Prime] {phi f g : ℤ[X]} {D : ℤ}
    (hcert : SimultaneousBezoutCertificate phi f g D)
    {x : ZMod p} (hphi : Polynomial.eval₂ (Int.castRingHom (ZMod p)) x phi = 0)
    (hf : Polynomial.eval₂ (Int.castRingHom (ZMod p)) x f = 0)
    (hg : Polynomial.eval₂ (Int.castRingHom (ZMod p)) x g = 0) :
    (p : ℤ) ∣ D := by
  have hzero := intCast_eq_zero_of_common_root (Int.castRingHom (ZMod p)) hcert hphi hf hg
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp hzero

/-- **Exact prime-selective criterion.** If `p` does not divide one simultaneous Bezout constant,
then `phi,f,g` have no common root modulo `p`. This is stronger and more useful than a size bound
when the certificate has large composite factors. -/
theorem no_common_root_of_not_dvd
    {p : ℕ} [Fact p.Prime] {phi f g : ℤ[X]} {D : ℤ}
    (hcert : SimultaneousBezoutCertificate phi f g D) (hnD : ¬ (p : ℤ) ∣ D) :
    ¬ ∃ x : ZMod p,
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x phi = 0 ∧
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x f = 0 ∧
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x g = 0 := by
  rintro ⟨x, hphi, hf, hg⟩
  exact hnD (prime_dvd_of_common_root hcert hphi hf hg)

/-- **No-common-root criterion.** A nonzero certificate smaller than `p` excludes a simultaneous
root of `phi,f,g` in `ZMod p`. -/
theorem no_common_root_of_natAbs_lt_prime
    {p : ℕ} [Fact p.Prime] {phi f g : ℤ[X]} {D : ℤ}
    (hcert : SimultaneousBezoutCertificate phi f g D)
    (hD0 : D ≠ 0) (hDp : D.natAbs < p) :
    ¬ ∃ x : ZMod p,
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x phi = 0 ∧
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x f = 0 ∧
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x g = 0 := by
  rintro ⟨x, hphi, hf, hg⟩
  have hdvdZ := prime_dvd_of_common_root hcert hphi hf hg
  have hdvd : p ∣ D.natAbs := by
    exact Int.natAbs_dvd_natAbs.mpr hdvdZ
  have hpos : 0 < D.natAbs := Int.natAbs_pos.mpr hD0
  have hle : p ≤ D.natAbs := Nat.le_of_dvd hpos hdvd
  omega

/-- Contrapositive form: any simultaneous root makes every nonzero Bezout constant at least `p` in
absolute value. -/
theorem prime_le_natAbs_of_common_root
    {p : ℕ} [Fact p.Prime] {phi f g : ℤ[X]} {D : ℤ}
    (hcert : SimultaneousBezoutCertificate phi f g D) (hD0 : D ≠ 0)
    {x : ZMod p} (hphi : Polynomial.eval₂ (Int.castRingHom (ZMod p)) x phi = 0)
    (hf : Polynomial.eval₂ (Int.castRingHom (ZMod p)) x f = 0)
    (hg : Polynomial.eval₂ (Int.castRingHom (ZMod p)) x g = 0) :
    p ≤ D.natAbs := by
  have hdvdZ := prime_dvd_of_common_root hcert hphi hf hg
  have hdvd : p ∣ D.natAbs := Int.natAbs_dvd_natAbs.mpr hdvdZ
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD0) hdvd

end ArkLib.ProximityGap.Frontier.R396SimultaneousCyclotomicBezoutCertificate

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R396SimultaneousCyclotomicBezoutCertificate.no_common_root_of_natAbs_lt_prime
#print axioms
  ArkLib.ProximityGap.Frontier.R396SimultaneousCyclotomicBezoutCertificate.no_common_root_of_not_dvd
#print axioms
  ArkLib.ProximityGap.Frontier.R396SimultaneousCyclotomicBezoutCertificate.prime_le_natAbs_of_common_root
