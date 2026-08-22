/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rigidity of one-root extensions of a locator line

Suppose three same-degree locators already lie on a polynomial line,

`pC = u * pA + v * pB`.

One tempting way to improve the rate-quarter smooth construction is to append
one new root to each locator.  The identity below isolates the obstruction.  If
the four natural directions

`X*pA, X*pB, pA, pB`

are linearly rigid, then collinearity of the three extended locators forces all
three appended roots to be the same.  In particular, this operation cannot
produce three pairwise-disjoint root sets.

The statement is field-universal and contains no finite-field computation.  It
does not rule out a genuinely new higher-degree locator identity: it only rules
out adjoining one independent root to an existing rigid identity.
-/

set_option autoImplicit false

open Polynomial
open scoped Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOneRootExtensionRigidity

variable {F : Type} [Field F]

/-- The four displayed polynomial directions have no nontrivial scalar
relation.  This is the exact independence input used by the extension lemma. -/
def FourDirectionRigid (pA pB : F[X]) : Prop :=
  ∀ sX tX s t : F,
    C sX * (X * pA) + C tX * (X * pB) + C s * pA + C t * pB = 0 →
      sX = 0 ∧ tX = 0 ∧ s = 0 ∧ t = 0

/-- Two polynomials admit no nontrivial scalar relation. -/
def ScalarPairRigid (pA pB : F[X]) : Prop :=
  ∀ s t : F, C s * pA + C t * pB = 0 → s = 0 ∧ t = 0

/-- Squaring-composition separates the odd directions `X*pA,X*pB` from the
even directions `pA,pB`.  Thus scalar rigidity of the base pair upgrades to
four-direction rigidity after the standard `X ↦ X²` dyadic lift. -/
theorem fourDirectionRigid_comp_sq
    (pA pB : F[X]) (hpair : ScalarPairRigid pA pB)
    (h2 : (2 : F) ≠ 0) :
    FourDirectionRigid (pA.comp (X ^ 2)) (pB.comp (X ^ 2)) := by
  intro sX tX s t hrelation
  let qA : F[X] := pA.comp (X ^ 2)
  let qB : F[X] := pB.comp (X ^ 2)
  have hqAneg : qA.comp (-X) = qA := by
    simp only [qA, comp_assoc, X_pow_comp, neg_sq]
  have hqBneg : qB.comp (-X) = qB := by
    simp only [qB, comp_assoc, X_pow_comp, neg_sq]
  change C sX * (X * qA) + C tX * (X * qB) +
      C s * qA + C t * qB = 0 at hrelation
  have hneg := congrArg (fun p : F[X] ↦ p.comp (-X)) hrelation
  simp only [add_comp, mul_comp, C_comp, X_comp, zero_comp,
    hqAneg, hqBneg] at hneg
  have hoddTwice :
      C (2 : F) * (C sX * (X * qA) + C tX * (X * qB)) = 0 := by
    simp only [map_ofNat]
    linear_combination hrelation - hneg
  have hevenTwice :
      C (2 : F) * (C s * qA + C t * qB) = 0 := by
    simp only [map_ofNat]
    linear_combination hrelation + hneg
  have hC2 : C (2 : F) ≠ (0 : F[X]) := C_ne_zero.mpr h2
  have hodd : C sX * (X * qA) + C tX * (X * qB) = 0 :=
    (mul_eq_zero.mp hoddTwice).resolve_left hC2
  have heven : C s * qA + C t * qB = 0 :=
    (mul_eq_zero.mp hevenTwice).resolve_left hC2
  have hoddPairComp :
      (C sX * pA + C tX * pB).comp (X ^ 2) = 0 := by
    have hx : X * (C sX * qA + C tX * qB) = 0 := by
      calc
        X * (C sX * qA + C tX * qB) =
            C sX * (X * qA) + C tX * (X * qB) := by ring
        _ = 0 := hodd
    have hpairQ : C sX * qA + C tX * qB = 0 :=
      (mul_eq_zero.mp hx).resolve_left X_ne_zero
    simpa only [add_comp, C_mul_comp, qA, qB] using hpairQ
  have hevenPairComp :
      (C s * pA + C t * pB).comp (X ^ 2) = 0 := by
    simpa only [add_comp, C_mul_comp, qA, qB] using heven
  have comp_sq_eq_zero {p : F[X]} (hp : p.comp (X ^ 2) = 0) : p = 0 := by
    rcases comp_eq_zero_iff.mp hp with hp | hconstant
    · exact hp
    · exfalso
      simpa using hconstant.2
  rcases hpair sX tX (comp_sq_eq_zero hoddPairComp) with ⟨hsX, htX⟩
  rcases hpair s t (comp_sq_eq_zero hevenPairComp) with ⟨hs, ht⟩
  exact ⟨hsX, htX, hs, ht⟩

/-- A scalar syzygy among three monic polynomials of the same degree has
coefficient sum zero.  This is why an exhaustive affine-line search loses no
general scalar syzygies for locator polynomials. -/
theorem monic_sameDegree_syzygy_sum
    (pA pB pC : F[X]) (d : ℕ) (r s t : F)
    (hmonicA : pA.Monic) (hmonicB : pB.Monic) (hmonicC : pC.Monic)
    (hdegA : pA.natDegree = d) (hdegB : pB.natDegree = d)
    (hdegC : pC.natDegree = d)
    (hsyzygy : C r * pA + C s * pB + C t * pC = 0) :
    r + s + t = 0 := by
  have hcoeff := congrArg (fun p : F[X] ↦ p.coeff d) hsyzygy
  have hcoeffA : pA.coeff d = 1 := by
    rw [← hdegA]
    exact hmonicA.coeff_natDegree
  have hcoeffB : pB.coeff d = 1 := by
    rw [← hdegB]
    exact hmonicB.coeff_natDegree
  have hcoeffC : pC.coeff d = 1 := by
    rw [← hdegC]
    exact hmonicC.coeff_natDegree
  simpa only [coeff_add, coeff_C_mul, coeff_zero, hcoeffA, hcoeffB,
    hcoeffC, mul_one] using hcoeff

/-- Every scalar syzygy with nonzero `pB` coefficient normalizes to the affine
form used by the locator-orbit probe.  The affine parameter is `-r/s`. -/
theorem monic_sameDegree_syzygy_affine
    (pA pB pC : F[X]) (d : ℕ) (r s t : F)
    (hmonicA : pA.Monic) (hmonicB : pB.Monic) (hmonicC : pC.Monic)
    (hdegA : pA.natDegree = d) (hdegB : pB.natDegree = d)
    (hdegC : pC.natDegree = d)
    (hs : s ≠ 0)
    (hsyzygy : C r * pA + C s * pB + C t * pC = 0) :
    pB = C (-r / s) * pA + C (1 - (-r / s)) * pC := by
  have hsum := monic_sameDegree_syzygy_sum pA pB pC d r s t
    hmonicA hmonicB hmonicC hdegA hdegB hdegC hsyzygy
  have hsLambda : s * (-r / s) = -r := by
    field_simp [hs]
  have hsOneMinus : s * (1 - (-r / s)) = -t := by
    calc
      s * (1 - (-r / s)) = s + r := by field_simp [hs]; ring
      _ = -t := by linear_combination hsum
  apply mul_left_cancel₀ (C_ne_zero.mpr hs)
  simp only [mul_add, ← mul_assoc, ← C_mul]
  rw [hsLambda, hsOneMinus]
  simp only [map_neg, neg_mul]
  linear_combination hsyzygy

/-- **One-root extension rigidity.**  Extending a rigid locator line by the
three linear factors `X-a`, `X-b`, and `X-c` preserves collinearity only when
the affine weights remain `u,v` and all three appended roots coincide. -/
theorem oneRootExtension_rigid
    (pA pB pC : F[X]) (u v alpha beta a b c : F)
    (hrigid : FourDirectionRigid pA pB)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hbase : pC = C u * pA + C v * pB)
    (hext :
      (X - C c) * pC =
        C alpha * ((X - C a) * pA) +
          C beta * ((X - C b) * pB)) :
    alpha = u ∧ beta = v ∧ a = c ∧ b = c := by
  have hrelation :
      C (u - alpha) * (X * pA) + C (v - beta) * (X * pB) +
          C (alpha * a - c * u) * pA + C (beta * b - c * v) * pB = 0 := by
    calc
      C (u - alpha) * (X * pA) + C (v - beta) * (X * pB) +
            C (alpha * a - c * u) * pA + C (beta * b - c * v) * pB =
          (X - C c) * pC -
            (C alpha * ((X - C a) * pA) +
              C beta * ((X - C b) * pB)) := by
                rw [hbase]
                simp only [map_sub, map_mul]
                ring
      _ = 0 := sub_eq_zero.mpr hext
  rcases hrigid (u - alpha) (v - beta)
      (alpha * a - c * u) (beta * b - c * v) hrelation with
    ⟨huAlpha, hvBeta, ha, hb⟩
  have huAlpha' : u = alpha := sub_eq_zero.mp huAlpha
  have hvBeta' : v = beta := sub_eq_zero.mp hvBeta
  have hua : u * a = u * c := by
    calc
      u * a = alpha * a := by rw [huAlpha']
      _ = c * u := sub_eq_zero.mp ha
      _ = u * c := mul_comm c u
  have hvb : v * b = v * c := by
    calc
      v * b = beta * b := by rw [hvBeta']
      _ = c * v := sub_eq_zero.mp hb
      _ = v * c := mul_comm c v
  exact ⟨huAlpha'.symm, hvBeta'.symm,
    mul_left_cancel₀ hu hua, mul_left_cancel₀ hv hvb⟩

/-- A direct disjointness corollary: under the same hypotheses, even the first
and third new roots cannot be distinct. -/
theorem no_distinct_oneRootExtension
    (pA pB pC : F[X]) (u v alpha beta a b c : F)
    (hrigid : FourDirectionRigid pA pB)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hbase : pC = C u * pA + C v * pB)
    (hac : a ≠ c) :
    ¬ (X - C c) * pC =
        C alpha * ((X - C a) * pA) +
          C beta * ((X - C b) * pB) := by
  intro hext
  exact hac (oneRootExtension_rigid pA pB pC u v alpha beta a b c
    hrigid hu hv hbase hext).2.2.1

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOneRootExtensionRigidity

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOneRootExtensionRigidity
#print axioms fourDirectionRigid_comp_sq
#print axioms monic_sameDegree_syzygy_sum
#print axioms monic_sameDegree_syzygy_affine
#print axioms oneRootExtension_rigid
#print axioms no_distinct_oneRootExtension
