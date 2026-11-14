/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Coprime rigidity for nested locator extensions

Let the coprime base locators `A,B` and a third locator `C` satisfy

`C = u*A + v*B`.

This file proves that every sufficiently low-degree polynomial-coefficient
syzygy

`A*rA + B*rB + C*rC = 0`

is merely the base identity multiplied by `rC`: necessarily

`rA = -u*rC` and `rB = -v*rC`.

Consequently all roots introduced by the three residual multipliers are
common roots.  This rules out every *nested* improvement of the smooth
rate-quarter construction that retains the old coprime locators and appends
lower-degree quotients.  It does not rule out a non-nested higher-degree
locator triangle with entirely different base factors.
-/

set_option autoImplicit false

open Polynomial
open scoped Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoprimeQuotientRigidity

variable {F : Type} [Field F]

/-- A low-degree syzygy between coprime polynomials is trivial.  Euclid's
lemma makes `B ∣ rA` and `A ∣ rB`; the strict degree bounds then force both
remainders to vanish. -/
theorem coprime_lowDegree_syzygy
    (A B rA rB : F[X])
    (hcoprime : IsCoprime A B)
    (hdegA : rA.natDegree < B.natDegree)
    (hdegB : rB.natDegree < A.natDegree)
    (hsyzygy : A * rA + B * rB = 0) :
    rA = 0 ∧ rB = 0 := by
  have hBdvdProduct : B ∣ A * rA := by
    refine ⟨-rB, ?_⟩
    calc
      A * rA = -(B * rB) := by linear_combination hsyzygy
      _ = B * (-rB) := by ring
  have hAdvdProduct : A ∣ B * rB := by
    refine ⟨-rA, ?_⟩
    calc
      B * rB = -(A * rA) := by linear_combination hsyzygy
      _ = A * (-rA) := by ring
  have hBdvdA : B ∣ rA :=
    hcoprime.symm.dvd_of_dvd_mul_left hBdvdProduct
  have hAdvdB : A ∣ rB :=
    hcoprime.dvd_of_dvd_mul_left hAdvdProduct
  exact ⟨eq_zero_of_dvd_of_natDegree_lt hBdvdA hdegA,
    eq_zero_of_dvd_of_natDegree_lt hAdvdB hdegB⟩

/-- **Coprime quotient rigidity.**  Subject only to the displayed strict
degree bounds, every polynomial-coefficient syzygy on the base locator line
is the base identity times the common multiplier `rC`. -/
theorem coprime_base_syzygy_rigid
    (A B D rA rB rC : F[X]) (u v : F)
    (hcoprime : IsCoprime A B)
    (hbase : D = C u * A + C v * B)
    (hdegA : (rA + C u * rC).natDegree < B.natDegree)
    (hdegB : (rB + C v * rC).natDegree < A.natDegree)
    (hsyzygy : A * rA + B * rB + D * rC = 0) :
    rA = -(C u * rC) ∧ rB = -(C v * rC) := by
  have hexpanded :
      A * (rA + C u * rC) + B * (rB + C v * rC) = 0 := by
    calc
      A * (rA + C u * rC) + B * (rB + C v * rC) =
          A * rA + B * rB + D * rC := by rw [hbase]; ring
      _ = 0 := hsyzygy
  rcases coprime_lowDegree_syzygy A B
      (rA + C u * rC) (rB + C v * rC)
      hcoprime hdegA hdegB hexpanded with ⟨hA, hB⟩
  exact ⟨eq_neg_of_add_eq_zero_left hA, eq_neg_of_add_eq_zero_left hB⟩

/-- If the two base coefficients are nonzero, the three residual multipliers
have exactly the same root set.  Thus every genuinely new root supplied by a
nested extension is shared by all three extended locators. -/
theorem coprime_base_syzygy_commonRoots
    (A B D rA rB rC : F[X]) (u v : F)
    (hcoprime : IsCoprime A B)
    (hbase : D = C u * A + C v * B)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hdegA : (rA + C u * rC).natDegree < B.natDegree)
    (hdegB : (rB + C v * rC).natDegree < A.natDegree)
    (hsyzygy : A * rA + B * rB + D * rC = 0)
    (x : F) :
    (rA.IsRoot x ↔ rC.IsRoot x) ∧
      (rB.IsRoot x ↔ rC.IsRoot x) := by
  rcases coprime_base_syzygy_rigid A B D rA rB rC u v
      hcoprime hbase hdegA hdegB hsyzygy with ⟨hA, hB⟩
  constructor
  · rw [hA]
    simp [IsRoot, hu]
  · rw [hB]
    simp [IsRoot, hv]

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoprimeQuotientRigidity

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoprimeQuotientRigidity
#print axioms coprime_lowDegree_syzygy
#print axioms coprime_base_syzygy_rigid
#print axioms coprime_base_syzygy_commonRoots
