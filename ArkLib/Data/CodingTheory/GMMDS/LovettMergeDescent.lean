/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeSubstitution
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Lovett's GM-MDS proof: the infinite-descent closing step for Lemma 2.6 (#389)

`LovettMergeSubstitution` supplies the substitution transport: a vanishing relation
`∑ₗ pVanish(Vₗ)·Aₗ = 0` is carried by `Xₙ₋₁ ↦ Xⱼ*` to the merged dimension-`(n−1)` system, and
when the merged system is independent (by the `n`-IH), `substPoly(Aₗ) = 0`, whence
`C(Xₙ₋₁ − Xⱼ*) ∣ Aₗ` (`C_subX_dvd_of_substPoly_eq_zero`).  Cancelling the common factor
(`cancel_common_factor`) yields *the same relation* on the quotients `Bₗ = Aₗ / C(Xₙ₋₁ − Xⱼ*)`, so the
argument re-runs and forces `C(Xₙ₋₁ − Xⱼ*)^m ∣ Aₗ` for **every** `m`.

This file closes that loop: in the UFD `R[X]` (`R = MvPolynomial (Fin n) F`), an element divisible by
every power of the non-unit `C(Xₙ₋₁ − Xⱼ*)` must be zero (finite multiplicity).  So `Aₗ = 0` — the
final contradiction of Lovett's Lemma 2.6, **without** appealing to the `d`-induction hypothesis (the
descent terminates on multiplicity grounds alone).

* `eq_zero_of_forall_pow_dvd` — the general UFD termination fact.
* `subC_subX_not_isUnit` — `C(Xₚ − X_q)` is a non-unit for `p ≠ q`.
* `eq_zero_of_forall_subC_pow_dvd` — the specialization: divisibility by all powers of
  `C(Xₚ − X_q)` forces `0`, the closing step `LovettMergeIndep` consumes.

Honest scope: this is the final brick of the GENERIC GM-MDS Lemma 2.6 (route R3); it does not pin
`δ*` for the explicit prize domain `μ_n` (which leaves the generic regime at order 3,
`HigherOrderMDSOrderThreeFail`).  The remaining open piece of `LovettMergeIndep` is the
`Fin n → Fin (n−1)` reindexing and the `n`-IH invocation that supply the "`∀ m`" divisibility input
to the descent below.  Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

/-- **Infinite-descent termination.**  In a UFD, an element divisible by every power of a fixed
non-unit is zero — its `c`-multiplicity would otherwise be infinite. -/
theorem eq_zero_of_forall_pow_dvd {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {c w : R} (hc : ¬ IsUnit c) (h : ∀ m : ℕ, c ^ m ∣ w) :
    w = 0 := by
  by_contra hw
  obtain ⟨N, hN⟩ := FiniteMultiplicity.of_not_isUnit hc hw
  exact hN (h (N + 1))

variable {F : Type*} [Field F] {n : ℕ}

/-- `Xₚ − X_q` is a non-unit in `MvPolynomial (Fin n) F` when `p ≠ q`: evaluating all variables at
`0` sends it to `0`, which is not a unit. -/
theorem subX_not_isUnit {p q : Fin n} :
    ¬ IsUnit (MvPolynomial.X p - MvPolynomial.X q : MvPolynomial (Fin n) F) := by
  intro hu
  have hu' : IsUnit ((MvPolynomial.aeval (fun _ : Fin n => (0 : F)))
      (MvPolynomial.X p - MvPolynomial.X q)) := hu.map _
  simp only [map_sub, MvPolynomial.aeval_X, sub_self] at hu'
  exact not_isUnit_zero hu'

/-- `C (Xₚ − X_q)` is a non-unit in `(MvPolynomial (Fin n) F)[X]` when `p ≠ q`. -/
theorem subC_subX_not_isUnit {p q : Fin n} :
    ¬ IsUnit (Polynomial.C (MvPolynomial.X p - MvPolynomial.X q :
      MvPolynomial (Fin n) F)) :=
  fun hu => subX_not_isUnit (Polynomial.isUnit_C.mp hu)

/-- **The closing-step specialization.**  If `A : (MvPolynomial (Fin n) F)[X]` is divisible by every
power of `C (Xₚ − X_q)` (`p ≠ q`) — the situation the merge-substitution descent produces — then
`A = 0`.  This is the final contradiction of Lovett's Lemma 2.6, on multiplicity grounds. -/
theorem eq_zero_of_forall_subC_pow_dvd {p q : Fin n}
    {A : (MvPolynomial (Fin n) F)[X]}
    (h : ∀ m : ℕ, (Polynomial.C (MvPolynomial.X p - MvPolynomial.X q :
      MvPolynomial (Fin n) F)) ^ m ∣ A) :
    A = 0 :=
  eq_zero_of_forall_pow_dvd subC_subX_not_isUnit h

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.eq_zero_of_forall_pow_dvd
#print axioms ArkLib.GMMDS.subC_subX_not_isUnit
#print axioms ArkLib.GMMDS.eq_zero_of_forall_subC_pow_dvd
