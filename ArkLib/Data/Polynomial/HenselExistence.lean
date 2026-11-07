/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.NewtonLinearization

/-!
# Scalar-coefficient power-series roots: constant existence and simple-root uniqueness

This file treats the **scalar-coefficient specialization**: a polynomial `P : R[X]` (coefficients
in `R`, not in `R⟦X⟧`) and an **exact** root `c : R` (`eval c P = 0`).

* `exists_powerSeries_root` (EXISTENCE): there is `γ : R⟦X⟧` with `constantCoeff γ = c` and
  `aeval γ P = 0`.  The witness is simply the constant series `C c`, since
  `aeval (C c) P = C (eval c P) = 0` (`aeval_C_eq_C_eval`).  No derivative/simple-root premise is
  needed for this.
* `aeval_root_unique` (UNIQUENESS): if `eval c P'` is a unit, any two power-series roots of `P`
  with constant coefficient `c` coincide.  Together the two say that, under the simple-root
  hypothesis, `C c` is the **unique** power-series root of `P` above `c`.

**Scope (audit L75).**  This is *not* general Hensel lifting.  Genuine Hensel lifting starts from a
polynomial with power-series coefficients whose order-0 reduction has a simple root (e.g.
`Y² − (1 + X)` over `ℚ⟦X⟧` with `c = 1`), and its lifted root is in general nonconstant; that input
shape is outside this file.  The general existence/uniqueness theorems are
`HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff` / `root_unique_seriesCoeff`
(`ArkLib/Data/Polynomial/HenselSeriesCoeff.lean`), with the related Newton developments in
`ArkLib/ToMathlib/PowerSeriesNewton.lean` and `ArkLib/ToMathlib/SectionNewtonGamma.lean`.

An earlier version of this file built an explicit Newton sequence starting at `C c` and
re-derived local copies of the `NewtonLinearization` coefficient lemmas.  For scalar `P` that
sequence is constant (every correction coefficient is a positive-order coefficient of the constant
series `aeval (C c) P`, hence `0`), so the construction only re-proved that `C c` is a root; it was
removed in favour of the direct constant embedding, and the uniqueness proof now uses
`NewtonLinearization.coeff_aeval_sub_at` directly.
-/

namespace ProximityPrize.HenselExistence

open PowerSeries

variable {R : Type*} [CommRing R]

/-- Evaluating a scalar polynomial at a constant power series gives the constant series of the
evaluation: `aeval (C c) P = C (eval c P)`. -/
theorem aeval_C_eq_C_eval (P : Polynomial R) (c : R) :
    Polynomial.aeval (PowerSeries.C c) P = PowerSeries.C (Polynomial.eval c P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [map_pow]

/-- `constantCoeff (aeval γ P) = eval (constantCoeff γ) P`. -/
theorem constantCoeff_aeval_powerSeries (P : Polynomial R) (γ : R⟦X⟧) :
    constantCoeff (Polynomial.aeval γ P) = Polynomial.eval (constantCoeff γ) P := by
  rw [Polynomial.aeval_eq_sum_range, map_sum, Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by
    rw [PowerSeries.constantCoeff_smul, map_pow, smul_eq_mul]

/-- For scalar `P`, a constant series `C c` is a root of `P` over `R⟦X⟧` iff `c` is a root of
`P` over `R`. -/
theorem aeval_C_eq_zero_iff (P : Polynomial R) (c : R) :
    Polynomial.aeval (PowerSeries.C c) P = 0 ↔ Polynomial.eval c P = 0 := by
  rw [aeval_C_eq_C_eval]
  constructor
  · intro h
    simpa using congrArg PowerSeries.constantCoeff h
  · intro h
    rw [h, map_zero]

/-! ## Uniqueness from coefficient linearization -/

/-- **Power-series root uniqueness for `aeval`.** If two power-series roots of `P`
have the same constant coefficient `c`, and `P'` is a unit at `c`, then the two roots
are equal.

This is the uniqueness half matching `exists_powerSeries_root`, proved directly by
coefficient induction from `coeff_aeval_sub_at`: once the roots agree below order `t`,
the order-`t` coefficient difference is killed by multiplication with the unit
`eval c P'`. -/
theorem aeval_root_unique
    {P : Polynomial R} {γ₁ γ₂ : R⟦X⟧} {c : R}
    (hc₁ : constantCoeff γ₁ = c) (hc₂ : constantCoeff γ₂ = c)
    (hroot₁ : Polynomial.aeval γ₁ P = 0)
    (hroot₂ : Polynomial.aeval γ₂ P = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative P))) :
    γ₁ = γ₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | t
      · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hc₁, hc₂]
      · have hagree : ∀ j < t + 1, coeff j γ₁ = coeff j γ₂ := fun j hj =>
          ih j hj
        have hlin := NewtonLinearization.coeff_aeval_sub_at P (γ₁ := γ₁) (γ₂ := γ₂)
          (t := t + 1) (Nat.succ_pos t) hagree
        rw [hc₁] at hlin
        have hmul :
            Polynomial.eval c (Polynomial.derivative P) *
              (coeff (t + 1) γ₁ - coeff (t + 1) γ₂) = 0 := by
          simpa [hroot₁, hroot₂] using hlin.symm
        rw [mul_comm] at hmul
        exact sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hu).1 hmul)

/-! ## Existence (scalar specialization: the constant embedding) -/

/-- **Power-series root existence, scalar-coefficient case.** For `P : R[X]` and an exact root
`c : R` (`eval c P = 0`), the constant series `C c` is a power-series root of `P` lifting `c`.

No simple-root hypothesis is needed for existence; it is needed only for uniqueness
(`aeval_root_unique`).  This is not general Hensel lifting; see the module docstring and
`HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff` for the series-coefficient statement. -/
theorem exists_powerSeries_root {P : Polynomial R} {c : R} (hc0 : Polynomial.eval c P = 0) :
    ∃ γ : R⟦X⟧, constantCoeff γ = c ∧ Polynomial.aeval γ P = 0 :=
  ⟨PowerSeries.C c, by simp, (aeval_C_eq_zero_iff P c).2 hc0⟩

/-- Under the simple-root hypothesis, every power-series root of a scalar polynomial `P` above a
root `c` is the constant series `C c`. -/
theorem eq_C_of_aeval_eq_zero {P : Polynomial R} {γ : R⟦X⟧} {c : R}
    (hc : constantCoeff γ = c) (hroot : Polynomial.aeval γ P = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative P))) :
    γ = PowerSeries.C c := by
  have hc0 : Polynomial.eval c P = 0 := by
    rw [← hc, ← constantCoeff_aeval_powerSeries, hroot, map_zero]
  exact aeval_root_unique hc (by simp) hroot ((aeval_C_eq_zero_iff P c).2 hc0) hu

end ProximityPrize.HenselExistence

-- Axiom audit: every declaration rests only on `[propext, Classical.choice, Quot.sound]`.
#print axioms ProximityPrize.HenselExistence.aeval_C_eq_C_eval
#print axioms ProximityPrize.HenselExistence.constantCoeff_aeval_powerSeries
#print axioms ProximityPrize.HenselExistence.exists_powerSeries_root
#print axioms ProximityPrize.HenselExistence.aeval_root_unique
#print axioms ProximityPrize.HenselExistence.eq_C_of_aeval_eq_zero
