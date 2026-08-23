/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsCore

/-!
# Finding F13 — the slice-separability satisfiability boundary (BCIKS20 §5, #304)

`ClaimA2.Hypotheses.separable_evalX` demands `(evalX (C x₀) R).Separable` **over the coefficient
ring `F[Z]`**, i.e. a Bézout identity `a·g + b·g' = 1` *in `F[Z][T]`*.  This file pins down
exactly how strong that is, with an exact characterization at pair-of-section products:

* `separable_mul_X_sub_C_iff` — for any commutative ring `A` and `a b : A`,
  `((X − C a)·(X − C b)).Separable ↔ IsUnit (a − b)`.

* `isUnit_sub_of_separable_of_dvd` — if a separable `Q` admits two section divisors
  `(X − C a)·(X − C b) ∣ Q`, then `IsUnit (a − b)`.

* `hypotheses_isUnit_branch_separation` — **the F13 boundary**: under `ClaimA2.Hypotheses`,
  any two rational sections `T = a(Z)`, `T = b(Z)` of the specialized GS surface must have
  *constant* difference `a − b ∈ Fˣ`.

* `not_separable_section_pair` — the refutation witness: `(T − 0)·(T − Z)` is **not** separable
  over `F[Z]` (the branch separation `Z` is not a unit), over every field `F`.

## Why this matters (the satisfiability boundary)

For a *real* Guruswami–Sudan surface in the §5 list-decoding regime, the specialized slice
`evalX (C x₀) R ∈ F[Z][T]` carries one branch `T = vᵢ(Z)` per decoded candidate; two distinct
decoded branches have `vᵢ − vⱼ` non-constant in general (their difference is the `x₀`-evaluation
of two distinct decoded codeword families).  By `hypotheses_isUnit_branch_separation`,
**`ClaimA2.Hypotheses` is unsatisfiable at every such slice** — the satisfiable sector of the
strong interface is exactly the constant-separated-branch surfaces (e.g. the
`FaithfulFrontierWitness` data `R = T² − T`).

Consequently the "ξ is a unit, integrality is free" phenomenon recorded in
`P1BetaOneRefutation.lean` is a property of the *degenerate sector only*: on it the `Λ`-weight
theory trivializes (the `ξ`-content is an `F`-constant, the `(A.4)` denominators carry no
`Z`-degree).  Honest instantiation at real GS data must replace the global Bézout field by
per-place simple-root facts (`ξ̄(z) ≠ 0` off a counted exceptional set), which is the elementary
section-Newton route.

This complements (does not contradict) `Claim57FieldDischarge.lean`'s `hsep` verdict
("strictly stronger than nonvanishing… kept as the §5 good-point separability residual"): here we
show the residual is not merely *unproven* but **false** at every multi-branch slice with
non-constant separation, so no producer can ever discharge it in the real regime.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, Appendix A.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate

namespace BCIKS20AppendixA

namespace SliceSeparabilityBoundary

section CommRing

variable {A : Type*} [CommRing A]

/-- A product of two monic linear sections is separable **only if** the section separation is a
unit: evaluating the Bézout identity `u·f + w·f' = 1` at `X := a` kills the `f`-term and leaves
`w(a) · (a − b) = 1`. -/
theorem isUnit_sub_of_separable_mul_X_sub_C {a b : A}
    (h : ((X - C a) * (X - C b) : A[X]).Separable) : IsUnit (a - b) := by
  obtain ⟨u, w, huw⟩ := h
  have hd : Polynomial.derivative ((X - C a) * (X - C b) : A[X])
      = (X - C b) + (X - C a) := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C,
      Polynomial.derivative_X_sub_C, one_mul, mul_one]
  have hev := congrArg (Polynomial.eval a) huw
  simp only [hd, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, sub_self, mul_zero,
    zero_mul, zero_add, add_zero] at hev
  exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hev)

/-- **The exact boundary**: a pair-of-sections product is separable **iff** the separation is a
unit.  (Forward: Bézout evaluation; backward: each linear factor is separable and the unit
separation supplies the coprimality certificate.) -/
theorem separable_mul_X_sub_C_iff {a b : A} :
    ((X - C a) * (X - C b) : A[X]).Separable ↔ IsUnit (a - b) := by
  constructor
  · exact isUnit_sub_of_separable_mul_X_sub_C
  · intro hu
    refine Polynomial.Separable.mul (Polynomial.separable_X_sub_C)
      (Polynomial.separable_X_sub_C) ?_
    refine ⟨-C ((hu.unit⁻¹ : Aˣ) : A), C ((hu.unit⁻¹ : Aˣ) : A), ?_⟩
    have : (C ((hu.unit⁻¹ : Aˣ) : A) : A[X]) * C (a - b) = 1 := by
      rw [← Polynomial.C_mul, ← Polynomial.C_1]
      congr 1
      exact hu.val_inv_mul
    calc -C ((hu.unit⁻¹ : Aˣ) : A) * (X - C a) + C ((hu.unit⁻¹ : Aˣ) : A) * (X - C b)
        = C ((hu.unit⁻¹ : Aˣ) : A) * ((X - C b) - (X - C a)) := by ring
      _ = C ((hu.unit⁻¹ : Aˣ) : A) * C (a - b) := by
          congr 1
          rw [sub_sub_sub_cancel_left, ← Polynomial.C_sub]
      _ = 1 := this

/-- Two section divisors of a separable polynomial must be constant-separated. -/
theorem isUnit_sub_of_separable_of_dvd {a b : A} {Q : A[X]}
    (hsep : Q.Separable) (hdvd : (X - C a) * (X - C b) ∣ Q) : IsUnit (a - b) :=
  isUnit_sub_of_separable_mul_X_sub_C (hsep.of_dvd hdvd)

end CommRing

section Witness

variable (F : Type) [Field F]

/-- **The refutation witness**: the two-branch slice `(T − 0)·(T − Z)` — branch values `0` and
`Z`, separation `Z` non-constant — is *not* separable over `F[Z]`, over every field `F`. -/
theorem not_separable_section_pair :
    ¬ ((X - C (0 : F[X])) * (X - C (Polynomial.X : F[X])) : F[X][Y]).Separable := by
  intro h
  have hu := isUnit_sub_of_separable_mul_X_sub_C h
  rw [zero_sub, IsUnit.neg_iff] at hu
  exact Polynomial.not_isUnit_X hu

end Witness

section F13

variable {F : Type} [Field F]

/-- **Finding F13 — the satisfiability boundary of `ClaimA2.Hypotheses`**: under the strong
slice-separability field, any two rational sections of the specialized GS surface are
constant-separated.  Contrapositive: at every real multi-branch slice (two decoded branches whose
`x₀`-values differ non-constantly), `ClaimA2.Hypotheses` is **unsatisfiable**, for every choice
of the modulus `H`. -/
theorem hypotheses_isUnit_branch_separation {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {a b : F[X]}
    (hdvd : (X - C a) * (X - C b) ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R) :
    IsUnit (a - b) :=
  isUnit_sub_of_separable_of_dvd hHyp.separable_evalX hdvd

end F13

end SliceSeparabilityBoundary

end BCIKS20AppendixA

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms BCIKS20AppendixA.SliceSeparabilityBoundary.isUnit_sub_of_separable_mul_X_sub_C
#print axioms BCIKS20AppendixA.SliceSeparabilityBoundary.separable_mul_X_sub_C_iff
#print axioms BCIKS20AppendixA.SliceSeparabilityBoundary.isUnit_sub_of_separable_of_dvd
#print axioms BCIKS20AppendixA.SliceSeparabilityBoundary.not_separable_section_pair
#print axioms BCIKS20AppendixA.SliceSeparabilityBoundary.hypotheses_isUnit_branch_separation
