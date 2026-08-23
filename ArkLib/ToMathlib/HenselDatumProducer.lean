/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HPzBridge

/-!
# Hensel Datum Construction and Separability Bounds

This module formalizes the construction of the per-point Hensel lifting data required for
the correlated agreement analysis in Section 5 of [BCIKS20]. In particular, we prove that
under the condition of separability, an approximate root of a polynomial yields a unit derivative.

## Mathematical Context

Let $F$ be a field, and $f \in F⟦X⟧[Y]$ be a polynomial in $Y$ with coefficients in the
power series ring. Let $a_0 \in F⟦X⟧$ be an approximate root of $f$, meaning:
$$f(a_0) \equiv 0 \pmod X$$
or equivalently, $f(a_0) \in (X)$.

If $f$ is separable, there exist polynomials $u, v \in F⟦X⟧[Y]$ satisfying the Bézout identity:
$$u \cdot f + v \cdot f' = 1$$
Evaluating this identity at $Y = a_0$ and examining the constant coefficient shows that
$$\text{constantCoeff}(f'(a_0)) \neq 0$$
which implies that $f'(a_0)$ is a unit in $F⟦X⟧$.

We package this algebraic fact to construct the `HenselDatum` structure, which certifies
that the matching polynomial has a unique Hensel lift.

## Key Formalizations
* `eval_sub_mem_span_X_of_congr`: Shows that polynomial evaluation preserves modular congruences.
* `approxRoot_of_isRoot_of_congr`: Certifies that closeness to an exact root implies being
  an approximate root.
* `isUnit_derivative_eval_of_separable`: Proves that separability implies a unit derivative
  at an approximate root.
* `henselDatum_of_sepInput`: Constructs the `HenselDatum` from a separable input configuration.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon
  Codes*, eprint 2020.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

namespace ArkLib

namespace HenselDatumProducer

/-! ### Polynomial Congruence Preservation -/

variable {F : Type} [Field F]

/-- Shows that evaluating a polynomial at congruent points yields congruent values modulo $X$. -/
theorem eval_sub_mem_span_X_of_congr (f : Polynomial (PowerSeries F)) {a b : PowerSeries F}
    (h : a - b ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    f.eval a - f.eval b ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  exact h.trans (Polynomial.sub_dvd_eval_sub a b f)

/-- Certifies that if $a_0$ is congruent to an exact root of $f$ modulo $X$, then $a_0$ is
an approximate root. -/
theorem approxRoot_of_isRoot_of_congr (f : Polynomial (PowerSeries F)) {r a₀ : PowerSeries F}
    (hroot : f.IsRoot r)
    (hcongr : r - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    f.eval a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  -- The evaluation difference lies in the ideal.
  have hsub : f.eval r - f.eval a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} :=
    eval_sub_mem_span_X_of_congr f hcongr
  rw [Polynomial.IsRoot.def] at hroot
  rw [hroot, zero_sub] at hsub
  -- Negating preserves ideal membership.
  simpa using (Ideal.neg_mem_iff _).mp hsub

/-! ### Separability and Unit Derivative -/

/-- Theorem showing that the derivative of a separable polynomial is a unit when evaluated
at an approximate root. -/
theorem isUnit_derivative_eval_of_separable (f : Polynomial (PowerSeries F))
    {a₀ : PowerSeries F} (hsep : f.Separable)
    (h0 : f.eval a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    IsUnit (f.derivative.eval a₀) := by
  obtain ⟨u, v, huv⟩ := hsep
  -- Evaluate the Bézout identity at $a_0$.
  have heval : (u.eval a₀) * (f.eval a₀) + (v.eval a₀) * (f.derivative.eval a₀) = 1 := by
    have := congrArg (Polynomial.eval a₀) huv
    simpa using this
  rw [PowerSeries.isUnit_iff_constantCoeff]
  -- The constant coefficient of the evaluated polynomial vanishes.
  have hcc0 : PowerSeries.constantCoeff (f.eval a₀) = 0 := by
    rw [← PowerSeries.X_dvd_iff, ← Ideal.mem_span_singleton]
    exact h0
  -- Read the constant coefficient of the Bézout evaluation.
  have hcc := congrArg (PowerSeries.constantCoeff (R := F)) heval
  simp only [map_add, map_mul, map_one, hcc0, mul_zero, zero_add] at hcc
  -- Deduce that the derivative evaluation constant coefficient is a unit.
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hcc)

/-- Combines approx root certification and separability to prove the derivative is a unit. -/
theorem isUnit_derivative_of_separable_of_isRoot_of_congr (f : Polynomial (PowerSeries F))
    {r a₀ : PowerSeries F} (hsep : f.Separable) (hroot : f.IsRoot r)
    (hcongr : r - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    IsUnit (f.derivative.eval a₀) :=
  isUnit_derivative_eval_of_separable f hsep (approxRoot_of_isRoot_of_congr f hroot hcongr)

end HenselDatumProducer

/-! ### Hensel Input Configuration -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

namespace HenselDatumProducer

/-- Input configuration for the Hensel lift at a specialized coordinate.
Contains the matching polynomials, root approximations, and separability parameters. -/
structure SepHenselInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) (v₀ v₁ : F[X]) : Type where
  /-- per-`z` matching polynomial over `F⟦X⟧`. -/
  f : F → Polynomial (PowerSeries F)
  /-- per-`z` common approximation. -/
  a₀ : F → PowerSeries F
  /-- `↑(P z)` is a root of the matching polynomial. -/
  hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot ((P z : PowerSeries F))
  /-- `↑(lift.eval (C z))` is a root of the matching polynomial. -/
  hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot
      ((((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z) : F[X]) : PowerSeries F)
  /-- `↑(P z)` reduces to the approximation mod `X`. -/
  hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (P z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- `↑(lift.eval (C z))` reduces to the approximation mod `X`. -/
  hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    ((((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z) : F[X]) : PowerSeries F) - a₀ z
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- per-`z` separability of the matching polynomial (the §5 `hsep` graph condition). -/
  hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).Separable

/-- Producer function constructing a `HenselDatum` from a separable input configuration. -/
def henselDatum_of_sepInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (d : SepHenselInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ where
  f := d.f
  a₀ := d.a₀
  hProot := d.hProot
  hQroot := d.hQroot
  hPapprox := d.hPapprox
  hQapprox := d.hQapprox
  hderiv := fun z hz =>
    isUnit_derivative_of_separable_of_isRoot_of_congr (d.f z) (d.hsep z hz)
      (d.hProot z hz) (d.hPapprox z hz)

end HenselDatumProducer

/-! ### End-to-End Hensel Integration -/

/-- Derives the point-wise polynomial equivalence for all candidate linear combinations using the
Hensel input configuration and degree bounds. -/
theorem hPz_of_sepHenselInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (hInput : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.SepHenselInput
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 :=
  HPzBridge.hPz_of_henselDatum
    (fun v₀ v₁ hlin => HenselDatumProducer.henselDatum_of_sepInput (hInput v₀ v₁ hlin)) hdeg

namespace HenselDatumProducer

/-! ### Roots from Divisibility -/

/-- Input configuration for the matching-divisibility route to the Hensel datum.

This is the same per-`z` data as `SepHenselInput`, except the two root facts are supplied in the
shape produced by the GS matching extractor: `Y - root` divides the per-`z` matching polynomial. -/
structure MatchingDvdInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) (v₀ v₁ : F[X]) :
    Type where
  /-- per-`z` matching polynomial over `F⟦X⟧`. -/
  f : F → Polynomial (PowerSeries F)
  /-- per-`z` common approximation. -/
  a₀ : F → PowerSeries F
  /-- `↑(P z)` is a root of the matching polynomial, expressed as a linear factor. -/
  hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (Polynomial.X - Polynomial.C ((P z : PowerSeries F))) ∣ f z
  /-- `↑(lift.eval (C z))` is a root of the matching polynomial, expressed as a linear factor. -/
  hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (Polynomial.X - Polynomial.C
      ((((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z) : F[X]) : PowerSeries F)) ∣ f z
  /-- `↑(P z)` reduces to the approximation mod `X`. -/
  hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (P z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- `↑(lift.eval (C z))` reduces to the approximation mod `X`. -/
  hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    ((((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z) : F[X]) : PowerSeries F) - a₀ z
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- per-`z` separability of the matching polynomial. -/
  hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).Separable

/-- Construct a `HenselDatum` when root properties are expressed as factor divisibility
statements. -/
def henselDatum_of_matchingDvd_and_sep {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (f : F → Polynomial (PowerSeries F)) (a₀ : F → PowerSeries F)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C ((P z : PowerSeries F))) ∣ f z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        ((((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z) : F[X]) : PowerSeries F)) ∣ f z)
    (hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z) : F[X]) : PowerSeries F) - a₀ z
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).Separable) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  henselDatum_of_sepInput
    { f := f
      a₀ := a₀
      hProot := fun z hz => (Polynomial.dvd_iff_isRoot).mp (hPdvd z hz)
      hQroot := fun z hz => (Polynomial.dvd_iff_isRoot).mp (hQdvd z hz)
      hPapprox := hPapprox
      hQapprox := hQapprox
      hsep := hsep }

/-- Construct a `HenselDatum` from the bundled matching-divisibility input. -/
def henselDatum_of_matchingDvdInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (d : MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  henselDatum_of_matchingDvd_and_sep d.f d.a₀ d.hPdvd d.hQdvd d.hPapprox d.hQapprox d.hsep

end HenselDatumProducer

/-- Derives the full `hPz` field from the matching-divisibility route.

The residual hypothesis is a producer for `MatchingDvdInput` for every linear representative
consistent with `γ`.  The per-`z` identity is still derived by Hensel uniqueness through
`HPzBridge.hPz_of_henselDatum`; the remaining separate input is the usual degree bound for the
representative. -/
theorem hPz_of_matchingDvdInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (hInput : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.MatchingDvdInput
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 :=
  HPzBridge.hPz_of_henselDatum
    (fun v₀ v₁ hlin =>
      HenselDatumProducer.henselDatum_of_matchingDvdInput (hInput v₀ v₁ hlin)) hdeg

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`.

These anchors cover the reduced #91 supplier surface:
`SepHenselInput -> HPzBridge.HenselDatum -> hPz`, plus the
matching-divisibility adapter and its direct `hPz` landing theorem. -/
#print axioms ArkLib.HenselDatumProducer.SepHenselInput
#print axioms ArkLib.HenselDatumProducer.MatchingDvdInput
#print axioms ArkLib.HenselDatumProducer.eval_sub_mem_span_X_of_congr
#print axioms ArkLib.HenselDatumProducer.approxRoot_of_isRoot_of_congr
#print axioms ArkLib.HenselDatumProducer.isUnit_derivative_eval_of_separable
#print axioms ArkLib.HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr
#print axioms ArkLib.HenselDatumProducer.henselDatum_of_sepInput
#print axioms ArkLib.hPz_of_sepHenselInput
#print axioms ArkLib.HenselDatumProducer.henselDatum_of_matchingDvd_and_sep
#print axioms ArkLib.HenselDatumProducer.henselDatum_of_matchingDvdInput
#print axioms ArkLib.hPz_of_matchingDvdInput
