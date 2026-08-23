/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorDegreeOverRatFunc
import ArkLib.ToMathlib.DiscriminantSeparableConverse

/-!
# Hab25 §3 Step S5, characteristic zero: the separability residual is a theorem

The S5 capstone `gs_interpolant_good_specialization_of_dvd`
(`GSFactorDegreeOverRatFunc.lean`) left exactly one per-factor residual: `discr R ≠ 0`
(separability of the irreducible factor), which can genuinely fail in characteristic `p`
(the inseparable `R(X, Y^{p^f})` factors the paper descends through). This file **discharges
that residual in characteristic zero**:

* `irreducible_discr_ne_zero_of_charZero` — for `F` of characteristic zero, every irreducible
  `R ∈ K[X][Y]` (`K = F(Z)`) of positive `Y`-degree has nonzero `Y`-discriminant: the fraction
  field `K(X) = FractionRing K[X]` has characteristic zero, hence is perfect, and the
  Gauss + perfect-field + converse-discriminant chain
  (`discr_ne_zero_of_irreducible_of_perfectField_fractionRing`) applies with `A = K[X]`.

* `gs_interpolant_good_specialization_charZero` — the **fully residual-free S5** in
  characteristic zero: for any finite family of positive-`Y`-degree irreducible factors of
  the GS interpolant, in the paper regime `|Rs| · 2·(D/(k−1))·D < n` a common good
  specialization point exists (every factor specializes to a nonzero, degree-preserved,
  separable polynomial of `K[Y]`). *No hypotheses beyond the factor shape and the regime.*

Together with `gs_decoded_eval_injective` (branch separation, already residual-free in any
characteristic), the entire S5 of Hab25 §3 is now **proven** in characteristic zero; in
characteristic `p` it is proven modulo the separable-core descent of the inseparable factors
(deep S4→S6 content).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- **Char-0 separability of irreducible bivariate factors.** For `F` of characteristic zero,
every irreducible `R ∈ (RatFunc F)[X][Y]` of positive `Y`-degree has nonzero `Y`-discriminant:
`K(X)` is a characteristic-zero, hence perfect, field. -/
theorem irreducible_discr_ne_zero_of_charZero [CharZero F]
    {R : (RatFunc F)[X][Y]} (hirr : Irreducible R) (hdeg : 0 < R.natDegree) :
    R.discr ≠ 0 := by
  haveI : CharZero (RatFunc F) :=
    charZero_of_injective_algebraMap (algebraMap F (RatFunc F)).injective
  haveI : CharZero ((RatFunc F)[X]) :=
    charZero_of_injective_algebraMap (C_injective : Function.Injective (C (R := RatFunc F)))
  haveI : CharZero (FractionRing ((RatFunc F)[X])) :=
    charZero_of_injective_algebraMap
      (IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])))
  exact discr_ne_zero_of_irreducible_of_perfectField_fractionRing hirr hdeg

/-- **Hab25 §3, Step S5 in characteristic zero — fully residual-free.**

There is a generic-fold GS interpolant `Q` over `K = F(Z)` (S2 `Conditions`) with the
[BCIKS20, Claim 5.4] degree data `degreeX Q ≤ D := gs_degree_bound k n m` and
`deg_Y Q ≤ D/(k−1)` (S3), factoring into irreducibles (S4a), such that for **any** finite
family `Rs` of positive-`Y`-degree members of `factors Q`, in the paper regime
`|Rs| · 2·(D/(k−1))·D < n` some lifted evaluation point `x₀` is simultaneously good for all
of `Rs`: every factor specializes along `X ↦ x₀` to a nonzero, degree-preserved, **separable**
polynomial in `K[Y]`.

Compared with `gs_interpolant_good_specialization_of_dvd`, the per-factor separability
hypothesis `discr R ≠ 0` is **gone** — it is supplied by
`irreducible_discr_ne_zero_of_charZero`. This is the complete Step S5 in characteristic
zero. -/
theorem gs_interpolant_good_specialization_charZero [CharZero F]
    {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      degreeX Q ≤ gs_degree_bound k n m ∧
      Q.natDegree ≤ gs_degree_bound k n m / (k - 1) ∧
      (∀ q ∈ UniqueFactorizationMonoid.factors Q, Irreducible q) ∧
      Associated (UniqueFactorizationMonoid.factors Q).prod Q ∧
      ∀ Rs : Finset (RatFunc F)[X][Y],
        (∀ R ∈ Rs, R ∈ UniqueFactorizationMonoid.factors Q) →
        (∀ R ∈ Rs, 0 < R.natDegree) →
        Rs.card * (2 * (gs_degree_bound k n m / (k - 1)) * gs_degree_bound k n m) < n →
        ∃ i₀ : Fin n, ∀ R ∈ Rs,
          (R.discr).eval (liftedDomain ωs i₀) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).natDegree = R.natDegree ∧
          R.map (evalRingHom (liftedDomain ωs i₀)) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).Separable := by
  obtain ⟨Q, hQ, hxdeg, hydeg, hirr, hprod, hmain⟩ :=
    gs_interpolant_good_specialization_of_dvd k m ωs f₀ f₁ hk1 hn0 hm hk
  refine ⟨Q, hQ, hxdeg, hydeg, hirr, hprod, ?_⟩
  intro Rs hmem hpos hcard
  refine hmain Rs (fun R hR => ?_) hpos (fun R hR => ?_) hcard
  · exact UniqueFactorizationMonoid.dvd_of_mem_factors (hmem R hR)
  · exact irreducible_discr_ne_zero_of_charZero
      (UniqueFactorizationMonoid.irreducible_of_factor R (hmem R hR)) (hpos R hR)

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.irreducible_discr_ne_zero_of_charZero
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_good_specialization_charZero
