/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSDiscriminantOverRatFunc

/-!
# Hab25 §3 — factor degree data for the GS interpolant (S3 for factors), discharging the
# S5 degree residuals

The S5 capstone `exists_good_specialization_point`
(`ArkLib/Data/CodingTheory/GuruswamiSudan/GSDiscriminantOverRatFunc.lean`) consumed, per factor,
two degree hypotheses (`Y`-degree `≤ L`, coefficient `X`-degrees `≤ B`). This file **discharges
them** from the GS interpolant's own degree data, using that degrees in *both* variables are
monotone under divisibility over a domain:

* `Polynomial.Bivariate.degreeX_le_natWeightedDegree` — the `(1, v)`-weighted degree dominates
  the `X`-degree (weight `1` on `X`), so the GS `Conditions` bound `Q_deg` yields
  `degreeX Q ≤ gs_degree_bound k n m` (`conditions_degreeX_le`, the `X`-half of
  [BCIKS20, Claim 5.4] over `K = F(Z)`; the `Y`-half is `genericInterpolant_yDegree_le`);
* `Polynomial.Bivariate.degreeX_le_of_dvd` — `X`-degrees of divisors are dominated
  (`degreeX_mul` additivity over the domain `K[X][Y]`), hence every `Y`-coefficient of every
  factor of `Q` has `X`-degree `≤ degreeX Q` (`coeff_natDegree_le_degreeX_of_dvd`);
* the `Y`-side is `Polynomial.natDegree_le_of_dvd`.

The capstone `gs_interpolant_good_specialization_of_dvd` then needs, per factor, **only**:
positive `Y`-degree, the separability residual `discr R ≠ 0` (genuinely deep in
characteristic `p`), and the global count `|Rs| · 2·(D/(k−1))·D < n` — the Lean form of the
paper's S5 numerology `deg_X disc_Y < ℓ²·ρn < n ≤ |F|`. All degree residuals of S5 are gone.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

/-! ## Bivariate degree bricks: divisors inherit `X`-degree bounds -/

namespace Polynomial.Bivariate

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- The `(1, v)`-weighted degree dominates the `X`-degree: weight `1` sits on the `X`-variable,
so dropping the `v·(Y-exponent)` summand can only decrease each term of the support-sup. -/
lemma degreeX_le_natWeightedDegree (f : F[X][Y]) (v : ℕ) :
    degreeX f ≤ natWeightedDegree f 1 v := by
  refine Finset.sup_mono_fun fun m _ => ?_
  simp only [one_mul]
  exact Nat.le_add_right _ _

end Semiring

section CommRing

variable [CommRing F] [IsDomain F]

/-- **Divisors inherit the `X`-degree bound.** Over a domain, `degreeX` is additive on
products (`degreeX_mul`), so a divisor of a nonzero bivariate polynomial has no larger
`X`-degree. -/
lemma degreeX_le_of_dvd {f q : F[X][Y]} (hq : q ∣ f) (hf : f ≠ 0) :
    degreeX q ≤ degreeX f := by
  obtain ⟨s, rfl⟩ := hq
  have hq0 : q ≠ 0 := fun h => hf (by simp [h])
  have hs0 : s ≠ 0 := fun h => hf (by simp [h])
  rw [degreeX_mul q s hq0 hs0]
  exact Nat.le_add_right _ _

/-- Every `Y`-coefficient of a divisor of the nonzero `f` has `X`-degree `≤ degreeX f` —
the per-factor coefficient bound the S5 discriminant estimate consumes. -/
lemma coeff_natDegree_le_degreeX_of_dvd {f q : F[X][Y]} (hq : q ∣ f) (hf : f ≠ 0) (j : ℕ) :
    (q.coeff j).natDegree ≤ degreeX f :=
  (coeff_natDegree_le_degreeX q j).trans (degreeX_le_of_dvd hq hf)

end CommRing

end Polynomial.Bivariate

/-! ## The GS interpolant's `X`-degree bound and the degree-residual-free S5 capstone -/

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- **The `X`-half of [BCIKS20, Claim 5.4] over `K`:** the `(1, k−1)`-weighted degree bound
recorded in the GS `Conditions` caps the `X`-degree of the interpolant, `degreeX Q ≤ D`.
(The `Y`-half is `genericInterpolant_yDegree_le`.) -/
theorem conditions_degreeX_le {K : Type} [Field K] {n k m D : ℕ}
    {ωs : Fin n ↪ K} {f : Fin n → K} {Q : K[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m D ωs f Q) :
    degreeX Q ≤ D := by
  have h := hQ.Q_deg
  rw [weightedDegree_eq_natWeightedDegree] at h
  exact le_trans (degreeX_le_natWeightedDegree Q (k - 1)) (by exact_mod_cast h)

/-- **Hab25 §3, S4 + S5 with all degree residuals discharged.**

There is a generic-fold GS interpolant `Q` over `K = F(Z)` (S2 `Conditions`) with
`degreeX Q ≤ D := gs_degree_bound k n m` and `deg_Y Q ≤ D/(k−1)` (S3, both halves of
[BCIKS20, Claim 5.4] over `K`), factoring into irreducibles (S4a), such that for **any**
finite family `Rs` of divisors of `Q` with positive `Y`-degree:

assuming only the **separability residual** `discr R ≠ 0` per factor (deep in characteristic
`p`) and the S5 count `|Rs| · 2·(D/(k−1))·D < n` — the paper's `deg_X disc_Y < ℓ²ρn` regime —
some lifted evaluation point `x₀` is simultaneously good for all of `Rs`: each factor
specializes along `X ↦ x₀` to a nonzero, degree-preserved, **separable** polynomial in `K[Y]`.

Degree data for the factors is no longer assumed: divisors inherit `deg_Y ≤ deg_Y Q`
(`natDegree_le_of_dvd`) and coefficient `X`-degrees `≤ degreeX Q`
(`coeff_natDegree_le_degreeX_of_dvd`). This is the complete tractable S5: only separability
(the char-`p` `R(X, Y^{p^f})` descent, part of deep S4→S6) remains per factor. -/
theorem gs_interpolant_good_specialization_of_dvd {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      degreeX Q ≤ gs_degree_bound k n m ∧
      Q.natDegree ≤ gs_degree_bound k n m / (k - 1) ∧
      (∀ q ∈ UniqueFactorizationMonoid.factors Q, Irreducible q) ∧
      Associated (UniqueFactorizationMonoid.factors Q).prod Q ∧
      ∀ Rs : Finset (RatFunc F)[X][Y],
        (∀ R ∈ Rs, R ∣ Q) →
        (∀ R ∈ Rs, 0 < R.natDegree) →
        (∀ R ∈ Rs, R.discr ≠ 0) →
        Rs.card * (2 * (gs_degree_bound k n m / (k - 1)) * gs_degree_bound k n m) < n →
        ∃ i₀ : Fin n, ∀ R ∈ Rs,
          (R.discr).eval (liftedDomain ωs i₀) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).natDegree = R.natDegree ∧
          R.map (evalRingHom (liftedDomain ωs i₀)) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).Separable := by
  obtain ⟨Q, hQ, hydeg⟩ := genericInterpolant_yDegree_le k m ωs f₀ f₁ hk1 hn0 hm hk
  have hxdeg : degreeX Q ≤ gs_degree_bound k n m := conditions_degreeX_le hQ
  refine ⟨Q, hQ, hxdeg, hydeg,
    fun q hq => UniqueFactorizationMonoid.irreducible_of_factor q hq,
    UniqueFactorizationMonoid.factors_prod hQ.Q_ne_0, ?_⟩
  intro Rs hdvd hpos hsep hcard
  refine exists_good_specialization_point ωs Rs (fun R => R) hpos ?_ ?_ hsep hcard
  · intro R hR
    exact le_trans (Polynomial.natDegree_le_of_dvd (hdvd R hR) hQ.Q_ne_0) hydeg
  · intro R hR j
    exact le_trans (coeff_natDegree_le_degreeX_of_dvd (hdvd R hR) hQ.Q_ne_0 j) hxdeg

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Polynomial.Bivariate.degreeX_le_natWeightedDegree
#print axioms Polynomial.Bivariate.degreeX_le_of_dvd
#print axioms Polynomial.Bivariate.coeff_natDegree_le_degreeX_of_dvd
#print axioms GuruswamiSudan.OverRatFunc.conditions_degreeX_le
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_good_specialization_of_dvd
