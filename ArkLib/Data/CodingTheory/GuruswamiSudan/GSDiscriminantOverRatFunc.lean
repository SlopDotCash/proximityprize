/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorizationOverRatFunc
import ArkLib.ToMathlib.ResultantDegreeBound
import ArkLib.ToMathlib.DiscriminantSeparable

/-!
# Hab25 §3 Step S5 — discriminant non-vanishing for the GS interpolant over `K = F(Z)`

This file discharges the tractable core of **Step S5** of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`):

> *S5 (Discriminant non-vanishing).* `deg_X disc_Y(Q) < ℓ²·ρn`, so for `|F| > ℓ²ρn` there is
> `x₀ ∈ D` with `disc_Y R_{i,j}(x₀,·) ≠ 0` for all `i,j`. Starting point of the Hensel lift.

Concretely, on top of the discharged S2–S4
(`gs_existence_over_ratfunc` / `genericInterpolant_yDegree_le` / `gs_factorization_index_structure`):

* **Degree half** (in `ArkLib/ToMathlib/ResultantDegreeBound.lean`): for a factor `R` of the GS
  interpolant with `Y`-degree `≤ L` and all `Y`-coefficients of `X`-degree `≤ B`,
  `deg_X disc_Y(R) ≤ (2L−1)·B` (`Polynomial.natDegree_discr_le`).

* **Avoidance half** (`exists_common_eval_ne_zero`, here): a family of `≤ N` nonzero avoidance
  polynomials of degree `≤ D` over the field `K` cannot vanish jointly on `n > N·D` distinct
  points — the product is a nonzero polynomial with too few roots. So a **common good point
  `x₀ ∈ D`** exists among the (lifted) evaluation points.

* **Specialization payoff** (`exists_good_specialization_point`, the S5 capstone): taking the
  avoidance polynomial of each factor to be `disc_Y(R) · leadingCoeff_Y(R)`, at the good point
  `x₀` *every* factor specializes along `X ↦ x₀` to a polynomial in `K[Y]` that is **nonzero, of
  unchanged `Y`-degree, and separable** — exactly the launch pad for the Hensel lift (S6). The
  degree preservation comes from the surviving leading coefficient
  (`Polynomial.natDegree_map_of_leadingCoeff_ne_zero`), and separability from the in-tree
  specialization bridge (`Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero`).

* **GS packaging** (`gs_interpolant_good_specialization`): the above, attached to the S4
  factorization of the generic-fold GS interpolant over `K = F(Z)`.

**Honest residuals.** Two hypotheses remain per factor, both genuinely deep:
1. `discr R ≠ 0` — separability of the irreducible factor. Over `K(X)` in characteristic `p`
   this can *fail* (inseparable factors `R(X, Y^{p^f})`); the paper handles it by descending to
   the separable core (part of the deep S4→S6 content), so it is taken as a named hypothesis.
2. the factor degree bounds (`Y`-degree `≤ L`, coefficient `X`-degrees `≤ B`) — the
   [BCIKS20, Claim 5.4]-over-`K` degree data (S3 for factors).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

/-! ## The avoidance argument: a common non-vanishing evaluation point -/

/-- **Common non-vanishing point.** Over a field `K`, given a finite family of nonzero
"avoidance" polynomials `d R ∈ K[X]` (`R ∈ Rs`), each of degree `≤ D`, and `n > |Rs|·D`
distinct evaluation points, some point `ωs i₀` has `d R (ωs i₀) ≠ 0` **simultaneously for
all `R ∈ Rs`**: the product `∏ d R` is a nonzero polynomial of degree `≤ |Rs|·D < n`, so it
cannot vanish at all `n` points. This is the S5 avoidance step (paper: "for `|F| > ℓ²ρn`
there is `x₀`"). -/
theorem exists_common_eval_ne_zero {K : Type*} [Field K] {n : ℕ} (ωs : Fin n ↪ K)
    {I : Type*} (Rs : Finset I) (d : I → K[X]) {D : ℕ}
    (hd0 : ∀ R ∈ Rs, d R ≠ 0) (hdeg : ∀ R ∈ Rs, (d R).natDegree ≤ D)
    (hn : Rs.card * D < n) :
    ∃ i₀ : Fin n, ∀ R ∈ Rs, (d R).eval (ωs i₀) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hP0 : (∏ R ∈ Rs, d R) ≠ 0 := Finset.prod_ne_zero_iff.mpr hd0
  have hPeval : ∀ i : Fin n, (∏ R ∈ Rs, d R).eval (ωs i) = 0 := by
    intro i
    obtain ⟨R, hR, hzero⟩ := hcon i
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hR hzero
  have hPdeg : (∏ R ∈ Rs, d R).natDegree < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    refine lt_of_le_of_lt ((Polynomial.natDegree_prod_le _ _).trans ?_) hn
    simpa using Finset.sum_le_card_nsmul Rs _ D fun R hR => hdeg R hR
  exact hP0
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ωs.injective hPeval hPdeg)

/-! ## The S5 capstone: good specialization point for a family of factors -/

variable {F : Type} [Field F]

/-- **Hab25 §3, Step S5 (tractable core) — a good specialization point exists.**

Let `Rs` index a family of factors `Rfam R ∈ K[X][Y]` (`K = F(Z) = RatFunc F`) such that each
factor has
* positive `Y`-degree, bounded by `L` (S3 degree data),
* all `Y`-coefficients of `X`-degree `≤ B` (S3 degree data),
* nonzero `Y`-discriminant (separability — the honest deep residual in characteristic `p`).

If `n > |Rs| · 2LB` then some lifted evaluation point `x₀ := liftedDomain ωs i₀` is
**simultaneously good for every factor**: the discriminant survives at `x₀`, and the
specialization `R(x₀, ·) ∈ K[Y]` is nonzero, of unchanged `Y`-degree, and separable.

The avoidance polynomial for each factor is `disc_Y(R) · leadingCoeff_Y(R)`, of `X`-degree
`≤ (2L−1)·B + B = 2LB` by `Polynomial.natDegree_discr_le`; the surviving leading coefficient
gives degree preservation, and the in-tree discriminant/separability bridge does the rest.
This is the full S5 payload consumed by the Hensel lift (S6). -/
theorem exists_good_specialization_point {n : ℕ} (ωs : Fin n ↪ F)
    {I : Type*} (Rs : Finset I) (Rfam : I → (RatFunc F)[X][Y]) {B L : ℕ}
    (hpos : ∀ R ∈ Rs, 0 < (Rfam R).natDegree)
    (hL : ∀ R ∈ Rs, (Rfam R).natDegree ≤ L)
    (hcoeff : ∀ R ∈ Rs, ∀ j, ((Rfam R).coeff j).natDegree ≤ B)
    (hsep : ∀ R ∈ Rs, (Rfam R).discr ≠ 0)
    (hn : Rs.card * (2 * L * B) < n) :
    ∃ i₀ : Fin n, ∀ R ∈ Rs,
      ((Rfam R).discr).eval (liftedDomain ωs i₀) ≠ 0 ∧
      ((Rfam R).map (evalRingHom (liftedDomain ωs i₀))).natDegree = (Rfam R).natDegree ∧
      (Rfam R).map (evalRingHom (liftedDomain ωs i₀)) ≠ 0 ∧
      ((Rfam R).map (evalRingHom (liftedDomain ωs i₀))).Separable := by
  classical
  set d : I → (RatFunc F)[X] := fun R => (Rfam R).discr * (Rfam R).leadingCoeff with hd
  have hd0 : ∀ R ∈ Rs, d R ≠ 0 := by
    intro R hR
    have hne : Rfam R ≠ 0 := by
      intro h0
      have hp := hpos R hR
      rw [h0, Polynomial.natDegree_zero] at hp
      exact Nat.lt_irrefl 0 hp
    exact mul_ne_zero (hsep R hR) (Polynomial.leadingCoeff_ne_zero.mpr hne)
  have hdeg : ∀ R ∈ Rs, (d R).natDegree ≤ 2 * L * B := by
    intro R hR
    have h1 : ((Rfam R).discr).natDegree ≤
        ((Rfam R).natDegree - 1 + (Rfam R).natDegree) * B :=
      Polynomial.natDegree_discr_le _ (hcoeff R hR)
    have h2 : ((Rfam R).leadingCoeff).natDegree ≤ B := hcoeff R hR _
    refine Polynomial.natDegree_mul_le.trans ?_
    have hd1 : (Rfam R).natDegree - 1 + (Rfam R).natDegree + 1 ≤ 2 * L := by
      have hp := hpos R hR
      have hl := hL R hR
      omega
    calc ((Rfam R).discr).natDegree + ((Rfam R).leadingCoeff).natDegree
        ≤ ((Rfam R).natDegree - 1 + (Rfam R).natDegree) * B + B := add_le_add h1 h2
      _ = ((Rfam R).natDegree - 1 + (Rfam R).natDegree + 1) * B := by ring
      _ ≤ 2 * L * B := Nat.mul_le_mul_right _ hd1
  obtain ⟨i₀, hi₀⟩ := exists_common_eval_ne_zero (liftedDomain ωs) Rs d hd0 hdeg hn
  refine ⟨i₀, fun R hR => ?_⟩
  have hboth := hi₀ R hR
  rw [hd, Polynomial.eval_mul] at hboth
  obtain ⟨hdisc, hlc⟩ := mul_ne_zero_iff.mp hboth
  have hmap : ((Rfam R).map (evalRingHom (liftedDomain ωs i₀))).natDegree =
      (Rfam R).natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _
      (by simpa [Polynomial.coe_evalRingHom] using hlc)
  obtain ⟨hne, hsepz⟩ :=
    Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero
      (hpos R hR) hmap (by simpa [Polynomial.coe_evalRingHom] using hdisc)
  exact ⟨hdisc, hmap, hne, hsepz⟩

/-! ## S5 packaged onto the S4 factorization of the GS interpolant -/

/-- **Hab25 §3, Steps S4 + S5 packaged for the generic-fold GS interpolant over `K = F(Z)`.**

There is a GS interpolant `Q` of the generic fold (S2 `Conditions`), factoring into
irreducibles (S4a), such that: for **any** finite subfamily `Rs` of its irreducible factors
carrying the S3-type degree data (`Y`-degree positive and `≤ L`, coefficient `X`-degrees `≤ B`)
and the separability hypothesis (`discr R ≠ 0` — deep in characteristic `p`), once
`n > |Rs|·2LB` there is a lifted domain point at which **every** factor in `Rs` specializes to
a nonzero, degree-preserved, separable polynomial in `K[Y]`.

This is the exact starting configuration of the Hensel lift (S6): a point `x₀ ∈ D` where the
"useful factor" (and all its companions) are separable with simple `Y`-roots. -/
theorem gs_interpolant_good_specialization {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      (∀ q ∈ UniqueFactorizationMonoid.factors Q, Irreducible q) ∧
      Associated (UniqueFactorizationMonoid.factors Q).prod Q ∧
      ∀ (B L : ℕ) (Rs : Finset (RatFunc F)[X][Y]),
        (∀ R ∈ Rs, R ∈ (UniqueFactorizationMonoid.factors Q).toFinset) →
        (∀ R ∈ Rs, 0 < R.natDegree) →
        (∀ R ∈ Rs, R.natDegree ≤ L) →
        (∀ R ∈ Rs, ∀ j, (R.coeff j).natDegree ≤ B) →
        (∀ R ∈ Rs, R.discr ≠ 0) →
        Rs.card * (2 * L * B) < n →
        ∃ i₀ : Fin n, ∀ R ∈ Rs,
          (R.discr).eval (liftedDomain ωs i₀) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).natDegree = R.natDegree ∧
          R.map (evalRingHom (liftedDomain ωs i₀)) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).Separable := by
  obtain ⟨Q, hQ, hirr, hprod⟩ := gs_interpolant_factorization k m ωs f₀ f₁ hk1 hn0 hm
  refine ⟨Q, hQ, hirr, hprod, ?_⟩
  intro B L Rs _hfactors hpos hL hcoeff hsep hcard
  exact exists_good_specialization_point ωs Rs (fun R => R) hpos hL hcoeff hsep hcard

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.exists_common_eval_ne_zero
#print axioms GuruswamiSudan.OverRatFunc.exists_good_specialization_point
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_good_specialization
