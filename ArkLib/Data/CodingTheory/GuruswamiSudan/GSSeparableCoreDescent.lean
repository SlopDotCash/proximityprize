/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSeparableContraction

/-!
# Hab25 §3 Step S5, any characteristic: descent of the separable cores and the full capstone

`GSSeparableContraction.lean` produced, for each irreducible factor `R` of the GS interpolant,
a separable core `g` over the function field `L = K(X)` with `expand (q^m) g = R` and
`discr g ≠ 0`, leaving "descend `g` to `K[X][Y]` with controlled `X`-degrees" as the
quantitative gap. This file closes that gap — **for free** — and with it Step S5 in every
characteristic:

* The key observation: `expand` only *spreads* coefficients (`(expand R p f).coeff (n·p) =
  f.coeff n`, zeros elsewhere), so the core is `G := contract (q^m) R ∈ K[X][Y]` — its
  `Y`-coefficients are literally `Y`-coefficients of `R`. Hence
  - `G.map φ = g` (`map_contract` + `contract_expand`), so `discr G ≠ 0` descends from
    `discr g ≠ 0` along the `discr` specialization commutation;
  - `expand (q^m) G = R` already over `K[X]` (injectivity of `map φ`);
  - every `Y`-coefficient of `G` has `X`-degree `≤ degreeX R` **with no denominator
    clearing** (`coeff_contract`).
  This is `irreducible_factor_core_descent`.

* `gs_interpolant_good_specialization_expChar` — **Step S5, complete, any exponential
  characteristic `q`**: there is a generic-fold GS interpolant `Q` (S2) with the Claim-5.4
  degree data (S3) and UFD factorization (S4a) such that for any finite family `Rs` of
  positive-`Y`-degree irreducible factors of `Q`, in the paper regime
  `|Rs| · 2·(D/(k−1))·D < n` some lifted evaluation point `x₀` is good for **the separable
  cores of all factors simultaneously**: each `R ∈ Rs` is `expand (q^e) G` of a core
  `G ∈ K[X][Y]` whose specialization at `x₀` is nonzero, degree-preserved, and separable.
  *No residual hypotheses.* In characteristic zero (`q = 1`) the cores are the factors
  themselves and this recovers `gs_interpolant_good_specialization_charZero`.

This is exactly the configuration the Hensel lift (S6) consumes: at `x₀`, every separable
core has simple `Y`-roots, and the factor is a `q`-power expansion of its core.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- **Descent of the separable core to `K[X][Y]`.** For `ExpChar F q` and `R ∈ K[X][Y]`
irreducible of positive `Y`-degree, the contraction `G := contract (q^m) R` is a polynomial
over `K[X]` (its `Y`-coefficients are `Y`-coefficients of `R`, so all `X`-degree bounds are
inherited verbatim) with `expand (q^m) G = R`, positive `Y`-degree, the inseparable degree
bookkeeping `deg G · q^m = deg_Y R`, and `discr G ≠ 0` over `K[X]`. -/
theorem irreducible_factor_core_descent (q : ℕ) [ExpChar F q]
    {R : (RatFunc F)[X][Y]} (hirr : Irreducible R) (hdeg : 0 < R.natDegree) :
    ∃ (G : (RatFunc F)[X][Y]) (m : ℕ),
      Polynomial.expand _ (q ^ m) G = R ∧
      0 < G.natDegree ∧
      G.natDegree * q ^ m = R.natDegree ∧
      G.discr ≠ 0 ∧
      ∀ j, (G.coeff j).natDegree ≤ degreeX R := by
  classical
  obtain ⟨g, m, hgsep, hgirr, hgdeg, hgdiscr, hexp, hdeg_eq⟩ :=
    irreducible_factor_separable_contraction q hirr hdeg
  set φ := algebraMap ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])) with hφ
  have hinj : Function.Injective φ :=
    IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X]))
  have hq0 : q ≠ 0 := (expChar_pos F q).ne'
  have hqm : q ^ m ≠ 0 := pow_ne_zero m hq0
  set G : (RatFunc F)[X][Y] := Polynomial.contract (q ^ m) R with hG
  have hmapG : G.map φ = g := by
    rw [hG, Polynomial.map_contract hqm, ← hexp, Polynomial.contract_expand _ hqm]
  have hexpG : Polynomial.expand _ (q ^ m) G = R := by
    apply Polynomial.map_injective φ hinj
    rw [Polynomial.map_expand, hmapG, hexp]
  have hpres : (G.map φ).natDegree = G.natDegree := natDegree_map_eq_of_injective hinj G
  have hndeg : G.natDegree = g.natDegree := by rw [← hmapG, hpres]
  have hGdeg : 0 < G.natDegree := hndeg ▸ hgdeg
  have hGdiscr : G.discr ≠ 0 := by
    have h1 : (G.map φ).discr ≠ 0 := by rw [hmapG]; exact hgdiscr
    rw [Polynomial.discr_map_of_natDegree_preserved hGdeg hpres] at h1
    exact fun h0 => h1 (by rw [h0, map_zero])
  refine ⟨G, m, hexpG, hGdeg, by rw [hndeg]; exact hdeg_eq, hGdiscr, fun j => ?_⟩
  have hcj : G.coeff j = R.coeff (j * q ^ m) := by
    rw [hG, Polynomial.coeff_contract hqm]
  rw [hcj]
  exact coeff_natDegree_le_degreeX R _

/-- **Hab25 §3, Step S5 — complete, any exponential characteristic.**

There is a generic-fold GS interpolant `Q` over `K = F(Z)` (S2 `Conditions`) with
`degreeX Q ≤ D := gs_degree_bound k n m₀` and `deg_Y Q ≤ D/(k−1)` (S3), factoring into
irreducibles (S4a), such that for **any** finite family `Rs` of positive-`Y`-degree members
of `factors Q`, in the paper regime `|Rs| · 2·(D/(k−1))·D < n` some lifted evaluation point
`x₀` is simultaneously good for the **separable cores** of all of `Rs`: each `R ∈ Rs` equals
`expand (q^e) G` for a core `G ∈ K[X][Y]` with `deg G · q^e = deg_Y R` whose specialization
along `X ↦ x₀` is nonzero, degree-preserved, and **separable**.

No residual hypotheses remain: separability of the cores is supplied by the contraction
(Stacks 09H0) + converse-discriminant chain, the degree data by `contract`/divisor
inheritance, and the avoidance count by the regime. This is the full S5 of Hab25 §3; the
Hensel lift (S6) starts from exactly this configuration. -/
theorem gs_interpolant_good_specialization_expChar (q : ℕ) [ExpChar F q]
    {n : ℕ} (k m₀ : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m₀) (hk : 0 < k - 1) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m₀ (gs_degree_bound k n m₀)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      degreeX Q ≤ gs_degree_bound k n m₀ ∧
      Q.natDegree ≤ gs_degree_bound k n m₀ / (k - 1) ∧
      (∀ p ∈ UniqueFactorizationMonoid.factors Q, Irreducible p) ∧
      Associated (UniqueFactorizationMonoid.factors Q).prod Q ∧
      ∀ Rs : Finset (RatFunc F)[X][Y],
        (∀ R ∈ Rs, R ∈ UniqueFactorizationMonoid.factors Q) →
        (∀ R ∈ Rs, 0 < R.natDegree) →
        Rs.card * (2 * (gs_degree_bound k n m₀ / (k - 1)) * gs_degree_bound k n m₀) < n →
        ∃ i₀ : Fin n, ∀ R ∈ Rs,
          ∃ (G : (RatFunc F)[X][Y]) (e : ℕ),
            Polynomial.expand _ (q ^ e) G = R ∧
            0 < G.natDegree ∧
            G.natDegree * q ^ e = R.natDegree ∧
            (G.discr).eval (liftedDomain ωs i₀) ≠ 0 ∧
            (G.map (evalRingHom (liftedDomain ωs i₀))).natDegree = G.natDegree ∧
            G.map (evalRingHom (liftedDomain ωs i₀)) ≠ 0 ∧
            (G.map (evalRingHom (liftedDomain ωs i₀))).Separable := by
  classical
  obtain ⟨Q, hQ, hydeg⟩ := genericInterpolant_yDegree_le k m₀ ωs f₀ f₁ hk1 hn0 hm hk
  have hxdeg : degreeX Q ≤ gs_degree_bound k n m₀ := conditions_degreeX_le hQ
  refine ⟨Q, hQ, hxdeg, hydeg,
    fun p hp => UniqueFactorizationMonoid.irreducible_of_factor p hp,
    UniqueFactorizationMonoid.factors_prod hQ.Q_ne_0, ?_⟩
  intro Rs hmem hpos hcard
  -- the core data of a factor, as a single existential over a pair
  set P : (RatFunc F)[X][Y] → ((RatFunc F)[X][Y] × ℕ) → Prop := fun R Ge =>
    Polynomial.expand _ (q ^ Ge.2) Ge.1 = R ∧ 0 < Ge.1.natDegree ∧
    Ge.1.natDegree * q ^ Ge.2 = R.natDegree ∧ Ge.1.discr ≠ 0 ∧
    ∀ j, (Ge.1.coeff j).natDegree ≤ degreeX R with hP
  have hPex : ∀ R ∈ Rs, ∃ Ge, P R Ge := by
    intro R hR
    obtain ⟨G, e, h1, h2, h3, h4, h5⟩ := irreducible_factor_core_descent q
      (UniqueFactorizationMonoid.irreducible_of_factor R (hmem R hR)) (hpos R hR)
    exact ⟨(G, e), h1, h2, h3, h4, h5⟩
  set core : (RatFunc F)[X][Y] → ((RatFunc F)[X][Y] × ℕ) := fun R =>
    if h : ∃ Ge, P R Ge then h.choose else (1, 0) with hcore
  have hcoreP : ∀ R ∈ Rs, P R (core R) := by
    intro R hR
    have h := hPex R hR
    simp only [hcore, dif_pos h]
    exact h.choose_spec
  -- divisor degree data for the factors
  have hRdvd : ∀ R ∈ Rs, R ∣ Q := fun R hR =>
    UniqueFactorizationMonoid.dvd_of_mem_factors (hmem R hR)
  -- run the avoidance engine on the cores
  obtain ⟨i₀, hi₀⟩ := exists_good_specialization_point ωs Rs (fun R => (core R).1)
    (fun R hR => (hcoreP R hR).2.1)
    (fun R hR => by
      -- deg core ≤ deg_Y R ≤ deg_Y Q ≤ D/(k−1)
      have h1 : (core R).1.natDegree ≤ R.natDegree := by
        have := (hcoreP R hR).2.2.1
        have hqe : 0 < q ^ (core R).2 := pow_pos (expChar_pos F q) _
        calc (core R).1.natDegree
            ≤ (core R).1.natDegree * q ^ (core R).2 := Nat.le_mul_of_pos_right _ hqe
          _ = R.natDegree := this
      exact h1.trans ((Polynomial.natDegree_le_of_dvd (hRdvd R hR) hQ.Q_ne_0).trans hydeg))
    (fun R hR j => by
      -- coeff X-degrees of the core ≤ degreeX R ≤ degreeX Q ≤ D
      exact ((hcoreP R hR).2.2.2.2 j).trans
        ((degreeX_le_of_dvd (hRdvd R hR) hQ.Q_ne_0).trans hxdeg))
    (fun R hR => (hcoreP R hR).2.2.2.1)
    hcard
  refine ⟨i₀, fun R hR => ?_⟩
  obtain ⟨hexp, hdeg', hmul, hdiscr, _⟩ := hcoreP R hR
  obtain ⟨heval, hpres, hne, hsep⟩ := hi₀ R hR
  exact ⟨(core R).1, (core R).2, hexp, hdeg', hmul, heval, hpres, hne, hsep⟩

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.irreducible_factor_core_descent
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_good_specialization_expChar
