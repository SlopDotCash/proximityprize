/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.FieldDischarge

/-!
# Claim 5.7 residuals over the *descended* factor set (BCIKS20 §5, Finding F10 fix)

`ProximityGap.Claim57Residuals` (`Agreement.lean`) carries a field

```
hfactor : ∀ R ∈ pg_Rset h_gs, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose
```

Finding **F10** established that this field is **structurally unprovable**.  The two finite sets
involved are genuinely different objects:

* `pg_Rset h_gs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset`
  (`Extraction.pg_Rset`, `Extraction.lean:724`) — *all* normalized factors of `Q`, including the
  degree-`0` ones and, in characteristic `p`, the *inseparable* ones.
* `(irreducible_factorization_of_gs_solution h_gs).choose_spec.choose` — the **descended
  primitive-separable** list built by `eq512_factor_descent` (`Extraction.lean:340`), where each
  positive-`Y`-degree normalized factor `g` is written `g = C u · expand (qᵐ) r` for a descended
  root `r` that is *primitive*, *fraction-field separable*, and irreducible.

In characteristic `p` an inseparable normalized factor `g` is a proper `p`-power image
`g = C u · expand (qᵐ) r` of its descended root `r ≠ g`; and the degree-`0` normalized factors are
dropped from the descended list entirely.  So `pg_Rset` and the descended list diverge, and the
inclusion `pg_Rset ⊆ descended` (the `hfactor` direction) cannot hold in general.

## This file: the descended-set replacement

We define

```
pg_RsetDescended h_gs := (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.toFinset
```

i.e. the `toFinset` of the descended list *itself*.  Against this set the analogue of `hfactor`
(membership in the descended list) is **definitionally trivial** — it is exactly
`Finset.mem_toFinset`.  We then re-establish the API surface the §5 consumers need, *directly from
the existential bundle* of `irreducible_factorization_of_gs_solution`:

* `pg_RsetDescended_irreducible`     — every member is `Irreducible`;
* `pg_RsetDescended_separable_FF`    — every member is separable over `FractionRing (F[Z][X])`;
* `pg_RsetDescended_natDegree_pos`   — every member has positive `Y`-degree;
* `pg_RsetDescended_discr_y_ne_zero` — every member has `discr_y ≠ 0` (the Claim-5.6 substrate);
* `pg_RsetDescended_comp_dvd_Q`      — every member `r` satisfies `r.comp (X^a) ∣ Q` for some `a ≥ 1`
                                       (the `expand`-shape divisibility read off the factorization
                                       equation);
* `pg_RsetDescended_nonempty`        — nonemptiness, under the same `Q`-has-a-positive-degree-factor
                                       hypothesis that makes `pg_Rset` nonempty for the §5 argument.

The **descent correspondence** `∀ r ∈ pg_RsetDescended, ∃ g ∈ pg_Rset, …` and the
**coincidence** `pg_RsetDescended = pg_Rset` under separability are provided as the *honest bridges*
(`pg_RsetDescended_descent_correspondence`, `pg_RsetDescended_eq_pg_Rset_of_*`): the per-member
`g = C u · expand (qᵐ) r` descent datum lives *inside* the proof of
`irreducible_factorization_of_gs_solution` and is **not** recoverable from its `.choose_spec`, so the
correspondence is taken as an input where it cannot be re-derived (this is the same honesty that
forced `hfactor` to be a hypothesis in the first place).

## Adequacy of the descended set for the §5 (Hensel / ClaimA2) chain

The descended variant **changes which polynomials** the downstream §5 lemmas run on (this is the
real char-`p` divergence — `r` rather than `g`).  We claim this is the *right* object.  The §5
consumers downstream of Claim 5.7 are the Hensel / Appendix-A.4 `ClaimA2` chain.  Tracing them:

* `Agreement.claimA2_hypotheses` packages everything the chain needs about the extracted factor `R`
  into `BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H`.
* That structure (`RationalFunctionsCore.lean:2170`) has exactly **two** fields:
  `dvd_evalX : H ∣ Bivariate.evalX (C x₀) R` and
  `separable_evalX : (Bivariate.evalX (C x₀) R).Separable`,
  together with the ambient `Fact (Irreducible H)` and `Fact (0 < H.natDegree)`.

So the chain consumes `R` purely as a polynomial through `evalX (C x₀) R` (its `x₀`-specialization
divisibility-by-`H` and separability) — it **never** consults `R ∈ descended list`, nor any property
of `R` beyond `irreducible + positive-degree + separable-at-x₀`.  Membership in a particular factor
list is used *only* to land the existence statement `exists_factors_with_large_common_root_set`; once
`R` is extracted it is an opaque polynomial.  Every property the chain reads off `R`
(`irreducible`, `positive Y-degree`, `evalX`-separability via `discr_y ≠ 0`) is one this file proves
for the descended members.  Hence the descended set carries exactly the adequate API surface, and
replacing `pg_Rset` by `pg_RsetDescended` in the residual bundle loses nothing the §5 chain needs
while making the `hfactor` obligation definitionally true.

## Incremental adoption

`Claim57ResidualsDescended` is `Claim57Residuals` with `hfactor` **removed** (it is now
`Finset.mem_toFinset`-trivial) and the other fields restated over `pg_RsetDescended`.  It is
constructed by `Claim57ResidualsDescended.ofInTree` from the same per-field discharges used by
`Claim57Residuals.ofInTree2` (the avoidance argument `exists_good_x₀_X_shape_ne` restated over the
descended finite set).  The bridge `Claim57Residuals.ofDescended` converts a
`Claim57ResidualsDescended` back into a full `Claim57Residuals` under the coincidence hypothesis
`pg_RsetDescended = pg_Rset` (the separable / characteristic-`0` case), so the issue-#8 owner can
adopt the descended bundle incrementally without disrupting existing `Claim57Residuals` consumers.

No `sorry`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claim 5.6 — good specialization point; Claim 5.7 — graph extraction; Eq. 5.12 — separable
  descended factorization of the GS solution; Appendix A.4 — Claim A.2 Hensel lifting).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-! ## The descended factor set and its `hfactor`-trivial membership -/

/-- **The descended primitive-separable factor set.**

The `toFinset` of the descended list produced by `irreducible_factorization_of_gs_solution`.  By
construction, membership in this set is *exactly* membership in the descended list (the property the
`Claim57Residuals.hfactor` field demands of `pg_Rset` members but which fails for `pg_Rset`); see
`pg_RsetDescended_mem_iff` and `mem_pg_RsetDescended_iff_mem_list`. -/
noncomputable def pg_RsetDescended
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Finset F[Z][X][Y] :=
  (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.toFinset

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **`hfactor`, definitionally true over the descended set.**  Membership in `pg_RsetDescended`
*is* membership in the descended list `(irreducible_factorization_of_gs_solution h_gs).choose_spec.choose`.
This is the `Claim57Residuals.hfactor` field, but landed *by construction* via `Finset.mem_toFinset`
— the F10-unprovable bridge for `pg_Rset` is here a triviality. -/
theorem mem_pg_RsetDescended_iff_mem_list
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (R : F[Z][X][Y]) :
    R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs ↔
      R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose := by
  unfold pg_RsetDescended
  exact List.mem_toFinset

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **`hfactor` field, definitional form.**  Every member of `pg_RsetDescended` lies in the descended
list — the exact shape of `Claim57Residuals.hfactor`, now `Finset.mem_toFinset`-trivial. -/
theorem pg_RsetDescended_hfactor
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose :=
  fun R hR => (mem_pg_RsetDescended_iff_mem_list (k := k) h_gs R).1 hR

/-! ## Bundle accessors — the descended list's proven properties

`irreducible_factorization_of_gs_solution` bundles, for its chosen list `R`, the conjunction
`(∀ Rᵢ ∈ R, (Rᵢ.map …).Separable) ∧ (∀ Rᵢ ∈ R, Irreducible Rᵢ) ∧ (∀ Rᵢ ∈ R, 0 < Rᵢ.natDegree)`
(plus the length / `e ≥ 1` / factorization-equation conjuncts).  We read each one off for the
`toFinset` members. -/

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- Every descended factor is **irreducible** (bundle field). -/
theorem pg_RsetDescended_irreducible
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Irreducible R := by
  intro R hR
  have hRl := (mem_pg_RsetDescended_iff_mem_list (k := k) h_gs R).1 hR
  have hspec := (irreducible_factorization_of_gs_solution h_gs)
      |>.choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨_hlen1, _hlen2, _he, _hsep, hirr, _hpos, _hfact⟩ := hspec
  exact hirr R hRl

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- Every descended factor is **separable over the fraction field** `FractionRing (F[Z][X])`
(bundle field) — the repaired Eq-5.12 separability conjunct. -/
theorem pg_RsetDescended_separable_FF
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (R.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable := by
  intro R hR
  have hRl := (mem_pg_RsetDescended_iff_mem_list (k := k) h_gs R).1 hR
  have hspec := (irreducible_factorization_of_gs_solution h_gs)
      |>.choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨_hlen1, _hlen2, _he, hsep, _hirr, _hpos, _hfact⟩ := hspec
  exact hsep R hRl

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- Every descended factor has **positive `Y`-degree** (bundle field). -/
theorem pg_RsetDescended_natDegree_pos
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        0 < R.natDegree := by
  intro R hR
  have hRl := (mem_pg_RsetDescended_iff_mem_list (k := k) h_gs R).1 hR
  have hspec := (irreducible_factorization_of_gs_solution h_gs)
      |>.choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨_hlen1, _hlen2, _he, _hsep, _hirr, hpos, _hfact⟩ := hspec
  exact hpos R hRl

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- Every descended factor has **nonvanishing `discr_y`** — the Claim-5.6 specialization substrate,
derived from fraction-field separability + positive degree via `discr_y_ne_zero_of_sep`.  (Note: this
holds for *every* descended member, whereas over `pg_Rset` it needs the extra honest per-factor
positive-degree + separability side conditions, precisely because `pg_Rset` includes the degree-`0`
and inseparable normalized factors that the descent strips out.) -/
theorem pg_RsetDescended_discr_y_ne_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.discr_y R ≠ 0 := by
  intro R hR
  exact discr_y_ne_zero_of_sep R
    (pg_RsetDescended_separable_FF (k := k) h_gs R hR)
    (pg_RsetDescended_natDegree_pos (k := k) h_gs R hR)

/-! ## `expand`-shape divisibility of `Q` (factorization-equation field)

The bundle's factorization equation `Q = C C * ∏ i ∈ range L.length, ((Rᵢ.comp X^fᵢ))^eᵢ` (with
`eᵢ ≥ 1`) lets us read off, for each list index `i`, that `(Rᵢ.comp X^fᵢ) ∣ Q`.  Since the descended
roots arise as `g = C u · expand nn r = C u · (r.comp X^nn)` for normalized factors `g ∣ Q`, this is
the honest `expand`-shape divisibility — the descended analogue of `pg_Rset`'s `dvd_of_mem_normalizedFactors`. -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- **Abstract `expand`-shape divisibility.**  Pure list/product fact, stated over *abstract* data
`C₀, L, f, e` so its proof never reduces the giant `irreducible_factorization_of_gs_solution` choice
term (which would blow up `whnf`).  If `Q = C C₀ · ∏ⱼ ((L.getD j 1).comp X^(f.getD j 0))^(e.getD j 0)`
with every exponent `≥ 1`, then for each index `i` the `i`-th factor divides `Q`. -/
theorem comp_getD_dvd_of_factorization
    (Q' : F[Z][X][Y]) (C₀ : F[Z][X]) (L : List F[Z][X][Y]) (f e : List ℕ)
    (hlen1 : L.length = f.length) (hlen2 : f.length = e.length)
    (he : ∀ eᵢ ∈ e, 1 ≤ eᵢ)
    (hfact : Q' = Polynomial.C C₀ *
      ∏ j ∈ Finset.range L.length,
        ((L.getD j 1).comp ((Polynomial.X : F[Z][X][Y]) ^ f.getD j 0)) ^ e.getD j 0)
    (i : ℕ) (hi : i < L.length) :
    ((L.getD i 1).comp ((Polynomial.X : F[Z][X][Y]) ^ (f.getD i 0))) ∣ Q' := by
  classical
  set body : ℕ → F[Z][X][Y] := fun j =>
    ((L.getD j 1).comp ((Polynomial.X : F[Z][X][Y]) ^ (f.getD j 0))) ^ (e.getD j 0) with hbodydef
  have hmem : i ∈ Finset.range L.length := Finset.mem_range.mpr hi
  have hdvd_prod : body i ∣ ∏ j ∈ Finset.range L.length, body j :=
    Finset.dvd_prod_of_mem body hmem
  have hprod_dvd_Q : (∏ j ∈ Finset.range L.length, body j) ∣ Q' :=
    Dvd.intro_left (Polynomial.C C₀) hfact.symm
  have hlen_e : e.length = L.length := by rw [← hlen2, ← hlen1]
  have hie : i < e.length := by rw [hlen_e]; exact hi
  have hei : 1 ≤ e.getD i 0 := by
    have hmem_e : e.getD i 0 ∈ e := by
      rw [List.getD_eq_getElem e 0 hie]
      exact List.mem_iff_getElem.2 ⟨i, hie, rfl⟩
    exact he _ hmem_e
  have hcomp_dvd_body : ((L.getD i 1).comp ((Polynomial.X : F[Z][X][Y]) ^ (f.getD i 0)))
      ∣ body i := dvd_pow_self _ (by omega)
  exact dvd_trans hcomp_dvd_body (dvd_trans hdvd_prod hprod_dvd_Q)

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **`expand`-shape divisibility (indexed form).**  For each index `i` into the descended list, the
`i`-th factor `(R.getD i 1).comp (X^(f.getD i 0))` divides `Q` (it appears, to a power `≥ 1`, in the
factorization equation).  Proved by instantiating the abstract `comp_getD_dvd_of_factorization` at the
chosen data, so the giant choice term is only *substituted*, never reduced. -/
theorem pg_RsetDescended_comp_getD_dvd_Q
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (i : ℕ)
    (hi : i < (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.length) :
    (((irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.getD i 1).comp
        ((Polynomial.X : F[Z][X][Y]) ^
          ((irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD i 0)))
      ∣ Q := by
  classical
  obtain ⟨hlen1, hlen2, he, _hsep, _hirr, _hpos, hfact, _hfpos⟩ :=
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose_spec
  exact comp_getD_dvd_of_factorization Q
    (irreducible_factorization_of_gs_solution h_gs).choose
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose
    hlen1 hlen2 he hfact i hi

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **`expand`-shape divisibility (member form).**  Every descended factor `R` admits an exponent
`a ≥ 1` with `R.comp (X^a) ∣ Q`.  This is the honest descended replacement of the `pg_Rset`
divisibility `R ∣ Q` (`UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`): in characteristic
`p` the descended root `R` itself need not divide `Q`, but its `expand`-image `R.comp (X^a) = expand a R`
does — exactly the inseparable `p`-power relation `g = C u · expand a R` for the normalized factor
`g ∣ Q`. -/
theorem pg_RsetDescended_comp_dvd_Q
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        ∃ a : ℕ, (R.comp ((Polynomial.X : F[Z][X][Y]) ^ a)) ∣ Q := by
  intro R hR
  classical
  have hRl := (mem_pg_RsetDescended_iff_mem_list (k := k) h_gs R).1 hR
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hRl
  -- `getD i 1 = R` at this index
  have hgetD :
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.getD i 1 = R := by
    rw [List.getD_eq_getElem _ 1 hi]; exact hget
  refine ⟨(irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD i 0,
    ?_⟩
  have hdvd := pg_RsetDescended_comp_getD_dvd_Q (k := k) h_gs i hi
  rwa [hgetD] at hdvd

/-! ## Nonemptiness

`pg_Rset` is nonempty exactly when `Q` has a normalized factor.  `pg_RsetDescended` is the descended
*positive-degree* factor set, so it is nonempty exactly when `Q` has a *positive-degree* normalized
factor — equivalently when the descended list is nonempty.  We expose both the direct (list-nonempty)
form and the genuine §5 hypothesis form. -/

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **Nonemptiness (list form).**  `pg_RsetDescended` is nonempty iff the descended list is. -/
theorem pg_RsetDescended_nonempty_iff
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    (pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).Nonempty ↔
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ≠ [] := by
  unfold pg_RsetDescended
  rw [List.toFinset_nonempty_iff]

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **Nonemptiness (hypothesis form).**  Under the genuine §5 hypothesis that the descended list is
nonempty (the descended analogue of "`Q` has a positive-`Y`-degree normalized factor", which is what
the §5 argument needs `pg_Rset` nonemptiness for), `pg_RsetDescended` is nonempty. -/
theorem pg_RsetDescended_nonempty
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hne : (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ≠ []) :
    (pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).Nonempty :=
  (pg_RsetDescended_nonempty_iff (k := k) h_gs).2 hne

/-! ## The descent correspondence and the coincidence bridge (honest)

The per-member descent datum `g = C u · expand nn r` (relating a `pg_Rset` member `g` to its
descended root `r`) lives *inside* the proof of `irreducible_factorization_of_gs_solution` and is not
exposed by its `.choose_spec`.  Recovering it from the bundle alone is exactly the obstruction that
made `hfactor` unprovable.  We therefore take the correspondence as an honest input where it cannot be
re-derived, and prove the coincidence in the separable case from it. -/

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **Descent correspondence (honest bridge).**  Given the per-member descent witness — for each
descended root `r` a normalized factor `g ∈ pg_Rset` and exponent/unit data with
`g = C u · expand a r` — the correspondence `∀ r ∈ pg_RsetDescended, ∃ g ∈ pg_Rset, …` holds.

The hypothesis `hcorr` is the descent datum produced by `eq512_factor_descent` internally; it is
supplied here rather than re-derived because the `.choose_spec` of `irreducible_factorization_of_gs_solution`
does not expose the per-member `g`/`u`/`a`.  This is the honest record of the F10 divergence. -/
theorem pg_RsetDescended_descent_correspondence
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcorr : ∀ r : F[Z][X][Y],
      r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        ∃ (g : F[Z][X][Y]) (u : F[Z][X]) (a : ℕ),
          g ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
              (u₀ := u₀) (u₁ := u₁) h_gs ∧
          IsUnit u ∧
          g = Polynomial.C u * (Polynomial.expand (F[Z][X]) a r)) :
    ∀ r : F[Z][X][Y],
      r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        ∃ (g : F[Z][X][Y]) (u : F[Z][X]) (a : ℕ),
          g ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
              (u₀ := u₀) (u₁ := u₁) h_gs ∧
          IsUnit u ∧
          g = Polynomial.C u * (Polynomial.expand (F[Z][X]) a r) :=
  hcorr

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **Coincidence in the separable case (honest bridge).**  When the two factor families agree as
finite sets — the situation in characteristic `0`, or whenever every normalized factor of `Q` is
separable with descent exponent `1`, so the descent is the identity — `pg_RsetDescended = pg_Rset`.
Supplied as a hypothesis-gated bridge: `hcoincide` is the separability/characteristic side condition
under which the descent collapses, and the conclusion is the set equality the owner uses in
`Claim57Residuals.ofDescended`. -/
theorem pg_RsetDescended_eq_pg_Rset_of_coincide
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs :=
  hcoincide

/-! ## `Claim57ResidualsDescended` — the `hfactor`-free residual bundle

`Claim57Residuals` with `hfactor` removed (definitionally true over the descended set) and the other
fields restated over `pg_RsetDescended`. -/

/-- **Claim-5.7 residual bundle over the descended factor set.**

Identical to `ProximityGap.Claim57Residuals` except:
* the `hfactor` field is **gone** — over `pg_RsetDescended` it is `Finset.mem_toFinset`-trivial
  (`pg_RsetDescended_hfactor`), so there is nothing left to assume;
* the `hx0` / `hsep` fields range over `pg_RsetDescended` instead of `pg_Rset`.

The Johnson / largeness fields (`hS_nonempty`, `A`, `hA`, `hcount`, `hlarge`) are unchanged — they do
not mention the factor set. -/
class Claim57ResidualsDescended (k : ℕ) (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) where
  hx0 : ∀ R : F[Z][X][Y],
    R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs →
      Bivariate.evalX (Polynomial.C x₀) R ≠ 0
  hsep : ∀ R : F[Z][X][Y],
    R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs →
      (Bivariate.evalX (Polynomial.C x₀) R).Separable
  hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty
  A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n)
  hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
    ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
      (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i)
  hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
    Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card
  hlarge : #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q

/-! ## Constructor — the descended bundle from the per-field discharges

Same arguments as `Claim57Residuals.ofInTree2`: the `hx0`/`hsep` pair is produced by the avoidance
argument restated over the descended finite set, and the Johnson/largeness data is passed through.
The `hfactor` argument that `ofInTree2` still carries is *dropped* here. -/

omit [DecidableEq (RatFunc F)] in
/-- **`hx0` over the descended set (avoidance, restated).**  The exact `exists_good_x₀_X_shape_ne`
argument — count the `X`-specialization bad sets and avoid them with the field-size budget — run over
`pg_RsetDescended.toList` instead of `pg_Rset.toList`.  Same proof structure; the only change is the
finite set the sum/avoidance ranges over. -/
theorem exists_good_x₀_X_shape_ne_descended [Fintype F]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F) :
    ∃ x₀ : F,
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0 := by
  classical
  set L : List F[Z][X][Y] :=
    (pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).toList with hLdef
  have hmem : ∀ R, R ∈ L ↔
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs := by
    intro R; rw [hLdef]; exact Finset.mem_toList
  set bad : F[Z][X][Y] → Finset F := claim57_badXC with hbad
  have hbad_card : ∀ R ∈ L, (bad R).card
      ≤ (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree := by
    intro R hR
    exact claim57_badXC_card_le R (z R) (hlead R ((hmem R).1 hR))
  have hsum_le :
      (L.map (fun R => (bad R).card)).sum
        ≤ (L.map (fun R =>
            (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum :=
    List.sum_le_sum hbad_card
  have hsum_lt : (L.map (fun R => (bad R).card)).sum < Fintype.card F :=
    lt_of_le_of_lt hsum_le hcard
  obtain ⟨x₀, hx₀⟩ := c56_exists_avoiding L bad hsum_lt
  refine ⟨x₀, fun R hR => ?_⟩
  have hRL : R ∈ L := (hmem R).2 hR
  have := hx₀ R hRL
  rw [hbad, claim57_badXC] at this
  simpa [Finset.mem_filter] using this

omit [DecidableEq (RatFunc F)] in
/-- **`hx0` ∧ `hsep` over the descended set.**  Combines the descended avoidance discharge with the
honest per-point separability residual `hsepPt`, producing the exact `hx0`/`hsep` field pair of
`Claim57ResidualsDescended`. -/
theorem exists_good_x₀_X_shape_descended [Fintype F]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
    ∃ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) ∧
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable) := by
  obtain ⟨x₀, hx₀⟩ := exists_good_x₀_X_shape_ne_descended (k := k) h_gs z hlead hcard
  exact ⟨x₀, hx₀, hsepPt x₀ hx₀⟩

/-- **`Claim57ResidualsDescended` from the per-field discharges.**

The descended residual bundle from the same honest in-tree inputs `Claim57Residuals.ofInTree2`
consumes — *minus* `hfactor`, which is definitionally discharged over the descended set.  The good
specialization point `x₀` is produced internally by `exists_good_x₀_X_shape_descended`; the
Johnson / largeness fields are supplied directly.

Inputs:
* `z` / `hlead` / `hcard` — the honest `X`-specialization budget (per-factor `Z`-witness not killing
  the leading coefficient, and the [BCIKS20] large-field bound on the total `X`-degree), over the
  descended set;
* `hsepPt` — the honest §5 good-point separability residual over the descended set;
* `hS_nonempty` / `A` / `hA` / `hcount` / `hlarge` — the Johnson / largeness data (unchanged).

There is **no** `hfactor` input — that is the whole point of the descended variant. -/
@[reducible]
noncomputable def Claim57ResidualsDescended.ofInTree [Fintype F] (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Σ' x₀ : F,
      Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  let good := exists_good_x₀_X_shape_descended (k := k) h_gs z hlead hcard hsepPt
  ⟨good.choose,
    { hx0 := good.choose_spec.1
      hsep := good.choose_spec.2
      hS_nonempty := hS_nonempty
      A := A
      hA := hA
      hcount := hcount
      hlarge := hlarge }⟩

/-! ## Incremental adoption bridge — `Claim57Residuals.ofDescended`

Under the coincidence hypothesis `pg_RsetDescended = pg_Rset` (the separable / characteristic-`0`
case), a `Claim57ResidualsDescended` bundle yields a full `Claim57Residuals` bundle: the `hx0`/`hsep`
fields transport along the set equality, the Johnson/largeness fields are identical, and `hfactor`
becomes the now-trivial `pg_RsetDescended_hfactor` (rewritten along the coincidence).  This lets the
issue-#8 owner adopt the descended bundle while still satisfying existing `Claim57Residuals`
consumers, with no disruption. -/

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **Graph-extraction bridge from the descended bundle.**  A `Claim57ResidualsDescended` instance
produces the smaller `GraphExtractionHypotheses` package under the same coincidence
`pg_RsetDescended = pg_Rset`.  This exposes the hfactor-free graph/count data directly, for callers
that want the graph-extraction API rather than the legacy `Claim57Residuals` class. -/
@[reducible]
def GraphExtractionHypotheses.ofDescended
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs where
  hx0 := by
    intro R hR
    exact hres.hx0 R (hcoincide.symm ▸ hR)
  hsep := by
    intro R hR
    exact hres.hsep R (hcoincide.symm ▸ hR)
  hS_nonempty := hres.hS_nonempty
  A := hres.A
  hA := hres.hA
  hcount := hres.hcount
  hlarge := hres.hlarge

/-- **Graph-extraction bridge from explicit descended in-tree inputs.**

This combines `Claim57ResidualsDescended.ofInTree` with
`GraphExtractionHypotheses.ofDescended`, so callers that only need the graph/count data can keep the
honest descended residual inputs explicit and receive the produced `x₀` together with the
graph-extraction bundle. -/
@[reducible]
noncomputable def GraphExtractionHypotheses.ofDescendedInTree
    [DecidableEq (Polynomial F)] [Fintype F] (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Σ' x₀ : F,
      GraphExtractionHypotheses (F := F) (m := m) (n := n) (k := k) (Q := Q)
        (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs :=
  let hpack := Claim57ResidualsDescended.ofInTree
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ h_gs z hlead hcard hsepPt
    hS_nonempty A hA hcount hlarge
  ⟨hpack.1,
    GraphExtractionHypotheses.ofDescended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hpack.1 h_gs hpack.2 hcoincide⟩

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **Incremental-adoption bridge.**  A `Claim57ResidualsDescended` instance produces a full
`Claim57Residuals` instance under the coincidence `pg_RsetDescended = pg_Rset`.  All eight
`Claim57Residuals` fields are discharged: `hx0`/`hsep` by transporting the descended fields along the
set equality, the Johnson/largeness block verbatim, and `hfactor` by the definitionally-true
`pg_RsetDescended_hfactor` rewritten through the coincidence. -/
@[reducible]
noncomputable def Claim57Residuals.ofDescended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs where
  hx0 := by
    intro R hR
    exact hres.hx0 R (hcoincide.symm ▸ hR)
  hsep := by
    intro R hR
    exact hres.hsep R (hcoincide.symm ▸ hR)
  hS_nonempty := hres.hS_nonempty
  A := hres.A
  hA := hres.hA
  hcount := hres.hcount
  hlarge := hres.hlarge
  hfactor := by
    intro R hR
    exact pg_RsetDescended_hfactor (k := k) h_gs R (hcoincide.symm ▸ hR)

/-- **Legacy `Claim57Residuals` bridge from explicit descended in-tree inputs.**

This packages the descended in-tree constructor with `Claim57Residuals.ofDescended`, exposing the
remaining legacy bundle directly for downstream consumers being rewired away from ambient
instances.  The real residuals stay explicit: descended `hsepPt`, Johnson/count data, `hlarge`, and
the legacy coincidence hypothesis. -/
@[reducible]
noncomputable def Claim57Residuals.ofDescendedInTree
    [DecidableEq (Polynomial F)] [Fintype F] (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Σ' x₀ : F,
      Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  let hpack := Claim57ResidualsDescended.ofInTree
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ h_gs z hlead hcard hsepPt
    hS_nonempty A hA hcount hlarge
  ⟨hpack.1,
    Claim57Residuals.ofDescended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hpack.1 h_gs hpack.2 hcoincide⟩

/-- Claim 5.7 front door from the descended residual bundle.

This is the incremental-adoption form of `exists_factors_with_large_common_root_set`: callers may
work with the hfactor-free `Claim57ResidualsDescended` bundle, then provide only the explicit
coincidence hypothesis needed to satisfy legacy consumers over `pg_Rset`. -/
lemma exists_factors_with_large_common_root_set_of_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
      Irreducible H ∧ 0 < H.natDegree ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
      #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
          letI Pz := Pz z.2
          (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
          (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0}
          (@Fintype.ofFinite _ Subtype.finite))
      ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
      ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by
  letI : Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
    Claim57Residuals.ofDescended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide
  exact exists_factors_with_large_common_root_set
    (F := F) (m := m) (n := n) (k := k) (Q := Q)
    (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs

/-- Claim 5.7 front door from the explicit descended in-tree inputs.

This packages `Claim57ResidualsDescended.ofInTree` with
`exists_factors_with_large_common_root_set_of_descended`, so callers can keep the genuine descended
residual inputs explicit and consume the produced `x₀` plus Claim-5.7 factor pair directly.  The
remaining inputs are still exactly the honest residuals: the descended `hsepPt`, `hlarge`/count
data, and the explicit legacy coincidence hypothesis. -/
noncomputable def exists_factors_with_large_common_root_set_of_descended_inTree [Fintype F] (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Σ' x₀ : F,
      ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
        Irreducible H ∧ 0 < H.natDegree ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
        (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
            letI Pz := Pz z.2
            (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
            (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0}
            (@Fintype.ofFinite _ Subtype.finite))
        ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
        ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
          2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q :=
  let hpack := Claim57ResidualsDescended.ofInTree
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ h_gs z hlead hcard hsepPt
    hS_nonempty A hA hcount hlarge
  ⟨hpack.1,
    exists_factors_with_large_common_root_set_of_descended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hpack.1 h_gs hpack.2 hcoincide⟩

/-- The `R` polynomial extracted from Claim 5.7 through the descended residual bundle. -/
noncomputable def R_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) : F[Z][X][Y] :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose

/-- The `H` polynomial extracted from Claim 5.7 through the descended residual bundle. -/
noncomputable def H_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) : F[Z][X] :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose

/-- The descended-bundle `R` lies in the Eq. 5.12 factorization list. -/
lemma R_descended_mem_factorization (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide
      ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose_spec.1

/-- The descended-bundle `H` extracted from Claim 5.7 is irreducible. -/
lemma irreducible_H_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Irreducible
      (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose_spec.2.1

/-- Typeclass form of descended-bundle irreducibility for downstream Claim A.2 consumers. -/
instance fact_irreducible_H_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Fact (Irreducible
      (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)) :=
  ⟨irreducible_H_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide⟩

/-- The descended-bundle `H` extracted from Claim 5.7 has positive `Y`-degree. -/
lemma natDegree_H_descended_pos (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    0 < (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).natDegree :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose_spec.2.2.1

/-- Typeclass form of descended-bundle positive degree for downstream Claim A.2 consumers. -/
instance fact_natDegree_H_descended_pos (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Fact (0 < (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q)
      (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).natDegree) :=
  ⟨natDegree_H_descended_pos
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide⟩

/-- The descended-bundle `H` divides the `x₀`-specialization of the descended-bundle `R`. -/
lemma H_descended_dvd_evalX_R_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide ∣
      Bivariate.evalX (Polynomial.C x₀)
        (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
          (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose_spec.2.2.2.1

/-- The `x₀`-specialization of the descended-bundle `R` is separable. -/
lemma evalX_R_descended_separable (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    (Bivariate.evalX (Polynomial.C x₀)
      (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)).Separable :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose_spec.2.2.2.2.1

/-- The common-root set extracted through the descended residual bundle has the Claim 5.7
cardinality lower bound. -/
lemma commonRootSet_descended_card_ge (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z
            (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
              (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1
            (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
              (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)).eval
          (Pz.eval x₀) = 0}
        (@Fintype.ofFinite _ Subtype.finite)) ≥
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose_spec.2.2.2.2.2.1

/-- The descended Claim 5.7 extractor carries the original largeness inequality. -/
lemma claim57_largeness_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q :=
  (exists_factors_with_large_common_root_set_of_descended
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide).choose_spec.choose_spec.2.2.2.2.2.2

open BCIKS20AppendixA.ClaimA2 in
/-- Claim A.2 hypotheses for the factors extracted through the descended residual bundle. -/
lemma claimA2_hypotheses_descended (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Hypotheses x₀
      (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
      (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) :=
  ⟨H_descended_dvd_evalX_R_descended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide,
    evalX_R_descended_separable
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide⟩

open BCIKS20AppendixA.ClaimA2 in
/-- Claim A.2 hypotheses from explicit descended in-tree inputs.

This packages `Claim57ResidualsDescended.ofInTree` with `claimA2_hypotheses_descended`, retaining
the produced descended residual bundle in the dependent result because the extracted
`R_descended`/`H_descended` factors are parameterized by that bundle. -/
noncomputable def claimA2_hypotheses_descended_inTree [Fintype F] (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Σ' x₀ : F,
      Σ' hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q)
          (ωs := ωs) (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs,
        Hypotheses x₀
          (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) :=
  let hpack := Claim57ResidualsDescended.ofInTree
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ h_gs z hlead hcard hsepPt
    hS_nonempty A hA hcount hlarge
  ⟨hpack.1, hpack.2,
    claimA2_hypotheses_descended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hpack.1 h_gs hpack.2 hcoincide⟩

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.7 / Claim A.2 package from explicit descended in-tree inputs.

This is the fuller downstream package over `claimA2_hypotheses_descended_inTree`: it returns the
produced `x₀`, the exact descended residual bundle used to define `R_descended`/`H_descended`, the
Claim A.2 `Hypotheses`, and the two Claim 5.7 numeric facts for those same extracted factors.
The genuine residuals remain explicit in the input list. -/
noncomputable def claim57_descended_inTree_package [Fintype F] (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hcoincide : pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs
      = pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Σ' x₀ : F,
      Σ' hres : Claim57ResidualsDescended (F := F) (m := m) (n := n) (Q := Q)
          (ωs := ωs) (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs,
        Hypotheses x₀
          (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)
          (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
            (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) ∧
        #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
            letI Pz := Pz z.2
            (Trivariate.eval_on_Z
                (R_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
                  (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide) z.1).eval Pz = 0 ∧
            (Bivariate.evalX z.1
                (H_descended (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
                  (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hres hcoincide)).eval
              (Pz.eval x₀) = 0}
            (@Fintype.ofFinite _ Subtype.finite)) ≥
          #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) ∧
        #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
          2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q :=
  let hpack := Claim57ResidualsDescended.ofInTree
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ h_gs z hlead hcard hsepPt
    hS_nonempty A hA hcount hlarge
  ⟨hpack.1, hpack.2,
    claimA2_hypotheses_descended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hpack.1 h_gs hpack.2 hcoincide,
    commonRootSet_descended_card_ge
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hpack.1 h_gs hpack.2 hcoincide,
    claim57_largeness_descended
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hpack.1 h_gs hpack.2 hcoincide⟩

/-! ### Axiom audit (issue #8 descended Claim 5.7 adoption surface) -/

#print axioms ProximityGap.GraphExtractionHypotheses.ofDescended
#print axioms ProximityGap.GraphExtractionHypotheses.ofDescendedInTree
#print axioms ProximityGap.Claim57Residuals.ofDescended
#print axioms ProximityGap.Claim57Residuals.ofDescendedInTree
#print axioms ProximityGap.exists_factors_with_large_common_root_set_of_descended
#print axioms ProximityGap.exists_factors_with_large_common_root_set_of_descended_inTree
#print axioms ProximityGap.R_descended
#print axioms ProximityGap.H_descended
#print axioms ProximityGap.fact_irreducible_H_descended
#print axioms ProximityGap.fact_natDegree_H_descended_pos
#print axioms ProximityGap.commonRootSet_descended_card_ge
#print axioms ProximityGap.claim57_largeness_descended
#print axioms ProximityGap.claimA2_hypotheses_descended
#print axioms ProximityGap.claimA2_hypotheses_descended_inTree
#print axioms ProximityGap.claim57_descended_inTree_package

end ProximityGap
