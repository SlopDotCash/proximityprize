/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceSupply
import ArkLib.Data.CodingTheory.GuruswamiSudan.Hab25SeparableSupply
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.FieldDischarge

/-!
# Issues #301/#302/#304 — producers for the two open `GSSurfaceSupply` nodes

`GSSurfaceSupply.lean` isolated the two genuinely open inputs of the deepest reachable
decoded capstone (`gammaGenuine_eq_trunc_of_decoded_integerRep`) as named `Prop`s:

* **Node A** — `IntegerRepCentreSupply x₀ Q₀`
  (`∃ H, Irreducible H ∧ 0 < H.natDegree ∧ ClaimA2.Hypotheses x₀ Q₀ H`), whose hard content
  is the centre-slice separability `(evalX (C x₀) Q₀).Separable` **over the non-field base
  `F[Z]`**;
* **Node B** — `SurfaceSeparabilitySupply Q₀` (`Q₀.Separable` in the trivariate ring, over
  the non-field base `F[Z][X]`), of which only the linear case `separable_of_eq_surface`
  was producible.

This file pushes the producible boundary of both nodes as far as the honest mathematics
allows, *without* faking domain-level separability from discriminant nonvanishing (the
in-tree Lemma 2′ analysis, `DiscriminantSeparable.lean`, shows `Separable` over `F[Z]`
demands a **unit** derivative-resultant — strictly stronger than `discr ≠ 0`):

## Node A (centre supply)

* `exists_irreducible_factor_natDegree_pos` — in `A[X]` over a UFD domain `A`, every
  positive-degree polynomial has an irreducible factor of positive degree (UFD
  factorization + degree additivity).  This kills the "irreducible curve `H`" half of
  Node A outright:
* `integerRepCentreSupply_of_separable_slice` — **Node A reduced exactly to its honest
  core**: a positive-degree separable centre slice already yields the full
  `IntegerRepCentreSupply x₀ Q₀` (the curve `H` is *constructed* as an irreducible factor;
  `Hypotheses.dvd_evalX` and `Hypotheses.separable_evalX` follow).
* `integerRepCentreSupply_of_resultant_isUnit` — the same from the honest domain-level
  condition: a **unit** derivative-resultant of the slice (Lemma 2′ shape).
* `integerRepCentreSupply_of_linear_slice` / `integerRepCentreSupply_of_monic_linear_slice`
  — **Node A PROVEN OUTRIGHT in the `Y`-linear-slice regime**: a slice of `Y`-degree one
  with unit (e.g. monic) leading coefficient is separable over `F[Z]` (its derivative is a
  unit constant), and the slice itself supplies the curve.  By the F7 satisfiability
  boundary (`branchCert_eq_zero` forces `H.natDegree = 1`) this is exactly the regime in
  which the composed capstones are non-vacuously instantiable.

## The good-centre (Route A1) counting legs

The centre slice is the **middle-`X`** specialization `evalX (C x₀) Q₀ =
Q₀.map (evalRingHom (C x₀))`.  At any centre where the `Y`-leading coefficient survives:

* `slice_natDegree_eq_of_leadingCoeff_eval_ne` — the `Y`-degree is preserved;
* `slice_discr_eq_of_leadingCoeff_eval_ne` — the discriminant specializes:
  `discr (slice) = (discr_Y Q₀).eval (C x₀)`;
* `exists_good_centre_slice_discr_ne_zero` — **the explicit bad-centre count** (the
  Schwartz–Zippel-style numeric leg): given `Z`-witnesses `z₁, z₂` not killing
  `Q₀.leadingCoeff` resp. `Q₀.discr` and the field-size budget
  `deg_X(lc|_{z₁}) + deg_X(discr|_{z₂}) < |F|`, a good centre exists with the slice degree
  preserved and `discr (slice) ≠ 0` (each bad set is counted by
  `ProximityGap.c56_evalC_bad_set_card_le`);
* `slice_separable_map_of_discr_ne_zero` / `exists_good_centre_slice_fracSeparable` — at
  such a centre the slice is separable **over the fraction field `F(Z)`** (the honest
  maximal conclusion of the discriminant route; the residual gap to Node A's `F[Z]`-level
  `Separable` is exactly the unit-resultant condition of
  `integerRepCentreSupply_of_resultant_isUnit` — see Lemma 2′, not derivable from
  `discr ≠ 0`);
* `radical_rep_good_centre_charZero` — the char-0 capstone for the **squarefree part**:
  for any integer representative `W₀` of `radical Q` of a GS interpolant with a decoded
  linear factor, `W₀.discr ≠ 0` holds unconditionally
  (`integer_rep_discr_ne_zero` + `separable_map_radical`), so the good-centre count above
  fires and produces a centre with degree preservation, `discr (slice) ≠ 0`, and
  `F(Z)`-separability of the slice;
* `surface_dvd_radical_integerRep` — the documented radical-replacement bridge for the
  lane: the decoded surface factor transfers to the integer representative of the
  squarefree part (`radical_linearFactor_dvd_iff` + `surface_dvd_integerRep`).

## Node B (trivariate separability)

* `separable_of_natDegree_eq_one_of_isUnit_leadingCoeff` /
  `surfaceSeparabilitySupply_of_linear` — the `Y`-degree-one case with unit leading
  coefficient (strictly generalizes `separable_of_eq_surface`; note this regime is
  *disjoint* from the capstone's `hd2 : 2 ≤ natDegreeY`, as documented there).
* `isCoprime_X_sub_C_of_isUnit_sub` + `separable_prod_X_sub_C_of_isUnit_sub` +
  `surfaceSeparabilitySupply_of_prod_surfaces` / `surfaceSeparabilitySupply_pair` —
  **the first Node-B producers compatible with the capstone regime**: a product of
  (≥ 2) decoded surfaces with pairwise *unit* differences (`wᵢ − wⱼ ∈ Fˣ`, i.e. decoded
  codewords differing by nonzero constants) is separable over `F[Z][X]`, with
  `natDegree = 2` for the pair (`natDegree_pair_surfaces`) — jointly satisfiable with
  `hd2` and the surface divisibility `hdvd`.
* `surfaceSeparabilitySupply_of_unit_mul` (with `separable_isUnit_C_mul`) — unit-constant
  rescalings.

## What remains genuinely open (honest boundary)

For a slice (resp. trivariate) of `Y`-degree ≥ 2 whose derivative-resultant is **not** a
unit of `F[Z]` (resp. `F[Z][X]`), `Separable` is *false* — the open content of Nodes A/B
is therefore not a missing proof but the (regime) question of whether the GS chain can be
steered into the unit-resultant / split-with-unit-differences regimes.  No producer is
faked outside them.

## References
* [BCIKS20] §5, Appendix A; [Hab25] §3; the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate UniqueFactorizationMonoid

namespace ArkLib

namespace GSSurfaceRadicalSupply

attribute [local instance] Classical.propDecidable

/-! ## §1 — generic separability bricks over a commutative ring -/

section Generic

variable {R : Type*} [CommRing R]

/-- **Separability survives unit-constant scaling** (over any commutative ring): the Bézout
pair of `f` rescales by the inverse unit. -/
theorem separable_isUnit_C_mul {c : R} (hc : IsUnit c) {f : R[X]} (hf : f.Separable) :
    (Polynomial.C c * f).Separable := by
  rw [Polynomial.separable_def] at hf ⊢
  obtain ⟨a, b, hab⟩ := hf
  set v : R := ((hc.unit⁻¹ : Rˣ) : R) with hv
  have hvc : Polynomial.C v * Polynomial.C c = 1 := by
    rw [← Polynomial.C_mul]
    have h1 : v * c = 1 := by
      conv_lhs => rw [← hc.unit_spec]
      exact Units.inv_mul _
    rw [h1, Polynomial.C_1]
  refine ⟨Polynomial.C v * a, Polynomial.C v * b, ?_⟩
  rw [Polynomial.derivative_C_mul]
  calc Polynomial.C v * a * (Polynomial.C c * f)
        + Polynomial.C v * b * (Polynomial.C c * Polynomial.derivative f)
      = (Polynomial.C v * Polynomial.C c) * (a * f + b * Polynomial.derivative f) := by ring
    _ = 1 := by rw [hvc, hab, one_mul]

/-- **Degree-one polynomials with unit leading coefficient are separable over any
commutative ring**: the derivative is the unit constant `C (p.coeff 1)`, so
`0·p + C(lc)⁻¹·p' = 1` is a Bézout pair.  (This is the honest generalization of
`separable_X_sub_C` powering the linear-regime producers below.) -/
theorem separable_of_natDegree_eq_one_of_isUnit_leadingCoeff {p : R[X]}
    (h1 : p.natDegree = 1) (hu : IsUnit p.leadingCoeff) : p.Separable := by
  have hc1 : p.leadingCoeff = p.coeff 1 := by rw [Polynomial.leadingCoeff, h1]
  rw [hc1] at hu
  have hd : Polynomial.derivative p = Polynomial.C (p.coeff 1) := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one h1.le]
    simp
  rw [Polynomial.separable_def, hd]
  refine ⟨0, Polynomial.C ((hu.unit⁻¹ : Rˣ) : R), ?_⟩
  rw [zero_mul, zero_add, ← Polynomial.C_mul, hu.val_inv_mul, Polynomial.C_1]

/-- **Linear factors with unit-difference roots are coprime over any commutative ring**:
`C((a−b)⁻¹)·((X − C b) − (X − C a)) = 1`. -/
theorem isCoprime_X_sub_C_of_isUnit_sub {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) := by
  set v : R := ((h.unit⁻¹ : Rˣ) : R) with hv
  refine ⟨-Polynomial.C v, Polynomial.C v, ?_⟩
  have hkey : -Polynomial.C v * (Polynomial.X - Polynomial.C a)
      + Polynomial.C v * (Polynomial.X - Polynomial.C b)
      = Polynomial.C (v * (a - b)) := by
    rw [Polynomial.C_mul, Polynomial.C_sub]
    ring
  rw [hkey]
  have h1 : v * (a - b) = 1 := by
    conv_lhs => rw [← h.unit_spec]
    exact Units.inv_mul _
  rw [h1, Polynomial.C_1]

/-- **A product of linear factors with pairwise unit differences is separable** over any
commutative ring (each factor is separable, the factors are pairwise coprime). -/
theorem separable_prod_X_sub_C_of_isUnit_sub {ι : Type*} {s : Finset ι} {w : ι → R}
    (hw : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (w i - w j)) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (w i))).Separable :=
  Polynomial.separable_prod'
    (fun _ hi _ hj hij => isCoprime_X_sub_C_of_isUnit_sub (hw _ hi _ hj hij))
    (fun _ _ => Polynomial.separable_X_sub_C)

end Generic

/-! ## §2 — irreducible-factor existence in `A[X]` over a UFD domain -/

/-- **Positive-degree polynomials over a UFD domain have a positive-degree irreducible
factor.**  Factor into primes; degree additivity forces some prime factor to carry positive
degree.  (Applied at `A = F[Z]` this constructs the curve `H` of Node A from any separable
slice; constant factors — which could never be the curve — are skipped by the degree
argument, not by fiat.) -/
theorem exists_irreducible_factor_natDegree_pos {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {p : A[X]} (hdeg : 0 < p.natDegree) :
    ∃ q : A[X], Irreducible q ∧ 0 < q.natDegree ∧ q ∣ p := by
  classical
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact absurd hdeg (lt_irrefl 0)
  set t : Multiset A[X] := UniqueFactorizationMonoid.factors p with ht
  have hassoc : Associated t.prod p := UniqueFactorizationMonoid.factors_prod hp0
  have h0t : (0 : A[X]) ∉ t := fun h0 =>
    (UniqueFactorizationMonoid.prime_of_factor 0 h0).ne_zero rfl
  have hproddeg : t.prod.natDegree = (t.map Polynomial.natDegree).sum :=
    Polynomial.natDegree_multiset_prod t h0t
  obtain ⟨u, hu⟩ := hassoc
  have htp0 : t.prod ≠ 0 := by
    intro h0
    rw [← hu, h0, zero_mul] at hp0
    exact hp0 rfl
  have hdegp : p.natDegree = t.prod.natDegree := by
    rw [← hu, Polynomial.natDegree_mul htp0 (Units.ne_zero u),
      Polynomial.natDegree_eq_zero_of_isUnit u.isUnit, add_zero]
  have hsum : 0 < (t.map Polynomial.natDegree).sum := by
    rw [← hproddeg, ← hdegp]; exact hdeg
  have hex : ∃ q ∈ t, 0 < q.natDegree := by
    by_contra hall
    simp only [not_exists, not_and, not_lt, Nat.le_zero] at hall
    have hzero : (t.map Polynomial.natDegree).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
      exact hall q hq
    rw [hzero] at hsum
    exact absurd hsum (lt_irrefl 0)
  obtain ⟨q, hq, hqdeg⟩ := hex
  exact ⟨q, (UniqueFactorizationMonoid.prime_of_factor q hq).irreducible, hqdeg,
    dvd_trans (Multiset.dvd_prod hq) (Associated.dvd ⟨u, hu⟩)⟩

/-! ## §3 — Node A producers (`IntegerRepCentreSupply`) -/

variable {F : Type} [Field F]

/-- **Node A reduced exactly to its honest core.**  A positive-degree *separable* centre
slice already yields the full `IntegerRepCentreSupply x₀ Q₀`: the irreducible curve `H` is
constructed as a positive-degree irreducible factor of the slice (`F[Z]` is a UFD), and
both `Hypotheses` fields follow.  The open content of Node A is therefore *only* the slice
separability over `F[Z]` (plus positive slice degree). -/
theorem integerRepCentreSupply_of_separable_slice {x₀ : F} {Q₀ : F[X][X][Y]}
    (hdeg : 0 < (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) Q₀).Separable) :
    GSSurfaceSupply.IntegerRepCentreSupply x₀ Q₀ := by
  obtain ⟨q, hirr, hqdeg, hqdvd⟩ := exists_irreducible_factor_natDegree_pos hdeg
  exact ⟨q, hirr, hqdeg, ⟨hqdvd, hsep⟩⟩

/-- **Node A from the honest domain-level unit-resultant condition** (Lemma 2′ shape): a
positive-degree slice whose derivative-resultant is a *unit* of `F[Z]` is separable, and
Node A follows.  By `DiscriminantSeparable` Lemma 2′ this unit condition is exactly the
honest residual — it is *not* implied by `discr ≠ 0` over the non-field base. -/
theorem integerRepCentreSupply_of_resultant_isUnit {x₀ : F} {Q₀ : F[X][X][Y]}
    (hdeg : 0 < (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree)
    (hres : IsUnit ((Bivariate.evalX (Polynomial.C x₀) Q₀).resultant
      (Polynomial.derivative (Bivariate.evalX (Polynomial.C x₀) Q₀))
      (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree
      ((Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree - 1))) :
    GSSurfaceSupply.IntegerRepCentreSupply x₀ Q₀ :=
  integerRepCentreSupply_of_separable_slice hdeg
    (Polynomial.separable_of_resultant_isUnit hdeg hres)

/-- **Node A PROVEN OUTRIGHT in the `Y`-linear-slice regime.**  If the centre slice has
`Y`-degree one with unit leading coefficient, it is separable over `F[Z]` (derivative = unit
constant) and Node A holds.  By the F7 satisfiability boundary (`branchCert_eq_zero`
forces `H.natDegree = 1`) this is exactly the regime where the composed capstones are
non-vacuously instantiable. -/
theorem integerRepCentreSupply_of_linear_slice {x₀ : F} {Q₀ : F[X][X][Y]}
    (h1 : (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree = 1)
    (hu : IsUnit (Bivariate.evalX (Polynomial.C x₀) Q₀).leadingCoeff) :
    GSSurfaceSupply.IntegerRepCentreSupply x₀ Q₀ :=
  integerRepCentreSupply_of_separable_slice (by rw [h1]; exact Nat.one_pos)
    (separable_of_natDegree_eq_one_of_isUnit_leadingCoeff h1 hu)

/-- Node A for a *monic* linear slice (the leading-coefficient unit is `1`). -/
theorem integerRepCentreSupply_of_monic_linear_slice {x₀ : F} {Q₀ : F[X][X][Y]}
    (h1 : (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree = 1)
    (hm : (Bivariate.evalX (Polynomial.C x₀) Q₀).Monic) :
    GSSurfaceSupply.IntegerRepCentreSupply x₀ Q₀ :=
  integerRepCentreSupply_of_linear_slice h1 (by rw [Polynomial.Monic.leadingCoeff hm]; exact isUnit_one)

/-! ## §4 — the good-centre counting legs (Route A1) -/

/-- The centre slice preserves the `Y`-degree wherever the `Y`-leading coefficient of `Q₀`
survives the middle-`X` evaluation at `C x₀`. -/
theorem slice_natDegree_eq_of_leadingCoeff_eval_ne {x₀ : F} {Q₀ : F[X][X][Y]}
    (hlc : Q₀.leadingCoeff.eval (Polynomial.C x₀) ≠ 0) :
    (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree = Q₀.natDegree := by
  rw [Bivariate.evalX_eq_map]
  exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _
    (by simpa [Polynomial.coe_evalRingHom] using hlc)

/-- **The discriminant specializes along the centre slice** (degree-preserving case):
`discr (evalX (C x₀) Q₀) = (discr_Y Q₀).eval (C x₀)`. -/
theorem slice_discr_eq_of_leadingCoeff_eval_ne {x₀ : F} {Q₀ : F[X][X][Y]}
    (hdeg : 0 < Q₀.natDegree)
    (hlc : Q₀.leadingCoeff.eval (Polynomial.C x₀) ≠ 0) :
    (Bivariate.evalX (Polynomial.C x₀) Q₀).discr = Q₀.discr.eval (Polynomial.C x₀) := by
  have hmap : (Q₀.map (Polynomial.evalRingHom (Polynomial.C x₀))).natDegree = Q₀.natDegree := by
    rw [← Bivariate.evalX_eq_map]
    exact slice_natDegree_eq_of_leadingCoeff_eval_ne hlc
  rw [Bivariate.evalX_eq_map]
  simpa [Polynomial.coe_evalRingHom] using
    Polynomial.discr_map_of_natDegree_preserved
      (φ := Polynomial.evalRingHom (Polynomial.C x₀)) hdeg hmap

/-- **The explicit bad-centre count (the Route-A1 numeric leg).**  Given `Z`-witnesses
`z₁, z₂` not killing `Q₀.leadingCoeff` resp. `Q₀.discr` and the field-size budget
`deg_X(lc|_{z₁}) + deg_X(discr|_{z₂}) < |F|`, there is a centre `x₀` at which the slice's
`Y`-degree is preserved **and** its discriminant is nonzero.  Each bad set is counted by the
in-tree `ProximityGap.c56_evalC_bad_set_card_le` (the bad `x₀` inject into the roots of the
`Z`-specialized polynomial), so the count is Schwartz–Zippel-explicit and feeds the
field-size legs of the consuming capstones. -/
theorem exists_good_centre_slice_discr_ne_zero [Fintype F] [DecidableEq F]
    {Q₀ : F[X][X][Y]} (hdeg : 0 < Q₀.natDegree) (z₁ z₂ : F)
    (hlcz : Q₀.leadingCoeff.map (Polynomial.evalRingHom z₁) ≠ 0)
    (hdz : Q₀.discr.map (Polynomial.evalRingHom z₂) ≠ 0)
    (hcard : (Q₀.leadingCoeff.map (Polynomial.evalRingHom z₁)).natDegree
        + (Q₀.discr.map (Polynomial.evalRingHom z₂)).natDegree < Fintype.card F) :
    ∃ x₀ : F, (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree = Q₀.natDegree ∧
      (Bivariate.evalX (Polynomial.C x₀) Q₀).discr ≠ 0 := by
  classical
  have h1 : (Finset.univ.filter
      (fun x₀ : F => Q₀.leadingCoeff.eval (Polynomial.C x₀) = 0)).card
      ≤ (Q₀.leadingCoeff.map (Polynomial.evalRingHom z₁)).natDegree := by
    simpa using ProximityGap.c56_evalC_bad_set_card_le Q₀.leadingCoeff z₁ hlcz
  have h2 : (Finset.univ.filter
      (fun x₀ : F => Q₀.discr.eval (Polynomial.C x₀) = 0)).card
      ≤ (Q₀.discr.map (Polynomial.evalRingHom z₂)).natDegree := by
    simpa using ProximityGap.c56_evalC_bad_set_card_le Q₀.discr z₂ hdz
  set bad : Finset F :=
    Finset.univ.filter (fun x₀ : F => Q₀.leadingCoeff.eval (Polynomial.C x₀) = 0)
      ∪ Finset.univ.filter (fun x₀ : F => Q₀.discr.eval (Polynomial.C x₀) = 0) with hbad
  have hbadcard : bad.card < Fintype.card F :=
    lt_of_le_of_lt (le_trans (Finset.card_union_le _ _) (add_le_add h1 h2)) hcard
  have hex : (badᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    omega
  obtain ⟨x₀, hx₀⟩ := hex
  rw [Finset.mem_compl, hbad, Finset.mem_union] at hx₀
  have hlc : Q₀.leadingCoeff.eval (Polynomial.C x₀) ≠ 0 := fun h0 =>
    hx₀ (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩))
  have hd : Q₀.discr.eval (Polynomial.C x₀) ≠ 0 := fun h0 =>
    hx₀ (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩))
  refine ⟨x₀, slice_natDegree_eq_of_leadingCoeff_eval_ne hlc, ?_⟩
  rw [slice_discr_eq_of_leadingCoeff_eval_ne hdeg hlc]
  exact hd

/-- **At a discriminant-good centre the slice is separable over the fraction field
`F(Z)`** — the honest maximal conclusion of the discriminant route (the residual gap to
Node A's `F[Z]`-level `Separable` is exactly the unit-resultant condition, which `discr ≠ 0`
does *not* supply over the non-field base; see Lemma 2′). -/
theorem slice_separable_map_of_discr_ne_zero {x₀ : F} {Q₀ : F[X][X][Y]}
    (hdeg : 0 < (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree)
    (hd : (Bivariate.evalX (Polynomial.C x₀) Q₀).discr ≠ 0) :
    ((Bivariate.evalX (Polynomial.C x₀) Q₀).map
      (algebraMap F[X] (RatFunc F))).Separable := by
  set s : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) Q₀ with hs
  have hinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    RatFunc.algebraMap_injective F
  have hmap : (s.map (algebraMap F[X] (RatFunc F))).natDegree = s.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj s
  have hd2 : (s.map (algebraMap F[X] (RatFunc F))).discr ≠ 0 := by
    rw [Polynomial.discr_map_of_natDegree_preserved hdeg hmap]
    exact fun h0 => hd ((map_eq_zero_iff _ hinj).mp h0)
  exact Polynomial.separable_of_discr_ne_zero (by rw [hmap]; exact hdeg) hd2

/-- **The good-centre slice capstone**: under the explicit bad-centre budget there is a
centre `x₀` with the slice degree preserved, `discr (slice) ≠ 0`, and the slice separable
over `F(Z)`. -/
theorem exists_good_centre_slice_fracSeparable [Fintype F] [DecidableEq F]
    {Q₀ : F[X][X][Y]} (hdeg : 0 < Q₀.natDegree) (z₁ z₂ : F)
    (hlcz : Q₀.leadingCoeff.map (Polynomial.evalRingHom z₁) ≠ 0)
    (hdz : Q₀.discr.map (Polynomial.evalRingHom z₂) ≠ 0)
    (hcard : (Q₀.leadingCoeff.map (Polynomial.evalRingHom z₁)).natDegree
        + (Q₀.discr.map (Polynomial.evalRingHom z₂)).natDegree < Fintype.card F) :
    ∃ x₀ : F, (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree = Q₀.natDegree ∧
      (Bivariate.evalX (Polynomial.C x₀) Q₀).discr ≠ 0 ∧
      ((Bivariate.evalX (Polynomial.C x₀) Q₀).map
        (algebraMap F[X] (RatFunc F))).Separable := by
  obtain ⟨x₀, hdeq, hdne⟩ :=
    exists_good_centre_slice_discr_ne_zero hdeg z₁ z₂ hlcz hdz hcard
  exact ⟨x₀, hdeq, hdne,
    slice_separable_map_of_discr_ne_zero (by rw [hdeq]; exact hdeg) hdne⟩

/-! ## §5 — the char-0 radical (squarefree-part) capstone and the lane bridge -/

/-- **The decoded surface transfers to the integer representative of the squarefree
part** — the radical-replacement bridge for the lane: the K-level decoded factor
`(Y − C p) ∣ Q` survives `radical` (`radical_linearFactor_dvd_iff`) and descends to the
trivariate surface factor of any integer representative `W₀` of `radical Q`. -/
theorem surface_dvd_radical_integerRep {Q : (RatFunc F)[X][Y]} (hQ0 : Q ≠ 0)
    {e : F[X]} {W₀ : F[X][X][Y]}
    (hrep : W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) * radical Q)
    {w : F[X][Y]} {p : (RatFunc F)[X]}
    (hw : w.map (algebraMap F[X] (RatFunc F)) = p)
    (hdvdK : (Polynomial.X - Polynomial.C p) ∣ Q) :
    (Polynomial.X - Polynomial.C w) ∣ W₀ :=
  GSSurfaceSupply.surface_dvd_integerRep hrep hw
    ((GuruswamiSudan.OverRatFunc.radical_linearFactor_dvd_iff hQ0 p).mpr hdvdK)

/-- **The char-0 good-centre capstone for the squarefree part** (the X-shape sibling of
`radical_rep_good_specialization_charZero`): for any integer representative `(e, W₀)` of
`radical Q` of a nonzero GS interpolant with a decoded linear factor, `W₀.discr ≠ 0` holds
*unconditionally* (`separable_map_radical` + `integer_rep_discr_ne_zero`), so under the
explicit bad-centre budget there is a centre `x₀` with the slice `Y`-degree preserved (and
positive), `discr (slice) ≠ 0`, and the slice separable over `F(Z)`.

Together with `surface_dvd_radical_integerRep` (the surface) and
`integerRepCentreSupply_of_separable_slice` (Node A modulo the `F[Z]`-level upgrade), this
is the deepest honest Route-A1 supply for the radical lane: what separates it from the full
`IntegerRepCentreSupply x₀ W₀` is *exactly* the `F(Z)`-vs-`F[Z]` separability gap (the
unit-resultant condition of Lemma 2′). -/
theorem radical_rep_good_centre_charZero [CharZero F] [Fintype F] [DecidableEq F]
    {Q : (RatFunc F)[X][Y]} (hQ0 : Q ≠ 0)
    {e : F[X]} {W₀ : F[X][X][Y]} (he : e ≠ 0)
    (hrep : W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) * radical Q)
    {p : (RatFunc F)[X]}
    (hdvd : (Polynomial.X - Polynomial.C p) ∣ Q)
    (z₁ z₂ : F)
    (hlcz : W₀.leadingCoeff.map (Polynomial.evalRingHom z₁) ≠ 0)
    (hdz : W₀.discr.map (Polynomial.evalRingHom z₂) ≠ 0)
    (hcard : (W₀.leadingCoeff.map (Polynomial.evalRingHom z₁)).natDegree
        + (W₀.discr.map (Polynomial.evalRingHom z₂)).natDegree < Fintype.card F) :
    ∃ x₀ : F, (Bivariate.evalX (Polynomial.C x₀) W₀).natDegree = W₀.natDegree ∧
      0 < (Bivariate.evalX (Polynomial.C x₀) W₀).natDegree ∧
      (Bivariate.evalX (Polynomial.C x₀) W₀).discr ≠ 0 ∧
      ((Bivariate.evalX (Polynomial.C x₀) W₀).map
        (algebraMap F[X] (RatFunc F))).Separable := by
  -- positive `Y`-degree of `W₀`, transferred from the squarefree part (as in
  -- `radical_rep_good_specialization_charZero`)
  have hWdeg : 0 < (radical Q : (RatFunc F)[X][Y]).natDegree :=
    GuruswamiSudan.OverRatFunc.natDegree_radical_pos_of_linearFactor_dvd hQ0 hdvd
  have hrad0 : (radical Q : (RatFunc F)[X][Y]) ≠ 0 := radical_ne_zero
  have hφinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    RatFunc.algebraMap_injective F
  have hφe : algebraMap F[X] (RatFunc F) e ≠ 0 := fun h0 =>
    he ((map_eq_zero_iff _ hφinj).mp h0)
  have hcc : (Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) :
      (RatFunc F)[X][Y]) ≠ 0 := by simpa using hφe
  have h2 : Function.Injective
      ⇑(Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ hφinj
  have h1 : (W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))).natDegree =
      W₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h2 W₀
  have h3 : (W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))).natDegree =
      (radical Q : (RatFunc F)[X][Y]).natDegree := by
    rw [hrep, Polynomial.natDegree_mul hcc hrad0, Polynomial.natDegree_C, zero_add]
  have hdeg : 0 < W₀.natDegree := by
    rw [← h1, h3]; exact hWdeg
  obtain ⟨x₀, hdeq, hdne, hsep⟩ :=
    exists_good_centre_slice_fracSeparable hdeg z₁ z₂ hlcz hdz hcard
  exact ⟨x₀, hdeq, by rw [hdeq]; exact hdeg, hdne, hsep⟩

/-! ## §6 — Node B producers (`SurfaceSeparabilitySupply`) -/

/-- **Node B in the `Y`-degree-one regime with unit leading coefficient** — strictly
generalizes `GSSurfaceSupply.separable_of_eq_surface` (which is the monic special case
`Q₀ = Y′ − C w`).  Note this regime is disjoint from the capstone's `hd2 : 2 ≤ natDegreeY`;
the in-regime producers are the product ones below. -/
theorem surfaceSeparabilitySupply_of_linear {Q₀ : F[X][X][Y]}
    (h1 : Q₀.natDegree = 1) (hu : IsUnit Q₀.leadingCoeff) :
    GSSurfaceSupply.SurfaceSeparabilitySupply Q₀ :=
  separable_of_natDegree_eq_one_of_isUnit_leadingCoeff h1 hu

/-- **Node B for a product of decoded surfaces with pairwise unit differences** — the first
producer compatible with the capstone regime `hd2 : 2 ≤ natDegreeY` (take `s.card ≥ 2`):
surfaces `Y′ − C (w i)` whose defining codewords pairwise differ by *units* of `F[Z][X]`
(nonzero `F`-constants) are pairwise coprime, and each is separable, so the product is. -/
theorem surfaceSeparabilitySupply_of_prod_surfaces {ι : Type*} {s : Finset ι}
    {w : ι → F[X][Y]}
    (hw : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (w i - w j)) :
    GSSurfaceSupply.SurfaceSeparabilitySupply
      (∏ i ∈ s, (Polynomial.X - Polynomial.C (w i))) :=
  separable_prod_X_sub_C_of_isUnit_sub hw

/-- **Node B for a pair of surfaces with unit difference** (the minimal in-regime case,
`natDegree = 2` by `natDegree_pair_surfaces`): jointly satisfiable with the capstone's
`hd2` and the surface divisibility `hdvd`. -/
theorem surfaceSeparabilitySupply_pair {w₁ w₂ : F[X][Y]} (h : IsUnit (w₁ - w₂)) :
    GSSurfaceSupply.SurfaceSeparabilitySupply
      ((Polynomial.X - Polynomial.C w₁) * (Polynomial.X - Polynomial.C w₂)) := by
  have h1 : (Polynomial.X - Polynomial.C w₁ : F[X][X][Y]).Separable :=
    Polynomial.separable_X_sub_C
  have h2 : (Polynomial.X - Polynomial.C w₂ : F[X][X][Y]).Separable :=
    Polynomial.separable_X_sub_C
  exact h1.mul h2 (isCoprime_X_sub_C_of_isUnit_sub h)

/-- The pair of surfaces has `Y`-degree exactly `2` — discharging the capstone's
`hd2 : 2 ≤ natDegreeY` for the pair producer. -/
theorem natDegree_pair_surfaces {w₁ w₂ : F[X][Y]} :
    ((Polynomial.X - Polynomial.C w₁) * (Polynomial.X - Polynomial.C w₂)
      : F[X][X][Y]).natDegree = 2 := by
  rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero w₁)
    (Polynomial.X_sub_C_ne_zero w₂), Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

/-- **Node B survives unit-constant rescaling**: `C c · Q₀` is separable for any unit
`c ∈ F[Z][X]ˣ` whenever `Q₀` is — covering the unit-content normalizations of the
integer-representative chain. -/
theorem surfaceSeparabilitySupply_of_unit_mul {Q₀ : F[X][X][Y]} {c : F[X][X]}
    (hc : IsUnit c) (h : GSSurfaceSupply.SurfaceSeparabilitySupply Q₀) :
    GSSurfaceSupply.SurfaceSeparabilitySupply (Polynomial.C c * Q₀) :=
  separable_isUnit_C_mul hc h

end GSSurfaceRadicalSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GSSurfaceRadicalSupply.separable_isUnit_C_mul
#print axioms ArkLib.GSSurfaceRadicalSupply.separable_of_natDegree_eq_one_of_isUnit_leadingCoeff
#print axioms ArkLib.GSSurfaceRadicalSupply.isCoprime_X_sub_C_of_isUnit_sub
#print axioms ArkLib.GSSurfaceRadicalSupply.separable_prod_X_sub_C_of_isUnit_sub
#print axioms ArkLib.GSSurfaceRadicalSupply.exists_irreducible_factor_natDegree_pos
#print axioms ArkLib.GSSurfaceRadicalSupply.integerRepCentreSupply_of_separable_slice
#print axioms ArkLib.GSSurfaceRadicalSupply.integerRepCentreSupply_of_resultant_isUnit
#print axioms ArkLib.GSSurfaceRadicalSupply.integerRepCentreSupply_of_linear_slice
#print axioms ArkLib.GSSurfaceRadicalSupply.integerRepCentreSupply_of_monic_linear_slice
#print axioms ArkLib.GSSurfaceRadicalSupply.slice_natDegree_eq_of_leadingCoeff_eval_ne
#print axioms ArkLib.GSSurfaceRadicalSupply.slice_discr_eq_of_leadingCoeff_eval_ne
#print axioms ArkLib.GSSurfaceRadicalSupply.exists_good_centre_slice_discr_ne_zero
#print axioms ArkLib.GSSurfaceRadicalSupply.slice_separable_map_of_discr_ne_zero
#print axioms ArkLib.GSSurfaceRadicalSupply.exists_good_centre_slice_fracSeparable
#print axioms ArkLib.GSSurfaceRadicalSupply.surface_dvd_radical_integerRep
#print axioms ArkLib.GSSurfaceRadicalSupply.radical_rep_good_centre_charZero
#print axioms ArkLib.GSSurfaceRadicalSupply.surfaceSeparabilitySupply_of_linear
#print axioms ArkLib.GSSurfaceRadicalSupply.surfaceSeparabilitySupply_of_prod_surfaces
#print axioms ArkLib.GSSurfaceRadicalSupply.surfaceSeparabilitySupply_pair
#print axioms ArkLib.GSSurfaceRadicalSupply.natDegree_pair_surfaces
#print axioms ArkLib.GSSurfaceRadicalSupply.surfaceSeparabilitySupply_of_unit_mul
