/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import CompPoly.Data.MvPolynomial.Notation
import CompPoly.Univariate.Lagrange
import CompPoly.Univariate.ToPoly.Impl

/-!
# Quotienting for STIR

This file develops the polynomial quotienting machinery used by STIR.

* `Quotienting.ansPoly` — the unique interpolating polynomial of degree `< |S|` through a given
  answer function `Ans : S → F`.
* `Quotienting.vanishingPoly` — the vanishing polynomial `∏ s ∈ S, (X - s)` on a finset `S`.
* `vanishingPoly_eval_eq_zero` / `vanishingPoly_eval_ne_zero` — the vanishing polynomial is zero
  exactly on the points of `S`.
-/

open Polynomial NNReal ReedSolomon ListDecodable Code

namespace Quotienting

variable {n : ℕ}
         {F : Type*} [Field F] [DecidableEq F]
         {ι : Finset F}

/-- Let `Ans : S → F`, `ansPoly(Ans, S)` is the unique interpolating polynomial of degree < |S|
    with `AnsPoly(s) = Ans(s)` for each s ∈ S.

    Note: For S=∅ we get Ans'(x) = 0 (the zero polynomial) -/
noncomputable def ansPoly (S : Finset F) (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
    that is 0 at each s ∈ S and is not the zero polynomial. That is V(X) = ∏(s ∈ S) (X - s). -/
noncomputable def vanishingPoly (S : Finset F) : Polynomial F :=
  ∏ s ∈ S, (Polynomial.X - Polynomial.C s)

omit [DecidableEq F] in
/-- The vanishing polynomial vanishes at every point of `S`. -/
lemma vanishingPoly_eval_eq_zero {S : Finset F} {s : F} (hs : s ∈ S) :
    (vanishingPoly S).eval s = 0 := by
  unfold vanishingPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero hs (by simp)

omit [DecidableEq F] in
/-- The vanishing polynomial is nonzero off `S`. -/
lemma vanishingPoly_eval_ne_zero {S : Finset F} {s : F} (hs : s ∉ S) :
    (vanishingPoly S).eval s ≠ 0 := by
  unfold vanishingPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero_of_ne (fun h => hs (h ▸ ha))

omit [DecidableEq F] in
/-- The vanishing polynomial is monic. -/
lemma vanishingPoly_monic (S : Finset F) : (vanishingPoly S).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_sub_C s)

omit [DecidableEq F] in
/-- The vanishing polynomial has degree exactly `|S|`. -/
lemma vanishingPoly_natDegree (S : Finset F) : (vanishingPoly S).natDegree = S.card := by
  unfold vanishingPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_sub_C s)]
  simp

/-- The answer polynomial has degree below `|S|`. -/
lemma ansPoly_degree_lt (S : Finset F) (Ans : S → F) :
    (ansPoly S Ans).degree < S.card := by
  unfold ansPoly
  have h := Lagrange.degree_interpolate_lt (s := S.attach) (v := fun i => (i : F)) Ans
    Subtype.val_injective.injOn
  rwa [Finset.card_attach] at h

/-- The answer polynomial interpolates `Ans` on `S`. -/
lemma ansPoly_eval {S : Finset F} (Ans : S → F) {s : F} (hs : s ∈ S) :
    (ansPoly S Ans).eval s = Ans ⟨s, hs⟩ := by
  unfold ansPoly
  exact Lagrange.eval_interpolate_at_node Ans
    Subtype.val_injective.injOn (Finset.mem_attach S ⟨s, hs⟩)

/-- Definition 4.2
  funcQuotient is the quotient function that outputs
  if x ∈ S,  Fill(x).
  else       (f(x) - Ans'(x)) / V(x).
  Note here that, V(x) = 0 ∀ x ∈ S, otherwise V(x) ≠ 0. -/
noncomputable def funcQuotient (f : ι → F) (S : Finset F) (Ans Fill : S → F) : ι → F :=
  fun x =>
    if hx : x.val ∈ S then Fill ⟨x.val, hx⟩ -- if x ∈ S,  Fill(x).
    else (f x - (ansPoly S Ans).eval x.val) / (vanishingPoly S).eval x.val

/-- Definition 4.3
  polyQuotient is the polynomial derived from the polynomials fPoly, Ans' and V, where
  Ans' is a polynomial s.t. Ans'(x) = fPoly(x) for x ∈ S, and
  V is the vanishing polynomial on S as before.
  Then, polyQuotient = (fPoly - Ans') / V, where
  polyQuotient.degree < (fPoly.degree - ι.card) -/
noncomputable def polyQuotient (S : Finset F) (fPoly : F[X]) : F[X] :=
    (fPoly - (ansPoly S (fun s => fPoly.eval s))) / (vanishingPoly S)

/-- We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S
such that the Ans' disagrees with f, we have
disagreementSet := { x ∈ ι ∩ S ∧ AnsPoly x ≠ f x }.

Quotienting-specific shape — *not* a direct specialisation of
`Code.disagreementCols` (which compares two `ι → R` words pointwise).
Here the comparison is between `f x` and the *polynomial extension*
`(ansPoly S Ans).eval x` of a finite assignment `Ans : S → F`, and is
restricted to `x` whose image lies in the answer-set `S`. The
canonical-base relationship is therefore: it is the
`Code.disagreementCols`-like disagreement of `(f, ansPoly ∘ eval)`
restricted to the preimage of `S` and then `image`d through
`Subtype.val`. -/
noncomputable def disagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  Set.toFinset ({x : ι | x.val ∈ S ∧ (ansPoly S Ans).eval x.val ≠ f x}.image Subtype.val)

/-- The quotient-reconstruction polynomial `w * V_S + Ans'` stays below `degree` whenever
`deg w < degree - |S|` and `|S| < degree`. -/
lemma reconstruct_mem_degreeLT {S : Finset F} {degree : ℕ} (hS_lt : S.card < degree)
    {w : Polynomial F} (hw : w ∈ Polynomial.degreeLT F (degree - S.card)) (Ans : S → F) :
    w * vanishingPoly S + ansPoly S Ans ∈ Polynomial.degreeLT F degree := by
  rw [Polynomial.mem_degreeLT] at hw ⊢
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · rcases eq_or_ne w 0 with rfl | hw0
    · rw [zero_mul, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_mul,
        Polynomial.degree_eq_natDegree (vanishingPoly_monic S).ne_zero,
        vanishingPoly_natDegree]
      have h1 : w.degree + (S.card : WithBot ℕ)
          < ((degree - S.card : ℕ) : WithBot ℕ) + (S.card : WithBot ℕ) :=
        WithBot.add_lt_add_right (by simp) hw
      refine lt_of_lt_of_eq h1 ?_
      rw [← Nat.cast_add, Nat.sub_add_cancel hS_lt.le]
  · exact lt_trans (ansPoly_degree_lt S Ans) (by exact_mod_cast hS_lt)

omit [DecidableEq F] in
/-- Evaluation vectors of `degreeLT` polynomials are codewords. -/
lemma evalOnPoints_mem_code {degree : ℕ} {domain : ι ↪ F} {p : Polynomial F}
    (hp : p ∈ Polynomial.degreeLT F degree) :
    (fun x => p.eval (domain x)) ∈ code domain degree :=
  Submodule.mem_map.mpr ⟨p, hp, rfl⟩

/-- Decoding round-trip: a codeword that is the evaluation vector of a polynomial of degree
below `degree ≤ |ι|` decodes back to that polynomial (interpolation uniqueness). -/
lemma decodeLT_evalOnPoints {degree : ℕ} {domain : ι ↪ F} (hdeg : degree ≤ ι.card)
    {p : Polynomial F} (hp : p ∈ Polynomial.degreeLT F degree)
    (c : code domain degree) (hc : ∀ x, c.val x = p.eval (domain x)) :
    ((decodeLT c : Polynomial F)) = p := by
  have hval : c.val = fun x => p.eval (domain x) := funext hc
  have hlt : p.degree < (((Finset.univ : Finset ι)).card : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLT] at hp
    refine lt_of_lt_of_le hp ?_
    rw [Finset.card_univ, Fintype.card_coe]
    exact_mod_cast hdeg
  have h := Lagrange.eq_interpolate (s := (Finset.univ : Finset ι)) (v := ⇑domain)
    domain.injective.injOn hlt
  calc ((decodeLT c : Polynomial F))
      = Lagrange.interpolate Finset.univ ⇑domain c.val := rfl
    _ = Lagrange.interpolate Finset.univ ⇑domain (fun i => p.eval (domain i)) := by rw [hval]
    _ = p := h.symm

/-- The `ℚ≥0`-valued relative Hamming distance, cast to `ENNReal`, is the `ENNReal` quotient of
the Hamming distance by the domain size. -/
lemma relHammingDist_cast_ennreal {ι' : Type*} [Fintype ι'] [Nonempty ι'] {G : Type*}
    [DecidableEq G] (u v : ι' → G) :
    ((relHammingDist u v : ℚ≥0) : ENNReal)
      = (hammingDist u v : ENNReal) / (Fintype.card ι' : ENNReal) := by
  rw [show ((relHammingDist u v : ℚ≥0) : ENNReal)
      = (((relHammingDist u v : ℚ≥0) : ℝ≥0) : ENNReal) from rfl]
  unfold relHammingDist
  rw [NNRat.cast_div, ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero)]
  norm_cast

/-- Quotienting Lemma 4.4
  Let `f : ι → F` be a function, `degree` a degree parameter, `δ ∈ (0,1)` be a distance parameter
  `S` be a set with |S| < degree, `Ans, Fill : S → F`. Suppose for all `u ∈ Λ(code, f, δ)`,
  there exists `x : S`, such that `uPoly(x) ≠ Ans(x)` then
  `δᵣ(funcQuotient(f, S, Ans, Fill), code[ι, F, degree - |S|]) + |T|/|ι| > δ`,
  where T is the disagreementSet as defined above.

  Compared to the original (sorried) statement, two hypotheses are added; both are implicit
  in [ACFY24stir] and necessary for the claim:
  * `hdom : ∀ x, domain x = x.val` — `funcQuotient`/`disagreementSet` and the conclusion all
    evaluate `ansPoly`/`vanishingPoly` at `x.val`, while codewords of `code domain _` are
    evaluations at `domain x`; the quotient/reconstruction correspondence requires these to
    be the same points (the paper works with `L ⊆ F` directly).
  * `hdeg_le : degree ≤ ι.card` — the decoding round-trip (degree-`< degree` polynomials are
    determined by their evaluations on the domain) requires the degree budget to fit; STIR
    always operates at rate `< 1`. -/
lemma quotienting {degree : ℕ} {domain : ι ↪ F} [Nonempty ι]
    (hdom : ∀ x, domain x = x.val) (hdeg_le : degree ≤ ι.card)
  (S : Finset F) (hS_lt : S.card < degree) (_r : F)
  (f : ι → F) (Ans Fill : S → F) (δ : ℝ≥0) (_hδPos : δ > 0) (_hδLt : δ < 1)
  (h : ∀ u : code domain degree, u.val ∈ (closeCodewordsRel ↑(code domain degree) f δ) →
    ∃ x : S, ((decodeLT u) : F[X]).eval x.val ≠ Ans x) :
    δᵣ((funcQuotient f S Ans Fill), (code domain (degree - S.card))) +
      ((disagreementSet f S Ans).card) / (ι.card) > δ := by
  classical
  by_contra hcon
  rw [not_lt] at hcon
  set Q : ι → F := funcQuotient f S Ans Fill with hQdef
  -- The smaller code is nonempty; pick a closest codeword `w` to `Q`.
  haveI hCne : Nonempty ↥(↑(code domain (degree - S.card)) : Set (ι → F)) :=
    Set.nonempty_coe_sort.mpr ⟨0, Submodule.zero_mem _⟩
  obtain ⟨w, hwC, hwdist⟩ := exists_relClosest_codeword_of_Nonempty_Code
    (↑(code domain (degree - S.card)) : Set (ι → F)) Q
  obtain ⟨q, hq, hqw⟩ := Submodule.mem_map.mp hwC
  have hwx : ∀ x : ι, w x = q.eval x.val := by
    intro x
    rw [← hqw]
    show q.eval (domain x) = _
    rw [hdom]
  -- Reconstruct the degree-< degree polynomial and its codeword.
  have hUmem : q * vanishingPoly S + ansPoly S Ans ∈ Polynomial.degreeLT F degree :=
    reconstruct_mem_degreeLT hS_lt hq Ans
  set uvec : ι → F := fun x => (q * vanishingPoly S + ansPoly S Ans).eval (domain x) with huvec
  have huC : uvec ∈ code domain degree := evalOnPoints_mem_code hUmem
  have huvx : ∀ x : ι, uvec x
      = q.eval x.val * (vanishingPoly S).eval x.val + (ansPoly S Ans).eval x.val := by
    intro x
    rw [huvec]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hdom x]
  -- Counting: disagreements of `f` with `uvec` are covered by those of `Q` with `w`, plus `T`.
  have hcount : hammingDist f uvec
      ≤ hammingDist Q w + (disagreementSet f S Ans).card := by
    have hT : (disagreementSet f S Ans).card
        = (Finset.univ.filter
            (fun x : ι => x.val ∈ S ∧ (ansPoly S Ans).eval x.val ≠ f x)).card := by
      unfold disagreementSet
      rw [Set.toFinset_image, Finset.card_image_of_injective _ Subtype.val_injective,
        Set.toFinset_setOf]
    rw [hT]
    show (Finset.univ.filter (fun x => f x ≠ uvec x)).card ≤ _
    refine le_trans (Finset.card_le_card (t :=
        (Finset.univ.filter (fun x : ι => Q x ≠ w x)) ∪
        (Finset.univ.filter
          (fun x : ι => x.val ∈ S ∧ (ansPoly S Ans).eval x.val ≠ f x)) ) ?_)
      (Finset.card_union_le _ _)
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases Decidable.em (x.val ∈ S) with hxS | hxS
    · rcases Decidable.em ((ansPoly S Ans).eval x.val = f x) with hAx | hAx
      · exfalso
        apply hx.2
        rw [huvx x, vanishingPoly_eval_eq_zero hxS, mul_zero, zero_add, hAx]
      · exact Or.inr ⟨Finset.mem_univ _, hxS, hAx⟩
    · rcases Decidable.em (Q x = w x) with hQw | hQw
      · exfalso
        apply hx.2
        have hVne := vanishingPoly_eval_ne_zero (S := S) hxS
        have hQx : Q x
            = (f x - (ansPoly S Ans).eval x.val) / (vanishingPoly S).eval x.val := by
          rw [hQdef]
          unfold funcQuotient
          rw [dif_neg hxS]
        rw [huvx x, ← hwx x, ← hQw, hQx, div_mul_cancel₀ _ hVne, sub_add_cancel]
      · exact Or.inl ⟨Finset.mem_univ _, hQw⟩
  -- Lift to ENNReal: `uvec` is δ-close to `f`.
  have hcard0 : (ι.card : ENNReal) ≠ 0 := by
    have := Finset.card_pos.mpr ((Finset.nonempty_coe_sort (s := ι)).mp inferInstance)
    exact_mod_cast this.ne'
  have e1 : ((relHammingDist f uvec : ℚ≥0) : ENNReal)
      ≤ ((relHammingDist Q w : ℚ≥0) : ENNReal)
        + ((disagreementSet f S Ans).card : ENNReal) / (ι.card : ENNReal) := by
    rw [relHammingDist_cast_ennreal, relHammingDist_cast_ennreal, Fintype.card_coe,
      ENNReal.div_add_div_same]
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast hcount
  have hcon' : ((relHammingDist Q w : ℚ≥0) : ENNReal)
      + ((disagreementSet f S Ans).card : ENNReal) / (ι.card : ENNReal) ≤ (δ : ENNReal) := by
    rw [hwdist]
    exact hcon
  have e3 : ((relHammingDist f uvec : ℚ≥0) : ENNReal) ≤ (δ : ENNReal) := le_trans e1 hcon'
  have hclose_r : ((relHammingDist f uvec : ℚ≥0) : ℝ) ≤ ((δ : ℝ≥0) : ℝ) := by
    have h4 : ((relHammingDist f uvec : ℚ≥0) : ℝ≥0) ≤ δ := by
      rw [show ((relHammingDist f uvec : ℚ≥0) : ENNReal)
          = (((relHammingDist f uvec : ℚ≥0) : ℝ≥0) : ENNReal) from rfl] at e3
      exact_mod_cast e3
    exact_mod_cast h4
  have hclose : uvec ∈ closeCodewordsRel (↑(code domain degree) : Set (ι → F)) f (δ : ℝ) := by
    refine ⟨huC, ?_⟩
    show uvec ∈ relHammingBall f (δ : ℝ)
    unfold relHammingBall
    rw [Set.mem_setOf_eq]
    convert hclose_r using 2
    congr!
  -- The list hypothesis contradicts the decoded reconstruction agreeing with `Ans` on `S`.
  obtain ⟨a, ha⟩ := h ⟨uvec, huC⟩ hclose
  apply ha
  have hdecode : ((decodeLT (⟨uvec, huC⟩ : code domain degree)) : Polynomial F)
      = q * vanishingPoly S + ansPoly S Ans :=
    decodeLT_evalOnPoints hdeg_le hUmem _ (fun x => rfl)
  rw [hdecode, Polynomial.eval_add, Polynomial.eval_mul,
    vanishingPoly_eval_eq_zero a.2, mul_zero, zero_add, ansPoly_eval Ans a.2]

/-- Computable version of `ansPoly`: the unique interpolating polynomial of degree `< |S|`
agreeing with `Ans` on `S`. Built on CompPoly's `CLagrange.interpolate`. -/
def cpolyAnsPoly (S : Finset F) (Ans : S → F) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.CLagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- Bridge lemma: `cpolyAnsPoly` and `ansPoly` agree under `toPoly`. -/
@[simp]
lemma cpolyAnsPoly_toPoly (S : Finset F) (Ans : S → F) :
    (cpolyAnsPoly S Ans).toPoly = ansPoly S Ans := by
  unfold cpolyAnsPoly ansPoly
  exact CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate

/-- Computable version of `vanishingPoly`: `∏ s ∈ S, (X - C s)`, built on CompPoly's
`CPolynomial`. -/
def cpolyVanishingPoly (S : Finset F) : CompPoly.CPolynomial F :=
  ∏ s ∈ S, (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C s)

/-- Bridge lemma: `cpolyVanishingPoly` and `vanishingPoly` agree under `toPoly`. -/
@[simp]
lemma cpolyVanishingPoly_toPoly (S : Finset F) :
    (cpolyVanishingPoly S).toPoly = vanishingPoly S := by
  unfold cpolyVanishingPoly vanishingPoly
  rw [CompPoly.CPolynomial.toPoly_prod]
  refine Finset.prod_congr rfl ?_
  intro s _
  rw [CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.X_toPoly,
      CompPoly.CPolynomial.C_toPoly]

/-- Computable version of `funcQuotient`. Uses the cpoly versions of `ansPoly` and
`vanishingPoly` for the off-`S` branch; the on-`S` branch is identical to the Mathlib spec. -/
def cpolyFuncQuotient (f : ι → F) (S : Finset F) (Ans Fill : S → F) : ι → F :=
  fun x =>
    if hx : x.val ∈ S then Fill ⟨x.val, hx⟩
    else (f x - (cpolyAnsPoly S Ans).eval x.val) / (cpolyVanishingPoly S).eval x.val

/-- Function equality: `cpolyFuncQuotient` agrees with `funcQuotient`. -/
@[simp]
lemma cpolyFuncQuotient_eq_funcQuotient
    (f : ι → F) (S : Finset F) (Ans Fill : S → F) :
    cpolyFuncQuotient f S Ans Fill = funcQuotient f S Ans Fill := by
  funext x
  unfold cpolyFuncQuotient funcQuotient
  by_cases hx : x.val ∈ S
  · simp [hx]
  · simp only [hx, dif_neg, not_false_eq_true]
    rw [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly,
        CompPoly.CPolynomial.eval_toPoly, cpolyVanishingPoly_toPoly]

/-- Computable version of `disagreementSet`: the set of `x ∈ ι ∩ S` at which the answer
polynomial `cpolyAnsPoly` disagrees with `f`. Uses `Finset.filter` over the decidable predicate
in place of the noncomputable `Set.toFinset`. -/
def cpolyDisagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  (ι.attach.filter
    (fun x => x.val ∈ S ∧ (cpolyAnsPoly S Ans).eval x.val ≠ f x)).image Subtype.val

/-- Set equality: `cpolyDisagreementSet` and `disagreementSet` describe the same `Finset F`. -/
@[simp]
lemma cpolyDisagreementSet_eq_disagreementSet
    (f : ι → F) (S : Finset F) (Ans : S → F) :
    cpolyDisagreementSet f S Ans = disagreementSet f S Ans := by
  ext y
  simp only [cpolyDisagreementSet, disagreementSet,
    Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
    Set.mem_toFinset, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hxS, hxDis⟩, hxy⟩
    refine ⟨x, ⟨hxS, ?_⟩, hxy⟩
    rwa [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly] at hxDis
  · rintro ⟨x, ⟨hxS, hxDis⟩, hxy⟩
    refine ⟨x, ⟨hxS, ?_⟩, hxy⟩
    rw [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly]
    exact hxDis

end Quotienting
