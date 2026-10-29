/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Stir.Quotienting

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
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
    cpolyFuncQuotient f S Ans Fill =
      funcQuotient (Function.Embedding.subtype _) f S Ans Fill := by
  funext x
  by_cases hx : x.val ∈ S
  · rw [funcQuotient_of_mem (domain := Function.Embedding.subtype _) hx]
    simp [cpolyFuncQuotient, hx]
  · rw [funcQuotient_of_not_mem (domain := Function.Embedding.subtype _) hx]
    simp only [cpolyFuncQuotient, hx, dite_false, Function.Embedding.subtype_apply]
    rw [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly,
        CompPoly.CPolynomial.eval_toPoly, cpolyVanishingPoly_toPoly]

/-- Computable version of `disagreementSet`: the set of `x ∈ ι ∩ S` at which the answer
polynomial `cpolyAnsPoly` disagrees with `f`, expressed in ambient-field coordinates. -/
def cpolyDisagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  (ι.attach.filter
    (fun x => x.val ∈ S ∧ (cpolyAnsPoly S Ans).eval x.val ≠ f x)).image Subtype.val

/-- The computable ambient-field set is the image of the canonical coordinate-indexed set. -/
@[simp]
lemma cpolyDisagreementSet_eq_disagreementSet
    (f : ι → F) (S : Finset F) (Ans : S → F) :
    cpolyDisagreementSet f S Ans =
      (disagreementSet (Function.Embedding.subtype _) f S Ans).image Subtype.val := by
  unfold cpolyDisagreementSet disagreementSet
  apply congrArg (Finset.image Subtype.val)
  rw [Finset.attach_eq_univ]
  apply Finset.filter_congr
  intro x _
  change (x.val ∈ S ∧ (cpolyAnsPoly S Ans).eval x.val ≠ f x) ↔
    (x.val ∈ S ∧ (ansPoly S Ans).eval x.val ≠ f x)
  rw [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly]

end Quotienting
