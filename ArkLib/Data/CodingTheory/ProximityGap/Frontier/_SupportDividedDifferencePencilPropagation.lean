/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceOperator
import ArkLib.ToMathlib.Polynomial.EvalExt

/-!
# Propagation of low-degree affine pencils

Local divided-difference rigidity produces an affine pair at every coordinate.  A first global
gluing brick is that two degree-`<K` polynomial pencils cannot remain different after agreeing at
two distinct scalar labels on `K` injective domain points.  The label pair may vary with the
coordinate: the two labels first pin both coefficient evaluations pointwise, then polynomial
interpolation pins both coefficient polynomials globally.

These theorems consume the required overlaps.  They do not extract them from support incidence or
prove the degree-restricted global kernel rigidity needed for the P1 exact pin.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.SupportDividedDifferencePencilPropagation

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Two low-degree polynomial pencils which agree at a coordinate-dependent pair of distinct
labels on `K` domain points are the same pencil.  This is a conditional gluing lemma: it consumes
the paired overlaps rather than constructing them from the support system. -/
theorem polynomialPencil_eq_of_coordinatewise_two_labels_agree_on
    (domain : I → F) (S : Finset I) (hinj : Set.InjOn domain ↑S)
    {K : ℕ} (hcard : S.card = K)
    (base₀ slope₀ base₁ slope₁ : Polynomial F)
    (hbase₀ : base₀ ∈ Polynomial.degreeLT F K)
    (hslope₀ : slope₀ ∈ Polynomial.degreeLT F K)
    (hbase₁ : base₁ ∈ Polynomial.degreeLT F K)
    (hslope₁ : slope₁ ∈ Polynomial.degreeLT F K)
    (gamma gamma' : I → F) (hgamma : ∀ x ∈ S, gamma x ≠ gamma' x)
    (hagree : ∀ x ∈ S,
      base₀.eval (domain x) + gamma x • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma x • slope₁.eval (domain x) ∧
        base₀.eval (domain x) + gamma' x • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma' x • slope₁.eval (domain x)) :
    base₀ = base₁ ∧ slope₀ = slope₁ := by
  have hpinned : ∀ x ∈ S,
      base₀.eval (domain x) = base₁.eval (domain x) ∧
        slope₀.eval (domain x) = slope₁.eval (domain x) := by
    intro x hx
    exact ProximityGap.affine_eq_of_two_smul_points (hgamma x hx)
      (hagree x hx).1 (hagree x hx).2
  have hdeg_base₀ : base₀.degree < (S.card : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLT] at hbase₀
    simpa [hcard] using hbase₀
  have hdeg_base₁ : base₁.degree < (S.card : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLT] at hbase₁
    simpa [hcard] using hbase₁
  have hdeg_slope₀ : slope₀.degree < (S.card : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLT] at hslope₀
    simpa [hcard] using hslope₀
  have hdeg_slope₁ : slope₁.degree < (S.card : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLT] at hslope₁
    simpa [hcard] using hslope₁
  constructor
  · exact Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj hdeg_base₀ hdeg_base₁
      (fun x hx => (hpinned x hx).1)
  · exact Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj hdeg_slope₀ hdeg_slope₁
      (fun x hx => (hpinned x hx).2)

/-- Fixed-label specialization of
`polynomialPencil_eq_of_coordinatewise_two_labels_agree_on`. -/
theorem polynomialPencil_eq_of_two_labels_agree_on
    (domain : I → F) (S : Finset I) (hinj : Set.InjOn domain ↑S)
    {K : ℕ} (hcard : S.card = K)
    (base₀ slope₀ base₁ slope₁ : Polynomial F)
    (hbase₀ : base₀ ∈ Polynomial.degreeLT F K)
    (hslope₀ : slope₀ ∈ Polynomial.degreeLT F K)
    (hbase₁ : base₁ ∈ Polynomial.degreeLT F K)
    (hslope₁ : slope₁ ∈ Polynomial.degreeLT F K)
    {gamma gamma' : F} (hgamma : gamma ≠ gamma')
    (hagree : ∀ x ∈ S,
      base₀.eval (domain x) + gamma • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma • slope₁.eval (domain x) ∧
        base₀.eval (domain x) + gamma' • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma' • slope₁.eval (domain x)) :
    base₀ = base₁ ∧ slope₀ = slope₁ := by
  exact polynomialPencil_eq_of_coordinatewise_two_labels_agree_on domain S hinj hcard
    base₀ slope₀ base₁ slope₁ hbase₀ hslope₀ hbase₁ hslope₁
    (fun _ => gamma) (fun _ => gamma') (fun _ _ => hgamma) hagree

/-- After coordinatewise two-label propagation, the two polynomial families agree for every
scalar label, not only for the label pairs used in the overlaps. -/
theorem all_labels_agree_of_coordinatewise_two_labels_agree_on
    (domain : I → F) (S : Finset I) (hinj : Set.InjOn domain ↑S)
    {K : ℕ} (hcard : S.card = K)
    (base₀ slope₀ base₁ slope₁ : Polynomial F)
    (hbase₀ : base₀ ∈ Polynomial.degreeLT F K)
    (hslope₀ : slope₀ ∈ Polynomial.degreeLT F K)
    (hbase₁ : base₁ ∈ Polynomial.degreeLT F K)
    (hslope₁ : slope₁ ∈ Polynomial.degreeLT F K)
    (gamma gamma' : I → F) (hgamma : ∀ x ∈ S, gamma x ≠ gamma' x)
    (hagree : ∀ x ∈ S,
      base₀.eval (domain x) + gamma x • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma x • slope₁.eval (domain x) ∧
        base₀.eval (domain x) + gamma' x • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma' x • slope₁.eval (domain x)) :
    ∀ delta : F, base₀ + delta • slope₀ = base₁ + delta • slope₁ := by
  obtain ⟨rfl, rfl⟩ := polynomialPencil_eq_of_coordinatewise_two_labels_agree_on
    domain S hinj hcard base₀ slope₀ base₁ slope₁ hbase₀ hslope₀ hbase₁ hslope₁
      gamma gamma' hgamma hagree
  exact fun _ => rfl

/-- Fixed-label specialization of
`all_labels_agree_of_coordinatewise_two_labels_agree_on`. -/
theorem all_labels_agree_of_two_labels_agree_on
    (domain : I → F) (S : Finset I) (hinj : Set.InjOn domain ↑S)
    {K : ℕ} (hcard : S.card = K)
    (base₀ slope₀ base₁ slope₁ : Polynomial F)
    (hbase₀ : base₀ ∈ Polynomial.degreeLT F K)
    (hslope₀ : slope₀ ∈ Polynomial.degreeLT F K)
    (hbase₁ : base₁ ∈ Polynomial.degreeLT F K)
    (hslope₁ : slope₁ ∈ Polynomial.degreeLT F K)
    {gamma gamma' : F} (hgamma : gamma ≠ gamma')
    (hagree : ∀ x ∈ S,
      base₀.eval (domain x) + gamma • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma • slope₁.eval (domain x) ∧
        base₀.eval (domain x) + gamma' • slope₀.eval (domain x) =
          base₁.eval (domain x) + gamma' • slope₁.eval (domain x)) :
    ∀ delta : F, base₀ + delta • slope₀ = base₁ + delta • slope₁ := by
  obtain ⟨rfl, rfl⟩ := polynomialPencil_eq_of_two_labels_agree_on domain S hinj hcard
    base₀ slope₀ base₁ slope₁ hbase₀ hslope₀ hbase₁ hslope₁ hgamma hagree
  exact fun _ => rfl

end ArkLib.ProximityGap.Frontier.SupportDividedDifferencePencilPropagation

open ArkLib.ProximityGap.Frontier.SupportDividedDifferencePencilPropagation

#print axioms polynomialPencil_eq_of_coordinatewise_two_labels_agree_on
#print axioms polynomialPencil_eq_of_two_labels_agree_on
#print axioms all_labels_agree_of_coordinatewise_two_labels_agree_on
#print axioms all_labels_agree_of_two_labels_agree_on
