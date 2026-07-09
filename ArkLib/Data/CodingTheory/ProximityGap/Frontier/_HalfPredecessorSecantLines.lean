/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge

/-!
# The finite secant-line space of a bad-scalar rich-point family

This file turns the local polynomial-line geometry into a finite incidence
structure.  A line parameter is a pair `(a,r)` and contains precisely the
selected lifted points satisfying `q gamma = a + C gamma * r`.  The finite set
of relevant lines is the image of the ordered distinct pairs of selected
points under the canonical secant construction.

The important feature is uniqueness: every two distinct selected points lie
on exactly one such polynomial line.  Consequently all later pair and triple
counts can be carried out over a literal `Finset` of lines, without quotienting
by an ad-hoc collinearity relation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A nonvertical polynomial line, written `q = a + gamma * r`. -/
abbrev LineParameter (F : Type) [Semiring F] := F[X] × F[X]

/-- Ordered pairs of distinct members of a finite set. -/
def orderedDistinctPairs (G : Finset F) : Finset (F × F) :=
  (G ×ˢ G).filter fun pair => pair.1 ≠ pair.2

@[simp]
theorem mem_orderedDistinctPairs_iff (G : Finset F) (gamma beta : F) :
    (gamma, beta) ∈ orderedDistinctPairs G ↔
      gamma ∈ G ∧ beta ∈ G ∧ gamma ≠ beta := by
  simp only [orderedDistinctPairs, mem_filter, mem_product, and_assoc]

/-- The canonical polynomial-line parameter through two lifted points. -/
noncomputable def secantParameter
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma beta : F) : LineParameter F :=
  let r := slopePolynomial gamma beta (family.q gamma) (family.q beta)
  (family.q gamma - C gamma * r, r)

/-- The selected scalar points lying on a polynomial line. -/
noncomputable def pointsOn
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) : Finset F :=
  family.G.filter fun gamma =>
    family.q gamma = line.1 + C gamma * line.2

@[simp]
theorem mem_pointsOn_iff
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) (gamma : F) :
    gamma ∈ pointsOn family line ↔
      gamma ∈ family.G ∧
        family.q gamma = line.1 + C gamma * line.2 := by
  simp only [pointsOn, mem_filter]

theorem pointsOn_subset_G
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) :
    pointsOn family line ⊆ family.G := by
  intro gamma hgamma
  exact (mem_pointsOn_iff family line gamma).mp hgamma |>.1

/-- The finite set of lines determined by pairs of selected lifted points. -/
noncomputable def lineParameters
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) :
    Finset (LineParameter F) :=
  (orderedDistinctPairs family.G).image fun pair =>
    secantParameter family pair.1 pair.2

/-- The first lifted point lies on its canonical secant. -/
theorem first_point_mem_pointsOn_secant
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma beta : F} (hgamma : gamma ∈ family.G) :
    gamma ∈ pointsOn family (secantParameter family gamma beta) := by
  rw [mem_pointsOn_iff]
  refine ⟨hgamma, ?_⟩
  simp only [secantParameter]
  ring

/-- The second lifted point lies on its canonical secant. -/
theorem second_point_mem_pointsOn_secant
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma beta : F} (hbeta : beta ∈ family.G) (hne : gamma ≠ beta) :
    beta ∈ pointsOn family (secantParameter family gamma beta) := by
  rw [mem_pointsOn_iff]
  refine ⟨hbeta, ?_⟩
  simpa only [secantParameter] using
    (second_point_on_secant_line hne (family.q gamma) (family.q beta))

/-- Every distinct selected pair determines a member of `lineParameters`. -/
theorem secantParameter_mem_lineParameters
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma beta : F} (hgamma : gamma ∈ family.G)
    (hbeta : beta ∈ family.G) (hne : gamma ≠ beta) :
    secantParameter family gamma beta ∈ lineParameters family := by
  rw [lineParameters, mem_image]
  exact ⟨(gamma, beta),
    (mem_orderedDistinctPairs_iff family.G gamma beta).mpr
      ⟨hgamma, hbeta, hne⟩, rfl⟩

/-- If two distinct lifted points lie on `(a,r)`, their slope is `r`. -/
theorem slopePolynomial_eq_of_mem_pointsOn
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) {gamma beta : F}
    (hgamma : gamma ∈ pointsOn family line)
    (hbeta : beta ∈ pointsOn family line) (hne : gamma ≠ beta) :
    slopePolynomial gamma beta (family.q gamma) (family.q beta) =
      line.2 := by
  have hgammaLine := (mem_pointsOn_iff family line gamma).mp hgamma |>.2
  have hbetaLine := (mem_pointsOn_iff family line beta).mp hbeta |>.2
  have hC : C (gamma - beta) ≠ (0 : F[X]) := by
    rw [C_ne_zero]
    exact sub_ne_zero.mpr hne
  apply (mul_left_cancel₀ hC)
  rw [C_sub_mul_slopePolynomial hne]
  rw [hgammaLine, hbetaLine, C_sub]
  ring

/-- **Unique secant parameter.**  Any line containing two distinct selected
points equals their canonical secant parameter. -/
theorem secantParameter_eq_of_mem_pointsOn
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) {gamma beta : F}
    (hgamma : gamma ∈ pointsOn family line)
    (hbeta : beta ∈ pointsOn family line) (hne : gamma ≠ beta) :
    secantParameter family gamma beta = line := by
  have hslope := slopePolynomial_eq_of_mem_pointsOn family line hgamma hbeta hne
  have hgammaLine := (mem_pointsOn_iff family line gamma).mp hgamma |>.2
  apply Prod.ext
  · simp only [secantParameter]
    rw [hslope, hgammaLine]
    ring
  · simpa only [secantParameter] using hslope

/-- Every relevant line is represented by a distinct selected pair. -/
theorem exists_pair_of_mem_lineParameters
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    ∃ gamma ∈ family.G, ∃ beta ∈ family.G,
      gamma ≠ beta ∧ line = secantParameter family gamma beta := by
  rw [lineParameters, mem_image] at hline
  obtain ⟨pair, hpair, rfl⟩ := hline
  have hp := (mem_orderedDistinctPairs_iff family.G pair.1 pair.2).mp hpair
  exact ⟨pair.1, hp.1, pair.2, hp.2.1, hp.2.2, rfl⟩

/-- Every relevant line contains at least the two points defining it. -/
theorem two_le_pointsOn_card_of_mem_lineParameters
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    2 ≤ (pointsOn family line).card := by
  obtain ⟨gamma, hgamma, beta, hbeta, hne, rfl⟩ :=
    exists_pair_of_mem_lineParameters family hline
  have hgammaOn :=
    first_point_mem_pointsOn_secant family (beta := beta) hgamma
  have hbetaOn :=
    second_point_mem_pointsOn_secant family (gamma := gamma) hbeta hne
  have hsub : {gamma, beta} ⊆ pointsOn family (secantParameter family gamma beta) := by
    intro theta htheta
    simp only [mem_insert, mem_singleton] at htheta
    rcases htheta with rfl | rfl
    · exact hgammaOn
    · exact hbetaOn
  have hcard := card_le_card hsub
  have hpairCard : ({gamma, beta} : Finset F).card = 2 := by
    simp [hne]
  omega

/-- The slope and intercept of every relevant line retain degree `< k`. -/
theorem lineParameter_degree_lt
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    line.1.natDegree < k ∧ line.2.natDegree < k := by
  obtain ⟨gamma, hgamma, beta, hbeta, hne, rfl⟩ :=
    exists_pair_of_mem_lineParameters family hline
  have hqgamma := family.degree_lt gamma hgamma
  have hqbeta := family.degree_lt beta hbeta
  have hr :
      (slopePolynomial gamma beta (family.q gamma) (family.q beta)).natDegree < k :=
    slopePolynomial_natDegree_lt hqgamma hqbeta
  refine ⟨?_, hr⟩
  exact lt_of_le_of_lt
    (natDegree_sub_le _ _)
    (max_lt hqgamma
      (lt_of_le_of_lt (natDegree_C_mul_le _ _) hr))

/-- The bad-family packing inequality, specialized to every relevant secant
line in the finite incidence structure. -/
theorem pointsOn_card_mul_max_add_core_le
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    (pointsOn family line).card *
        max 1 (⌈(1 - delta) * (Fintype.card ι : NNReal)⌉₊ -
          (jointCore dom (u 0) (u 1) line.1 line.2).card) +
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤
        Fintype.card ι := by
  have hdeg := lineParameter_degree_lt family hline
  exact family.line_core_packing line.1 line.2 (pointsOn family line)
    hdeg.1 hdeg.2 (pointsOn_subset_G family line)
    (fun gamma hgamma => (mem_pointsOn_iff family line gamma).mp hgamma |>.2)

/-! ## Exact partition of ordered pairs by secant line -/

/-- The number of ordered distinct pairs from an `N`-element set is
`N * (N - 1)`. -/
theorem card_orderedDistinctPairs (G : Finset F) :
    (orderedDistinctPairs G).card = G.card * (G.card - 1) := by
  let diagonal : Finset (F × F) :=
    (G ×ˢ G).filter fun pair => pair.1 = pair.2
  have hsplit := card_filter_add_card_filter_not
    (s := G ×ˢ G) (p := fun pair : F × F => pair.1 = pair.2)
  have hdiagEq : diagonal = G.image fun gamma => (gamma, gamma) := by
    ext pair
    simp only [diagonal, mem_filter, mem_product, mem_image, Prod.ext_iff]
    constructor
    · rintro ⟨⟨hfst, hsnd⟩, heq⟩
      exact ⟨pair.1, hfst, rfl, heq.symm⟩
    · rintro ⟨gamma, hgamma, hfst, hsnd⟩
      subst hfst
      subst hsnd
      exact ⟨⟨hgamma, hgamma⟩, rfl⟩
  have hinj : Function.Injective (fun gamma : F => (gamma, gamma)) := by
    intro gamma beta h
    exact congrArg Prod.fst h
  have hdiagCard : diagonal.card = G.card := by
    rw [hdiagEq, card_image_iff.mpr hinj]
  have hsplit' : diagonal.card + (orderedDistinctPairs G).card =
      (G ×ˢ G).card := by
    simpa only [diagonal, orderedDistinctPairs, ne_eq] using hsplit
  rw [hdiagCard, card_product] at hsplit'
  by_cases hG : G.card = 0
  · simp only [hG, zero_mul, Nat.zero_sub] at hsplit' ⊢
  · have hone : 1 ≤ G.card := Nat.one_le_iff_ne_zero.mpr hG
    have hmul : G.card * G.card =
        G.card + G.card * (G.card - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hone]
      ring
    omega

/-- The fiber of the secant map over a relevant line is exactly the ordered
distinct pairs of selected points on that line. -/
theorem secant_fiber_eq_orderedDistinctPairs_pointsOn
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) :
    (orderedDistinctPairs family.G).filter
        (fun pair => secantParameter family pair.1 pair.2 = line) =
      orderedDistinctPairs (pointsOn family line) := by
  ext pair
  simp only [mem_filter, mem_orderedDistinctPairs_iff]
  constructor
  · rintro ⟨⟨hfst, hsnd, hne⟩, hparam⟩
    have hfirst := first_point_mem_pointsOn_secant
      family (beta := pair.2) hfst
    have hsecond := second_point_mem_pointsOn_secant
      family (gamma := pair.1) hsnd hne
    rw [hparam] at hfirst hsecond
    exact ⟨hfirst, hsecond, hne⟩
  · rintro ⟨hfirst, hsecond, hne⟩
    have hfst := (mem_pointsOn_iff family line pair.1).mp hfirst |>.1
    have hsnd := (mem_pointsOn_iff family line pair.2).mp hsecond |>.1
    exact ⟨⟨hfst, hsnd, hne⟩,
      secantParameter_eq_of_mem_pointsOn family line hfirst hsecond hne⟩

/-- **Pair partition identity.** Every ordered distinct selected pair belongs
to exactly one relevant polynomial line. -/
theorem sum_pointsOn_mul_pred_eq_G_mul_pred
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) :
    ∑ line ∈ lineParameters family,
        (pointsOn family line).card * ((pointsOn family line).card - 1) =
      family.G.card * (family.G.card - 1) := by
  let pairLine : F × F → LineParameter F := fun pair =>
    secantParameter family pair.1 pair.2
  have hmaps : ((orderedDistinctPairs family.G : Finset (F × F)) : Set (F × F)).MapsTo
      pairLine (lineParameters family) := by
    intro pair hpair
    have hp := (mem_orderedDistinctPairs_iff family.G pair.1 pair.2).mp hpair
    exact secantParameter_mem_lineParameters family hp.1 hp.2.1 hp.2.2
  have hpartition := card_eq_sum_card_fiberwise hmaps
  rw [card_orderedDistinctPairs] at hpartition
  rw [← hpartition]
  apply sum_congr rfl
  intro line hline
  have hfiber := congrArg Finset.card
    (secant_fiber_eq_orderedDistinctPairs_pointsOn family line)
  simpa only [pairLine, card_orderedDistinctPairs] using hfiber.symm

end ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines.secantParameter_eq_of_mem_pointsOn
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines.pointsOn_card_mul_max_add_core_le
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines.sum_pointsOn_mul_pred_eq_G_mul_pred
