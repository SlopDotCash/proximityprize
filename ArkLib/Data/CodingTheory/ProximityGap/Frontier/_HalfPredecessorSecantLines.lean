/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCorePacking

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
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking

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
    aesop
  have hinj : Function.Injective (fun gamma : F => (gamma, gamma)) := by
    intro gamma beta h
    exact congrArg Prod.fst h
  have hdiagCard : diagonal.card = G.card := by
    rw [hdiagEq, card_image_of_injective G hinj]
  have hsplit' : diagonal.card + (orderedDistinctPairs G).card =
      (G ×ˢ G).card := by
    simpa only [diagonal, orderedDistinctPairs, ne_eq] using hsplit
  rw [hdiagCard, card_product] at hsplit'
  by_cases hG : G.card = 0
  · simp only [hG, zero_mul, Nat.zero_sub] at hsplit' ⊢
    omega
  · have hone : 1 ≤ G.card := Nat.one_le_iff_ne_zero.mpr hG
    have hmul : G.card * G.card =
        G.card + G.card * (G.card - 1) := by
      calc
        G.card * G.card = G.card * ((G.card - 1) + 1) := by
          rw [Nat.sub_add_cancel hone]
        _ = G.card * (G.card - 1) + G.card := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = G.card + G.card * (G.card - 1) := Nat.add_comm _ _
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
  simp only [Finset.mem_filter]
  rw [mem_orderedDistinctPairs_iff, mem_orderedDistinctPairs_iff]
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
  rw [hpartition]
  apply sum_congr rfl
  intro line hline
  have hfiber := congrArg Finset.card
    (secant_fiber_eq_orderedDistinctPairs_pointsOn family line)
  simpa only [pairLine, card_orderedDistinctPairs] using hfiber.symm

/-! ## High-core collapse -/

/-- A general numerical consequence of fresh-fibre packing: at agreement
threshold `t` in `n` coordinates, every nonempty proper polynomial line has at
most `n - t + 1` selected points. -/
theorem line_card_le_complement_threshold_succ
    {n t z L : ℕ} (ht : t ≤ n) (hz : z ≤ n) (hL : 1 ≤ L)
    (hpacking : L * max 1 (t - z) + z ≤ n) :
    L ≤ n - t + 1 := by
  by_cases hzt : z < t
  · have hc : 1 ≤ t - z := by omega
    have hmax : max 1 (t - z) = t - z := max_eq_right hc
    rw [hmax] at hpacking
    have haux : L + (t - z) - 1 ≤ L * (t - z) := by
      have hLz : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
      have hcz : (1 : ℤ) ≤ (t - z : ℕ) := by exact_mod_cast hc
      have hprod : (0 : ℤ) ≤
          ((L : ℤ) - 1) * ((t - z : ℕ) - 1) :=
        mul_nonneg (sub_nonneg.mpr hLz) (sub_nonneg.mpr hcz)
      have hauxZ : (L : ℤ) + (t - z : ℕ) ≤
          (L : ℤ) * (t - z : ℕ) + 1 := by nlinarith
      have hauxNat : L + (t - z) ≤ L * (t - z) + 1 := by
        exact_mod_cast hauxZ
      omega
    have htz : t - z + z = t := Nat.sub_add_cancel (Nat.le_of_lt hzt)
    omega
  · have hmax : 1 ≤ max 1 (t - z) := le_max_left _ _
    have hmul : L ≤ L * max 1 (t - z) := by
      simpa only [mul_one] using Nat.mul_le_mul_left L hmax
    have htz : t ≤ z := by omega
    omega

/-- On a high-core line, three off-line selected points have common agreement
larger than the Reed--Solomon root cap.  This is the finite-set form of the
Bonferroni step in the line-richness dichotomy. -/
theorem triple_fullAgreement_card_gt_pred_of_outside_high_core
    {dom : ι ↪ F} {k t : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (htd : k - 1 ≤ t)
    (hlarge : ∀ gamma ∈ family.G,
      t ≤ (fullAgreement dom (u 0) (u 1) gamma
        (family.q gamma)).card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hhigh : 2 * Fintype.card ι + 4 * (k - 1) <
      3 * t + 2 * (jointCore dom (u 0) (u 1) line.1 line.2).card)
    {gamma beta theta : F}
    (hgamma : gamma ∈ family.G \ pointsOn family line)
    (hbeta : beta ∈ family.G \ pointsOn family line)
    (htheta : theta ∈ family.G \ pointsOn family line) :
    k - 1 <
      ((fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta)) ∩
        fullAgreement dom (u 0) (u 1) theta (family.q theta)).card := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let A : F → Finset ι := fun eta =>
    fullAgreement dom (u 0) (u 1) eta (family.q eta)
  let fresh : F → Finset ι := fun eta => A eta \ D
  let U : Finset ι := Finset.univ \ D
  have hdeg := lineParameter_degree_lt family hline
  have houtGamma := Finset.mem_sdiff.mp hgamma
  have houtBeta := Finset.mem_sdiff.mp hbeta
  have houtTheta := Finset.mem_sdiff.mp htheta
  have hoffGamma : family.q gamma ≠ line.1 + C gamma * line.2 := by
    intro heq
    apply houtGamma.2
    exact (mem_pointsOn_iff family line gamma).mpr ⟨houtGamma.1, heq⟩
  have hoffBeta : family.q beta ≠ line.1 + C beta * line.2 := by
    intro heq
    apply houtBeta.2
    exact (mem_pointsOn_iff family line beta).mpr ⟨houtBeta.1, heq⟩
  have hoffTheta : family.q theta ≠ line.1 + C theta * line.2 := by
    intro heq
    apply houtTheta.2
    exact (mem_pointsOn_iff family line theta).mpr ⟨houtTheta.1, heq⟩
  have hinterGamma : (A gamma ∩ D).card ≤ k - 1 := by
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
      (family.degree_lt gamma houtGamma.1) hdeg.1 hdeg.2 hoffGamma
  have hinterBeta : (A beta ∩ D).card ≤ k - 1 := by
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
      (family.degree_lt beta houtBeta.1) hdeg.1 hdeg.2 hoffBeta
  have hinterTheta : (A theta ∩ D).card ≤ k - 1 := by
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
      (family.degree_lt theta houtTheta.1) hdeg.1 hdeg.2 hoffTheta
  have hfreshGamma : t - (k - 1) ≤ (fresh gamma).card := by
    have hsplit := card_sdiff_add_card_inter (A gamma) D
    have hbig := hlarge gamma houtGamma.1
    change t ≤ (A gamma).card at hbig
    dsimp only [fresh]
    omega
  have hfreshBeta : t - (k - 1) ≤ (fresh beta).card := by
    have hsplit := card_sdiff_add_card_inter (A beta) D
    have hbig := hlarge beta houtBeta.1
    change t ≤ (A beta).card at hbig
    dsimp only [fresh]
    omega
  have hfreshTheta : t - (k - 1) ≤ (fresh theta).card := by
    have hsplit := card_sdiff_add_card_inter (A theta) D
    have hbig := hlarge theta houtTheta.1
    change t ≤ (A theta).card at hbig
    dsimp only [fresh]
    omega
  have hfreshSubset : ∀ eta, fresh eta ⊆ U := by
    intro eta i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hDcard : D.card ≤ Fintype.card ι := Finset.card_le_univ D
  have hUcard : U.card = Fintype.card ι - D.card := by
    dsimp only [U]
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  have htripleFresh : k - 1 <
      (((fresh gamma ∩ fresh beta) ∩ fresh theta).card) := by
    have htSub : t - (k - 1) + (k - 1) = t :=
      Nat.sub_add_cancel htd
    have hNSub : Fintype.card ι - D.card + D.card = Fintype.card ι :=
      Nat.sub_add_cancel hDcard
    change 2 * Fintype.card ι + 4 * (k - 1) <
      3 * t + 2 * D.card at hhigh
    have hgap : 2 * U.card + (k - 1) < 3 * (t - (k - 1)) := by
      rw [hUcard]
      omega
    exact three_set_inter_card_gt U (fresh gamma) (fresh beta) (fresh theta)
      (t - (k - 1)) (k - 1)
      (hfreshSubset gamma) (hfreshSubset beta) (hfreshSubset theta)
      hfreshGamma hfreshBeta hfreshTheta hgap
  have hsubset : (fresh gamma ∩ fresh beta) ∩ fresh theta ⊆
      (A gamma ∩ A beta) ∩ A theta := by
    intro i hi
    simp only [Finset.mem_inter, fresh, Finset.mem_sdiff] at hi ⊢
    exact ⟨⟨hi.1.1.1, hi.1.2.1⟩, hi.2.1⟩
  have hcard := Finset.card_le_card hsubset
  simpa only [A] using lt_of_lt_of_le htripleFresh hcard

/-- Three off-line points above a high core must be collinear. -/
theorem slopePolynomial_eq_of_outside_high_core
    {dom : ι ↪ F} {k t : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (htd : k - 1 ≤ t)
    (hlarge : ∀ gamma ∈ family.G,
      t ≤ (fullAgreement dom (u 0) (u 1) gamma
        (family.q gamma)).card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hhigh : 2 * Fintype.card ι + 4 * (k - 1) <
      3 * t + 2 * (jointCore dom (u 0) (u 1) line.1 line.2).card)
    {gamma beta theta : F} (hgb : gamma ≠ beta) (hgt : gamma ≠ theta)
    (hgamma : gamma ∈ family.G \ pointsOn family line)
    (hbeta : beta ∈ family.G \ pointsOn family line)
    (htheta : theta ∈ family.G \ pointsOn family line) :
    slopePolynomial gamma beta (family.q gamma) (family.q beta) =
      slopePolynomial gamma theta (family.q gamma) (family.q theta) := by
  by_contra hslope
  have hupper := triple_fullAgreement_card_le_pred_of_slope_ne
    dom (u 0) (u 1) hk hgb hgt
    (family.degree_lt gamma (Finset.mem_sdiff.mp hgamma).1)
    (family.degree_lt beta (Finset.mem_sdiff.mp hbeta).1)
    (family.degree_lt theta (Finset.mem_sdiff.mp htheta).1) hslope
  have hlower := triple_fullAgreement_card_gt_pred_of_outside_high_core
    family hk htd hlarge hline hhigh hgamma hbeta htheta
  omega

/-- **High-core collapse.** If every relevant line has at most `B` points
and the whole selected family has more than `2B` points, then every line core
satisfies the low-core inequality.  Otherwise all points lie in the union of
the original high-core line and one outsider secant. -/
theorem low_core_of_card_gt_two_mul_lineCap
    {dom : ι ↪ F} {k t B : ℕ} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (htd : k - 1 ≤ t)
    (hlarge : ∀ gamma ∈ family.G,
      t ≤ (fullAgreement dom (u 0) (u 1) gamma
        (family.q gamma)).card)
    (hlineCap : ∀ line ∈ lineParameters family,
      (pointsOn family line).card ≤ B)
    (hcard : 2 * B < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    3 * t +
        2 * (jointCore dom (u 0) (u 1) line.1 line.2).card ≤
      2 * Fintype.card ι + 4 * (k - 1) := by
  by_contra hnot
  have hhigh : 2 * Fintype.card ι + 4 * (k - 1) <
      3 * t +
        2 * (jointCore dom (u 0) (u 1) line.1 line.2).card := by
    omega
  let outside := family.G \ pointsOn family line
  have hlineCard := hlineCap line hline
  have hpointsSub := pointsOn_subset_G family line
  have houtCard : outside.card = family.G.card - (pointsOn family line).card := by
    dsimp only [outside]
    exact Finset.card_sdiff_of_subset hpointsSub
  have houtTwo : 1 < outside.card := by
    have hlineTwo := two_le_pointsOn_card_of_mem_lineParameters family hline
    have hBtwo : 2 ≤ B := hlineTwo.trans hlineCard
    omega
  obtain ⟨gamma, hgamma, beta, hbeta, hgb⟩ :=
    (Finset.one_lt_card.mp houtTwo)
  let secondLine := secantParameter family gamma beta
  have hgammaG := (Finset.mem_sdiff.mp hgamma).1
  have hbetaG := (Finset.mem_sdiff.mp hbeta).1
  have hsecondLine : secondLine ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgammaG hbetaG hgb
  have hsecondCap := hlineCap secondLine hsecondLine
  have houtsideSubset : outside ⊆ pointsOn family secondLine := by
    intro theta htheta
    by_cases htg : theta = gamma
    · subst theta
      exact first_point_mem_pointsOn_secant family (beta := beta) hgammaG
    by_cases htb : theta = beta
    · subst theta
      exact second_point_mem_pointsOn_secant family
        (gamma := gamma) hbetaG hgb
    · have hslope := slopePolynomial_eq_of_outside_high_core
        family hk htd hlarge hline hhigh hgb (Ne.symm htg) hgamma hbeta htheta
      have hthetaG := (Finset.mem_sdiff.mp htheta).1
      have hthird := third_point_on_secant_line_of_slope_eq
        (Ne.symm htg) hslope.symm
      exact (mem_pointsOn_iff family secondLine theta).mpr
        ⟨hthetaG, by simpa only [secondLine, secantParameter] using hthird⟩
  have hGsubset : family.G ⊆
      pointsOn family line ∪ pointsOn family secondLine := by
    intro theta htheta
    by_cases hthetaLine : theta ∈ pointsOn family line
    · exact Finset.mem_union_left _ hthetaLine
    · exact Finset.mem_union_right _ <|
        houtsideSubset (Finset.mem_sdiff.mpr ⟨htheta, hthetaLine⟩)
  have hcardUnion := Finset.card_le_card hGsubset
  have hunionLe := Finset.card_union_le
    (pointsOn family line) (pointsOn family secondLine)
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines.secantParameter_eq_of_mem_pointsOn
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines.pointsOn_card_mul_max_add_core_le
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines.sum_pointsOn_mul_pred_eq_G_mul_pred
