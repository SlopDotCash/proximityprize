/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCorePacking

/-!
# Large-core collapse for the half-predecessor rich-point family

This file formalizes the large-joint-core branch of the rate-`1/16`
half-predecessor incidence argument.  For a determined polynomial line, it
splits the selected bad-scalar rich points into the points on that line and
the points outside it.

For an outside point, the root bound caps its agreement with the line core by
`k-1`.  If the core satisfies the strict large-core inequality, Bonferroni on
three fresh agreement sets forces their triple intersection to have more than
`k-1` coordinates.  The noncollinear-triple root bound then forces equality of
the two secant slopes.  Consequently every outside point lies on the canonical
secant line through any two distinct outside points.

The line-core packing theorem bounds both the original determined line and
this secant line by `h` points.  Thus a family of more than `2h` points cannot
have such a large determined-line core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Scalars in the rich-point family but outside a polynomial line. -/
noncomputable def outsideLine
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) : Finset F :=
  family.G.filter fun gamma =>
    family.q gamma ≠ line.1 + C gamma * line.2

@[simp]
theorem mem_outsideLine_iff
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) (gamma : F) :
    gamma ∈ outsideLine family line ↔
      gamma ∈ family.G ∧
        family.q gamma ≠ line.1 + C gamma * line.2 := by
  simp only [outsideLine, Finset.mem_filter]

/-- The points on a line and the outside points partition the rich family. -/
theorem pointsOn_card_add_outsideLine_card
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) :
    (pointsOn family line).card + (outsideLine family line).card =
      family.G.card := by
  simpa only [pointsOn, outsideLine] using
    (Finset.card_filter_add_card_filter_not
      (s := family.G)
      (p := fun gamma => family.q gamma = line.1 + C gamma * line.2))

/-- An outside point has at least `threshold-(k-1)` agreements away from the
given line core.  This combines richness with the off-line root cap `(L3)`. -/
theorem threshold_sub_pred_le_fresh_card
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) (hk : 1 ≤ k)
    (hline : line ∈ lineParameters family)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ - (k - 1) ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
        jointCore dom (u 0) (u 1) line.1 line.2).card := by
  have hgammaData := (mem_outsideLine_iff family line gamma).mp hgamma
  have hdeg := lineParameter_degree_lt family hline
  have hcap := fullAgreement_inter_jointCore_card_le
    dom (u 0) (u 1) hk
    (family.degree_lt gamma hgammaData.1) hdeg.1 hdeg.2 hgammaData.2
  have hlarge := family.threshold_le gamma hgammaData.1
  rw [Finset.card_sdiff, Finset.inter_comm
    (jointCore dom (u 0) (u 1) line.1 line.2)]
  exact (Nat.sub_le_sub_right hlarge (k - 1)).trans
    (Nat.sub_le_sub_left hcap
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)

/-- Every determined polynomial line has at most `h` points at agreement
threshold at least `h+1` in a domain of size `2h`. -/
theorem pointsOn_card_le_half
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    (pointsOn family line).card ≤ h := by
  have hdeg := lineParameter_degree_lt family hline
  have hG := pointsOn_subset_G family line
  have hidentity : ∀ gamma ∈ pointsOn family line,
      family.q gamma = line.1 + C gamma * line.2 := by
    intro gamma hgamma
    exact (mem_pointsOn_iff family line gamma).mp hgamma |>.2
  have hlarge : ∀ gamma ∈ pointsOn family line,
      h + 1 ≤ (fullAgreement dom (u 0) (u 1) gamma
        (line.1 + C gamma * line.2)).card := by
    intro gamma hgamma
    exact hthreshold.trans <|
      family.line_hlarge line.1 line.2 (pointsOn family line)
        hG hidentity gamma hgamma
  have hproper := family.line_hproper
    line.1 line.2 (pointsOn family line)
    hdeg.1 hdeg.2 hG hidentity
  have hpacking := line_card_mul_max_add_core_le
    dom (u 0) (u 1) line.1 line.2
    (pointsOn family line) (h + 1) hlarge hproper
  rw [hn] at hpacking
  exact line_card_le_half_of_packing hpacking

/-- **Large-core triple collapse.** For three outside points with distinct
base scalar, Bonferroni forces more than `k-1` common fresh agreements.  Hence
the two secant slopes are equal by the noncollinear-triple root cap `(T1)`.

The strict core hypothesis is the subtraction-free form of
`2*|D| > h + 4*(k-1) - 3`. -/
theorem outside_triple_slope_eq_of_largeCore
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ outsideLine family line)
    (hgamma2 : gamma2 ∈ outsideLine family line)
    (hgamma3 : gamma3 ∈ outsideLine family line)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (hcore : h + 4 * (k - 1) <
      2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3) :
    slopePolynomial gamma1 gamma2 (family.q gamma1) (family.q gamma2) =
      slopePolynomial gamma1 gamma3 (family.q gamma1) (family.q gamma3) := by
  let A : F → Finset ι := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D : Finset ι := jointCore dom (u 0) (u 1) line.1 line.2
  let fresh : F → Finset ι := fun gamma => A gamma \ D
  let U : Finset ι := Finset.univ \ D
  have hgamma1G := (mem_outsideLine_iff family line gamma1).mp hgamma1 |>.1
  have hgamma2G := (mem_outsideLine_iff family line gamma2).mp hgamma2 |>.1
  have hgamma3G := (mem_outsideLine_iff family line gamma3).mp hgamma3 |>.1
  have hfreshLower : ∀ gamma ∈ outsideLine family line,
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ - (k - 1) ≤
        (fresh gamma).card := by
    intro gamma hgamma
    simpa only [fresh, A, D] using
      threshold_sub_pred_le_fresh_card family line hk hline hgamma
  have h1 : h + 1 - (k - 1) ≤ (fresh gamma1).card :=
    (Nat.sub_le_sub_right hthreshold (k - 1)).trans
      (hfreshLower gamma1 hgamma1)
  have h2 : h + 1 - (k - 1) ≤ (fresh gamma2).card :=
    (Nat.sub_le_sub_right hthreshold (k - 1)).trans
      (hfreshLower gamma2 hgamma2)
  have h3 : h + 1 - (k - 1) ≤ (fresh gamma3).card :=
    (Nat.sub_le_sub_right hthreshold (k - 1)).trans
      (hfreshLower gamma3 hgamma3)
  have hfreshU : ∀ gamma : F, fresh gamma ⊆ U := by
    intro gamma i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hUcard : U.card = 2 * h -
      (jointCore dom (u 0) (u 1) line.1 line.2).card := by
    calc
      U.card = Fintype.card ι -
          (jointCore dom (u 0) (u 1) line.1 line.2).card := by
        dsimp only [U, D]
        rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
      _ = 2 * h -
          (jointCore dom (u 0) (u 1) line.1 line.2).card := by rw [hn]
  have hz : (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 2 * h := by
    have := Finset.card_le_univ
      (jointCore dom (u 0) (u 1) line.1 line.2)
    rw [hn] at this
    exact this
  have hd : k - 1 ≤ h := by
    omega
  have hgap :
      2 * U.card + (k - 1) < 3 * (h + 1 - (k - 1)) := by
    rw [hUcard]
    omega
  have htriple :
      k - 1 < ((fresh gamma1 ∩ fresh gamma2) ∩ fresh gamma3).card := by
    exact three_set_inter_card_gt
      U (fresh gamma1) (fresh gamma2) (fresh gamma3)
      (h + 1 - (k - 1)) (k - 1)
      (hfreshU gamma1) (hfreshU gamma2) (hfreshU gamma3)
      h1 h2 h3 hgap
  by_contra hslope
  have hcap := triple_fullAgreement_card_le_pred_of_slope_ne
    dom (u 0) (u 1) hk h12 h13
    (family.degree_lt gamma1 hgamma1G)
    (family.degree_lt gamma2 hgamma2G)
    (family.degree_lt gamma3 hgamma3G) hslope
  have hsub :
      (fresh gamma1 ∩ fresh gamma2) ∩ fresh gamma3 ⊆
        (A gamma1 ∩ A gamma2) ∩ A gamma3 := by
    intro i hi
    rw [Finset.mem_inter, Finset.mem_inter] at hi ⊢
    exact ⟨⟨(Finset.mem_sdiff.mp hi.1.1).1,
      (Finset.mem_sdiff.mp hi.1.2).1⟩,
      (Finset.mem_sdiff.mp hi.2).1⟩
  have hcardSub := Finset.card_le_card hsub
  dsimp only [A] at hcap hcardSub
  omega

/-- **Secant-line containment.** Under the large-core inequality, every point
outside the original line lies on the canonical secant through any two
distinct outside points. -/
theorem outsideLine_subset_pointsOn_secant_of_largeCore
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma1 gamma2 : F}
    (hgamma1 : gamma1 ∈ outsideLine family line)
    (hgamma2 : gamma2 ∈ outsideLine family line)
    (h12 : gamma1 ≠ gamma2)
    (hcore : h + 4 * (k - 1) <
      2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3) :
    outsideLine family line ⊆
      pointsOn family (secantParameter family gamma1 gamma2) := by
  intro gamma hgamma
  have hgammaG := (mem_outsideLine_iff family line gamma).mp hgamma |>.1
  by_cases hgamma1eq : gamma = gamma1
  · subst gamma
    exact first_point_mem_pointsOn_secant family
      ((mem_outsideLine_iff family line gamma1).mp hgamma1 |>.1)
  by_cases hgamma2eq : gamma = gamma2
  · subst gamma
    exact second_point_mem_pointsOn_secant family
      ((mem_outsideLine_iff family line gamma2).mp hgamma2 |>.1) h12
  · have h13 : gamma1 ≠ gamma := fun h => hgamma1eq h.symm
    have hslope := outside_triple_slope_eq_of_largeCore
      family hk hn hthreshold hline
      hgamma1 hgamma2 hgamma h12 h13 hcore
    rw [mem_pointsOn_iff]
    refine ⟨hgammaG, ?_⟩
    simpa only [secantParameter] using
      (third_point_on_secant_line_of_slope_eq h13 hslope.symm)

/-- If two distinct outside points exist, the original line and their secant
cover the whole rich-point family, so the two line-packing bounds give
`|G| <= 2h`. -/
theorem card_le_two_mul_of_largeCore_and_two_outside
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma1 gamma2 : F}
    (hgamma1 : gamma1 ∈ outsideLine family line)
    (hgamma2 : gamma2 ∈ outsideLine family line)
    (h12 : gamma1 ≠ gamma2)
    (hcore : h + 4 * (k - 1) <
      2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3) :
    family.G.card ≤ 2 * h := by
  have hgamma1G := (mem_outsideLine_iff family line gamma1).mp hgamma1 |>.1
  have hgamma2G := (mem_outsideLine_iff family line gamma2).mp hgamma2 |>.1
  have hsecantLine := secantParameter_mem_lineParameters
    family hgamma1G hgamma2G h12
  have houtSub := outsideLine_subset_pointsOn_secant_of_largeCore
    family hk hn hthreshold hline hgamma1 hgamma2 h12 hcore
  have hfirst := pointsOn_card_le_half family hn hthreshold hline
  have hsecond := pointsOn_card_le_half
    family hn hthreshold hsecantLine
  have hout : (outsideLine family line).card ≤ h :=
    (Finset.card_le_card houtSub).trans hsecond
  have hpartition := pointsOn_card_add_outsideLine_card family line
  omega

/-- **Large-core branch closed.** If `|G|>2h`, the outside set contains two
distinct points because the original line has at most `h` points.  Their
canonical secant contains every outside point, and the two line bounds
contradict `|G|>2h`. -/
theorem largeCore_contradiction_of_card_gt_two_mul
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcard : 2 * h < family.G.card)
    (hcore : h + 4 * (k - 1) <
      2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3) :
    False := by
  have hlineCard := pointsOn_card_le_half family hn hthreshold hline
  have hpartition := pointsOn_card_add_outsideLine_card family line
  have houtside : 1 < (outsideLine family line).card := by omega
  obtain ⟨gamma1, hgamma1, gamma2, hgamma2, h12⟩ :=
    Finset.one_lt_card.mp houtside
  have hle := card_le_two_mul_of_largeCore_and_two_outside
    family hk hn hthreshold hline hgamma1 hgamma2 h12 hcore
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse.outside_triple_slope_eq_of_largeCore
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse.outsideLine_subset_pointsOn_secant_of_largeCore
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse.largeCore_contradiction_of_card_gt_two_mul
