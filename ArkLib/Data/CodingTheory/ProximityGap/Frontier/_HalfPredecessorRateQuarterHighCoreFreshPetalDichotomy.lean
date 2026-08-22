/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCoreBandSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCollapsedClusterInjection

/-!
# Rate-quarter high cores: fresh-petal dichotomy

Fix two relevant decoded lines whose joint cores each contain half of the
domain.  Every other relevant half-core line then lies in their determinant-
collapsed cluster.  A nonzero difference of the two reference slope
polynomials vanishes at at most `k - 1` domain coordinates.  Consequently,
`k` fresh cross-core coordinates for each selected scalar supply a transverse
coordinate automatically, and the collapsed-cluster injection bounds the
family by the domain.

The final theorem records the exact remaining obstruction without a choice
function: unless the reference slope polynomials coincide or the family is
already domain-bounded, some selected scalar has at most `k - 1` fresh
coordinates against every relevant half-core target line.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Agreement coordinates of a point on `source` which lie in the target
line's joint core but outside the source line's own joint core. -/
noncomputable def freshCrossCore (dom : ι ↪ F) (u0 u1 : ι → F) (gamma : F)
    (source target : PolynomialLine F) : Finset ι :=
  (fullAgreement dom u0 u1 gamma
      (source.1 + C gamma * source.2) ∩
    jointCore dom u0 u1 target.1 target.2) \
      jointCore dom u0 u1 source.1 source.2

/-- The same fresh cross-core set, written using the polynomial selected by a
rich-point family. -/
noncomputable def familyFreshCrossCore
    {dom : ι ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (gamma : F)
    (source target : LineParameter F) : Finset ι :=
  (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
    jointCore dom (u 0) (u 1) target.1 target.2) \
      jointCore dom (u 0) (u 1) source.1 source.2

/-- If the selected point lies on `source`, the family and line forms of its
fresh cross-core set agree literally. -/
theorem familyFreshCrossCore_eq_freshCrossCore_of_mem_pointsOn
    {dom : ι ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) {gamma : F}
    (source target : LineParameter F)
    (hsource : gamma ∈ pointsOn family source) :
    familyFreshCrossCore family gamma source target =
      freshCrossCore dom (u 0) (u 1) gamma source target := by
  have hline := (mem_pointsOn_iff family source gamma).mp hsource |>.2
  simp only [familyFreshCrossCore, freshCrossCore, hline]

/-- `k` fresh coordinates avoid the zero set of any nonzero degree-`< k`
reference slope difference. -/
theorem exists_reference_transverse_mem_freshCrossCore
    (dom : ι ↪ F) (u0 u1 : ι → F) {k : Nat} (hk : 1 ≤ k)
    (line0 line1 source target : PolynomialLine F) (gamma : F)
    (href : line1.2 - line0.2 ≠ 0)
    (hrefDeg : (line1.2 - line0.2).natDegree < k)
    (hsupply : k ≤
      (freshCrossCore dom u0 u1 gamma source target).card) :
    ∃ i ∈ freshCrossCore dom u0 u1 gamma source target,
      (line1.2 - line0.2).eval (dom i) ≠ 0 := by
  by_contra hnone
  have hzero : ∀ i ∈ freshCrossCore dom u0 u1 gamma source target,
      (line1.2 - line0.2).eval (dom i) = 0 := by
    intro i hi
    by_contra hne
    exact hnone ⟨i, hi, hne⟩
  have hsub : freshCrossCore dom u0 u1 gamma source target ⊆
      Finset.univ.filter fun i =>
        (line1.2 - line0.2).eval (dom i) = 0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzero i hi
  have hroot := domain_root_card_le_pred dom hk
    (line1.2 - line0.2) href hrefDeg
  have hcard := Finset.card_le_card hsub
  omega

/-- **Collapsed-cluster injection from quantitative fresh supply.**  The
determinant hypotheses put every source and target line in one fixed cluster.
The degree bound on the reference slope difference converts `k` fresh petals
per scalar into a transverse coordinate assignment, hence an injection into
the domain. -/
theorem card_le_domain_of_collapsed_large_fresh_crossCores
    (dom : ι ↪ F) (u0 u1 : ι → F) (G : Finset F) {k : Nat}
    (hk : 1 ≤ k) (line0 line1 : PolynomialLine F)
    (source target : F → PolynomialLine F)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htarget : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (target gamma) = 0)
    (href : line1.2 - line0.2 ≠ 0)
    (hrefDeg : (line1.2 - line0.2).natDegree < k)
    (hsupply : ∀ gamma ∈ G, k ≤
      (freshCrossCore dom u0 u1 gamma
        (source gamma) (target gamma)).card) :
    G.card ≤ Fintype.card ι := by
  have hchoice : ∀ gamma ∈ G,
      ∃ i ∈ freshCrossCore dom u0 u1 gamma
          (source gamma) (target gamma),
        (line1.2 - line0.2).eval (dom i) ≠ 0 := by
    intro gamma hgamma
    exact exists_reference_transverse_mem_freshCrossCore
      dom u0 u1 hk line0 line1 (source gamma) (target gamma) gamma
        href hrefDeg (hsupply gamma hgamma)
  let coord : F → ι := fun gamma =>
    if hgamma : gamma ∈ G then
      Classical.choose (hchoice gamma hgamma)
    else
      Classical.choice (inferInstance : Nonempty ι)
  have hcoordSpec : ∀ gamma ∈ G,
      coord gamma ∈ freshCrossCore dom u0 u1 gamma
          (source gamma) (target gamma) ∧
        (line1.2 - line0.2).eval (dom (coord gamma)) ≠ 0 := by
    intro gamma hgamma
    simp only [coord, dif_pos hgamma]
    exact Classical.choose_spec (hchoice gamma hgamma)
  apply card_le_domain_of_collapsed_fresh_petals
    dom u0 u1 G line0 line1 source target coord hsource htarget
  · intro gamma hgamma
    exact (hcoordSpec gamma hgamma).2
  · intro gamma hgamma
    have hm := (hcoordSpec gamma hgamma).1
    rw [freshCrossCore] at hm
    exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hm).1).1
  · intro gamma hgamma
    have hm := (hcoordSpec gamma hgamma).1
    rw [freshCrossCore] at hm
    exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hm).1).2
  · intro gamma hgamma
    have hm := (hcoordSpec gamma hgamma).1
    rw [freshCrossCore] at hm
    exact (Finset.mem_sdiff.mp hm).2

/-- **Family-level high-core injection.**  Fix two relevant half-core reference
lines with different slope polynomials.  If each selected point lies on a
relevant half-core source line and has `k` fresh coordinates in some relevant
half-core target, then the family has at most the domain size.  Determinant
collapse for every chosen source and target is derived internally from the
three-half-core theorem. -/
theorem card_le_two_mul_of_half_core_fresh_target_supply
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (href : line1.2 - line0.2 ≠ 0)
    (source : F → LineParameter F)
    (hsourceLine : ∀ gamma ∈ family.G,
      source gamma ∈ lineParameters family)
    (hsourceCore : ∀ gamma ∈ family.G, h ≤
      (jointCore dom (u 0) (u 1)
        (source gamma).1 (source gamma).2).card)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma))
    (htargetSupply : ∀ gamma ∈ family.G,
      ∃ target ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card ∧
        k ≤ (familyFreshCrossCore family gamma
          (source gamma) target).card) :
    family.G.card ≤ 2 * h := by
  let target : F → LineParameter F := fun gamma =>
    if hgamma : gamma ∈ family.G then
      Classical.choose (htargetSupply gamma hgamma)
    else
      line0
  have htargetSpec : ∀ gamma ∈ family.G,
      target gamma ∈ lineParameters family ∧
        h ≤ (jointCore dom (u 0) (u 1)
          (target gamma).1 (target gamma).2).card ∧
        k ≤ (familyFreshCrossCore family gamma
          (source gamma) (target gamma)).card := by
    intro gamma hgamma
    simp only [target, dif_pos hgamma]
    exact Classical.choose_spec (htargetSupply gamma hgamma)
  have hrefDeg : (line1.2 - line0.2).natDegree < k := by
    have hdeg0 := lineParameter_degree_lt family hline0
    have hdeg1 := lineParameter_degree_lt family hline1
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt hdeg1.2 hdeg0.2)
  have hbound := card_le_domain_of_collapsed_large_fresh_crossCores
    dom (u 0) (u 1) family.G hk line0 line1 source target
      (fun gamma hgamma =>
        lineDeterminant_eq_zero_of_three_relevant_half_core_lines
          family hk hn hrate line0 line1 (source gamma)
            hline0 hline1 (hsourceLine gamma hgamma)
            hcore0 hcore1 (hsourceCore gamma hgamma))
      (fun gamma hgamma =>
        lineDeterminant_eq_zero_of_three_relevant_half_core_lines
          family hk hn hrate line0 line1 (target gamma)
            hline0 hline1 (htargetSpec gamma hgamma).1
            hcore0 hcore1 (htargetSpec gamma hgamma).2.1)
      href hrefDeg
      (fun gamma hgamma => by
        rw [← familyFreshCrossCore_eq_freshCrossCore_of_mem_pointsOn
          family (source gamma) (target gamma) (hsourceOn gamma hgamma)]
        exact (htargetSpec gamma hgamma).2.2)
  simpa only [hn] using hbound

/-- **Sharp high-core residual.**  With a transverse fixed reference pair,
either the family is domain-bounded or some selected scalar is starved against
every relevant half-core target: at most `k - 1` of its fresh source agreements
land in that target core. -/
theorem card_le_two_mul_or_exists_half_core_target_starved_scalar
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (href : line1.2 - line0.2 ≠ 0)
    (source : F → LineParameter F)
    (hsourceLine : ∀ gamma ∈ family.G,
      source gamma ∈ lineParameters family)
    (hsourceCore : ∀ gamma ∈ family.G, h ≤
      (jointCore dom (u 0) (u 1)
        (source gamma).1 (source gamma).2).card)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma)) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∀ target ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card →
          (familyFreshCrossCore family gamma
            (source gamma) target).card ≤ k - 1 := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  apply Or.inr
  by_contra hresidual
  have htargetSupply : ∀ gamma ∈ family.G,
      ∃ target ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card ∧
        k ≤ (familyFreshCrossCore family gamma
          (source gamma) target).card := by
    intro gamma hgamma
    by_contra hnone
    apply hresidual
    refine ⟨gamma, hgamma, ?_⟩
    intro target htargetLine htargetCore
    by_contra hnotSmall
    have hkFresh : k ≤
        (familyFreshCrossCore family gamma
          (source gamma) target).card := by
      omega
    exact hnone ⟨target, htargetLine, htargetCore, hkFresh⟩
  exact hcard <| card_le_two_mul_of_half_core_fresh_target_supply
    family hk hn hrate line0 line1 hline0 hline1 hcore0 hcore1 href
      source hsourceLine hsourceCore hsourceOn htargetSupply

/-- **Reference-degeneracy / bound / starvation trichotomy.**  This removes
the last transversality assumption from the high-core statement.  The only
additional branch is literal equality of the two reference slope polynomials. -/
theorem equal_reference_slope_or_card_le_or_exists_half_core_target_starved_scalar
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (source : F → LineParameter F)
    (hsourceLine : ∀ gamma ∈ family.G,
      source gamma ∈ lineParameters family)
    (hsourceCore : ∀ gamma ∈ family.G, h ≤
      (jointCore dom (u 0) (u 1)
        (source gamma).1 (source gamma).2).card)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma)) :
    line1.2 = line0.2 ∨ family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∀ target ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card →
          (familyFreshCrossCore family gamma
            (source gamma) target).card ≤ k - 1 := by
  by_cases href : line1.2 = line0.2
  · exact Or.inl href
  · exact Or.inr <|
      card_le_two_mul_or_exists_half_core_target_starved_scalar
        family hk hn hrate line0 line1 hline0 hline1 hcore0 hcore1
          (sub_ne_zero.mpr href) source hsourceLine hsourceCore hsourceOn

/-- **High-core cover / starvation decomposition.**  Fixing two relevant
half-core reference lines is enough to remove every global choice function
from the conclusion.  One of four explicit outcomes holds:

* the two reference slope polynomials coincide;
* the family is bounded by the domain;
* some selected scalar lies on no relevant half-core line; or
* some selected scalar lies on a relevant half-core source but has at most
  `k - 1` fresh coordinates in every relevant half-core target.

Thus the nondegenerate high-core branch reduces exactly to a line-cover
failure or a universal cross-core starvation witness. -/
theorem equal_reference_slope_or_card_le_or_uncovered_or_starved_scalar
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    line1.2 = line0.2 ∨ family.G.card ≤ 2 * h ∨
      (∃ gamma ∈ family.G, ∀ source ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) source.1 source.2).card →
          gamma ∉ pointsOn family source) ∨
      ∃ gamma ∈ family.G, ∃ source ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) source.1 source.2).card ∧
        gamma ∈ pointsOn family source ∧
        ∀ target ∈ lineParameters family,
          h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card →
            (familyFreshCrossCore family gamma source target).card ≤ k - 1 := by
  by_cases href : line1.2 = line0.2
  · exact Or.inl href
  apply Or.inr
  by_cases hcoverage : ∀ gamma ∈ family.G,
      ∃ source ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) source.1 source.2).card ∧
        gamma ∈ pointsOn family source
  · let source : F → LineParameter F := fun gamma =>
      if hgamma : gamma ∈ family.G then
        Classical.choose (hcoverage gamma hgamma)
      else
        line0
    have hsourceSpec : ∀ gamma ∈ family.G,
        source gamma ∈ lineParameters family ∧
          h ≤ (jointCore dom (u 0) (u 1)
            (source gamma).1 (source gamma).2).card ∧
          gamma ∈ pointsOn family (source gamma) := by
      intro gamma hgamma
      simp only [source, dif_pos hgamma]
      exact Classical.choose_spec (hcoverage gamma hgamma)
    rcases card_le_two_mul_or_exists_half_core_target_starved_scalar
        family hk hn hrate line0 line1 hline0 hline1 hcore0 hcore1
          (sub_ne_zero.mpr href) source
          (fun gamma hgamma => (hsourceSpec gamma hgamma).1)
          (fun gamma hgamma => (hsourceSpec gamma hgamma).2.1)
          (fun gamma hgamma => (hsourceSpec gamma hgamma).2.2) with
      hcard | ⟨gamma, hgamma, hstarved⟩
    · exact Or.inl hcard
    · apply Or.inr
      apply Or.inr
      exact ⟨gamma, hgamma, source gamma,
        (hsourceSpec gamma hgamma).1,
        (hsourceSpec gamma hgamma).2.1,
        (hsourceSpec gamma hgamma).2.2, hstarved⟩
  · apply Or.inr
    apply Or.inl
    have hnocovered : ∃ gamma ∈ family.G,
        ¬ ∃ source ∈ lineParameters family,
          h ≤ (jointCore dom (u 0) (u 1) source.1 source.2).card ∧
          gamma ∈ pointsOn family source := by
      by_contra hnone
      apply hcoverage
      intro gamma hgamma
      by_contra hgammaNone
      exact hnone ⟨gamma, hgamma, hgammaNone⟩
    obtain ⟨gamma, hgamma, hgammaUncovered⟩ := hnocovered
    refine ⟨gamma, hgamma, ?_⟩
    intro source hsourceLine hsourceCore hsourceOn
    exact hgammaUncovered
      ⟨source, hsourceLine, hsourceCore, hsourceOn⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy
#print axioms exists_reference_transverse_mem_freshCrossCore
#print axioms card_le_domain_of_collapsed_large_fresh_crossCores
#print axioms card_le_two_mul_of_half_core_fresh_target_supply
#print axioms card_le_two_mul_or_exists_half_core_target_starved_scalar
#print axioms equal_reference_slope_or_card_le_or_exists_half_core_target_starved_scalar
#print axioms equal_reference_slope_or_card_le_or_uncovered_or_starved_scalar
