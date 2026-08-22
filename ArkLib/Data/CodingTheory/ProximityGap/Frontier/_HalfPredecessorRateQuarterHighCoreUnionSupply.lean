/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy

/-!
# Rate-quarter high cores: aggregate union supply

The one-target fresh-petal dichotomy asks for `k` fresh coordinates in a
single target core.  This file replaces that local requirement by aggregate
supply across the union of all relevant half-domain cores.  Since the fixed
reference slope difference has at most `k - 1` domain roots, `k` aggregate
fresh coordinates contain a transverse coordinate in some target core.

There is also a sharper set-theoretic form.  For a selected point on a source
line, the only coordinates which cannot supply the collapsed-cluster
injection are

* coordinates in the source core;
* roots of the fixed reference slope difference; and
* coordinates missed by the union of all relevant half-domain cores.

If their union is smaller than the point's agreement set, a transverse target
coordinate exists directly.  The final theorem derives this condition from a
full high-core union, exact half-sized cores, and containment of the reference
singular locus.  These are explicit global residual assumptions; no
one-target supply function remains.
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

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Relevant decoded lines whose joint core contains at least half of a
`2h`-coordinate domain. -/
noncomputable def highCoreLines
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ) :
    Finset (LineParameter F) :=
  (lineParameters family).filter fun line =>
    h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card

@[simp]
theorem mem_highCoreLines_iff
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ)
    (line : LineParameter F) :
    line ∈ highCoreLines family h ↔
      line ∈ lineParameters family ∧
        h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  simp only [highCoreLines, Finset.mem_filter]

/-- Union of every relevant half-domain line core. -/
noncomputable def highCoreUnion
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ) : Finset I :=
  (highCoreLines family h).biUnion fun line =>
    jointCore dom (u 0) (u 1) line.1 line.2

/-- Domain coordinates where the fixed reference slope difference vanishes. -/
noncomputable def referenceSingularCoordinates
    (dom : I ↪ F) (line0 line1 : LineParameter F) : Finset I :=
  Finset.univ.filter fun i =>
    (line1.2 - line0.2).eval (dom i) = 0

/-- Aggregate fresh agreements carried by some relevant half-domain core. -/
noncomputable def aggregateHighCoreFresh
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ)
    (gamma : F) (source : LineParameter F) : Finset I :=
  (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
      highCoreUnion family h) \
    jointCore dom (u 0) (u 1) source.1 source.2

/-- The exact global obstruction to a transverse cross-core coordinate. -/
noncomputable def highCoreTransverseForbidden
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ)
    (line0 line1 source : LineParameter F) : Finset I :=
  (jointCore dom (u 0) (u 1) source.1 source.2 ∪
      referenceSingularCoordinates dom line0 line1) ∪
    (Finset.univ \ highCoreUnion family h)

/-- Membership in a high core puts its coordinates in the aggregate union. -/
theorem jointCore_subset_highCoreUnion
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ)
    {line : LineParameter F} (hline : line ∈ highCoreLines family h) :
    jointCore dom (u 0) (u 1) line.1 line.2 ⊆
      highCoreUnion family h := by
  intro i hi
  simp only [highCoreUnion, Finset.mem_biUnion]
  exact ⟨line, hline, hi⟩

/-- A point outside the explicit forbidden union supplies a transverse
coordinate in some relevant half-core target. -/
theorem exists_transverse_target_of_forbidden_card_lt
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ)
    (line0 line1 source : LineParameter F) (gamma : F)
    (hroom :
      (highCoreTransverseForbidden family h line0 line1 source).card <
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    ∃ i : I, ∃ target : LineParameter F,
      target ∈ highCoreLines family h ∧
      (line1.2 - line0.2).eval (dom i) ≠ 0 ∧
      i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
      i ∈ jointCore dom (u 0) (u 1) target.1 target.2 ∧
      i ∉ jointCore dom (u 0) (u 1) source.1 source.2 := by
  classical
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let B := highCoreTransverseForbidden family h line0 line1 source
  have hnsub : ¬ A ⊆ B := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    change B.card < A.card at hroom
    omega
  simp only [Finset.not_subset] at hnsub
  obtain ⟨i, hiA, hiB⟩ := hnsub
  have hiRaw :
      (i ∉ jointCore dom (u 0) (u 1) source.1 source.2 ∧
        (line1.2 - line0.2).eval (dom i) ≠ 0) ∧
      i ∈ highCoreUnion family h := by
    simpa only [B, highCoreTransverseForbidden,
      referenceSingularCoordinates, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_sdiff, not_or, not_and,
      not_not] using hiB
  have hiData :
      i ∉ jointCore dom (u 0) (u 1) source.1 source.2 ∧
      (line1.2 - line0.2).eval (dom i) ≠ 0 ∧
      i ∈ highCoreUnion family h := by
    exact ⟨hiRaw.1.1, hiRaw.1.2, hiRaw.2⟩
  have hiUnion : i ∈ (highCoreLines family h).biUnion fun line =>
      jointCore dom (u 0) (u 1) line.1 line.2 := by
    simpa only [highCoreUnion] using hiData.2.2
  obtain ⟨target, htarget, hiTarget⟩ := Finset.mem_biUnion.mp hiUnion
  exact ⟨i, target, htarget, hiData.2.1,
    by simpa only [A] using hiA, hiTarget, hiData.1⟩

/-- `k` aggregate fresh coordinates across all high cores avoid the at most
`k-1` roots of a nonzero degree-`<k` reference slope difference. -/
theorem exists_transverse_target_of_aggregateHighCoreFresh
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ)
    (hk : 1 ≤ k) (line0 line1 source : LineParameter F) (gamma : F)
    (href : line1.2 - line0.2 ≠ 0)
    (hrefDeg : (line1.2 - line0.2).natDegree < k)
    (hsupply : k ≤
      (aggregateHighCoreFresh family h gamma source).card) :
    ∃ i : I, ∃ target : LineParameter F,
      target ∈ highCoreLines family h ∧
      (line1.2 - line0.2).eval (dom i) ≠ 0 ∧
      i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
      i ∈ jointCore dom (u 0) (u 1) target.1 target.2 ∧
      i ∉ jointCore dom (u 0) (u 1) source.1 source.2 := by
  classical
  let T := aggregateHighCoreFresh family h gamma source
  let R := referenceSingularCoordinates dom line0 line1
  have hroot : R.card ≤ k - 1 := by
    simpa only [R, referenceSingularCoordinates] using
      domain_root_card_le_pred dom hk (line1.2 - line0.2) href hrefDeg
  have hnsub : ¬ T ⊆ R := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    change k ≤ T.card at hsupply
    omega
  simp only [Finset.not_subset] at hnsub
  obtain ⟨i, hiT, hiR⟩ := hnsub
  have hiTRaw :
      (i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
        i ∈ highCoreUnion family h) ∧
      i ∉ jointCore dom (u 0) (u 1) source.1 source.2 := by
    simpa only [T, aggregateHighCoreFresh, Finset.mem_sdiff,
      Finset.mem_inter] using hiT
  have hiT' :
      i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
      i ∈ highCoreUnion family h ∧
      i ∉ jointCore dom (u 0) (u 1) source.1 source.2 := by
    exact ⟨hiTRaw.1.1, hiTRaw.1.2, hiTRaw.2⟩
  have hiRef : (line1.2 - line0.2).eval (dom i) ≠ 0 := by
    simpa only [R, referenceSingularCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and, not_not] using hiR
  have hiUnion : i ∈ (highCoreLines family h).biUnion fun line =>
      jointCore dom (u 0) (u 1) line.1 line.2 := by
    simpa only [highCoreUnion] using hiT'.2.1
  obtain ⟨target, htarget, hiTarget⟩ := Finset.mem_biUnion.mp hiUnion
  exact ⟨i, target, htarget, hiRef, hiT'.1, hiTarget, hiT'.2.2⟩

/-- A numerical union-coverage inequality supplies `k` aggregate fresh
coordinates.  The loss is exactly the source-core size plus the number of
coordinates missed by all high cores. -/
theorem aggregateHighCoreFresh_card_ge_of_union_slack
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : ℕ)
    (gamma : F) (source : LineParameter F)
    (hslack :
      (jointCore dom (u 0) (u 1) source.1 source.2).card +
          (Finset.univ \ highCoreUnion family h).card + k ≤
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    k ≤ (aggregateHighCoreFresh family h gamma source).card := by
  classical
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let S := jointCore dom (u 0) (u 1) source.1 source.2
  let M := Finset.univ \ highCoreUnion family h
  let T := aggregateHighCoreFresh family h gamma source
  have hsub : A ⊆ (S ∪ M) ∪ T := by
    intro i hiA
    by_cases hiS : i ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hiS)
    by_cases hiU : i ∈ highCoreUnion family h
    · apply Finset.mem_union_right
      simp only [T, aggregateHighCoreFresh, Finset.mem_sdiff,
        Finset.mem_inter]
      exact ⟨⟨by simpa only [A] using hiA, hiU⟩,
        by simpa only [S] using hiS⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hiU
  have hcardA := Finset.card_le_card hsub
  have hcardUnion := Finset.card_union_le (S ∪ M) T
  have hcardSM := Finset.card_union_le S M
  change S.card + M.card + k ≤ A.card at hslack
  change k ≤ T.card
  omega

/-! ## Family-level closures -/

/-- A transverse high-core target coordinate for every selected scalar closes
the whole family.  Determinant collapse of each chosen source and target is
derived internally from the two fixed half-core reference lines. -/
theorem card_le_two_mul_of_transverse_high_core_supply
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h)
    (source : F → LineParameter F)
    (hsource : ∀ gamma ∈ family.G,
      source gamma ∈ highCoreLines family h)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma))
    (hsupply : ∀ gamma ∈ family.G,
      ∃ i : I, ∃ target : LineParameter F,
        target ∈ highCoreLines family h ∧
        (line1.2 - line0.2).eval (dom i) ≠ 0 ∧
        i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
        i ∈ jointCore dom (u 0) (u 1) target.1 target.2 ∧
        i ∉ jointCore dom (u 0) (u 1)
          (source gamma).1 (source gamma).2) :
    family.G.card ≤ 2 * h := by
  classical
  have hw : ∀ gamma ∈ family.G,
      ∃ p : I × LineParameter F,
        p.2 ∈ highCoreLines family h ∧
        (line1.2 - line0.2).eval (dom p.1) ≠ 0 ∧
        p.1 ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
        p.1 ∈ jointCore dom (u 0) (u 1) p.2.1 p.2.2 ∧
        p.1 ∉ jointCore dom (u 0) (u 1)
          (source gamma).1 (source gamma).2 := by
    intro gamma hgamma
    obtain ⟨i, target, htarget, href, hagree, htargetCore, hfresh⟩ :=
      hsupply gamma hgamma
    exact ⟨(i, target), htarget, href, hagree, htargetCore, hfresh⟩
  let picked : F → I × LineParameter F := fun gamma =>
    if hgamma : gamma ∈ family.G then
      Classical.choose (hw gamma hgamma)
    else
      (Classical.choice (inferInstance : Nonempty I), line0)
  let coord : F → I := fun gamma => (picked gamma).1
  let target : F → LineParameter F := fun gamma => (picked gamma).2
  have hpicked : ∀ gamma ∈ family.G,
      target gamma ∈ highCoreLines family h ∧
      (line1.2 - line0.2).eval (dom (coord gamma)) ≠ 0 ∧
      coord gamma ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
      coord gamma ∈ jointCore dom (u 0) (u 1)
        (target gamma).1 (target gamma).2 ∧
      coord gamma ∉ jointCore dom (u 0) (u 1)
        (source gamma).1 (source gamma).2 := by
    intro gamma hgamma
    simpa only [target, coord, picked, dif_pos hgamma] using
      (Classical.choose_spec (hw gamma hgamma))
  have hline0' := (mem_highCoreLines_iff family h line0).mp hline0
  have hline1' := (mem_highCoreLines_iff family h line1).mp hline1
  rw [← hn]
  apply card_le_domain_of_collapsed_fresh_petals
    dom (u 0) (u 1) family.G line0 line1 source target coord
  · intro gamma hgamma
    have hsource' :=
      (mem_highCoreLines_iff family h (source gamma)).mp
        (hsource gamma hgamma)
    exact lineDeterminant_eq_zero_of_three_relevant_half_core_lines
      family hk hn hrate line0 line1 (source gamma)
        hline0'.1 hline1'.1 hsource'.1
        hline0'.2 hline1'.2 hsource'.2
  · intro gamma hgamma
    have htarget' :=
      (mem_highCoreLines_iff family h (target gamma)).mp
        (hpicked gamma hgamma).1
    exact lineDeterminant_eq_zero_of_three_relevant_half_core_lines
      family hk hn hrate line0 line1 (target gamma)
        hline0'.1 hline1'.1 htarget'.1
        hline0'.2 hline1'.2 htarget'.2
  · intro gamma hgamma
    exact (hpicked gamma hgamma).2.1
  · intro gamma hgamma
    have hline := (mem_pointsOn_iff family (source gamma) gamma).mp
      (hsourceOn gamma hgamma) |>.2
    simpa only [hline] using (hpicked gamma hgamma).2.2.1
  · intro gamma hgamma
    exact (hpicked gamma hgamma).2.2.2.1
  · intro gamma hgamma
    exact (hpicked gamma hgamma).2.2.2.2

/-- Aggregate fresh supply across all high cores is enough; no single target
core needs to carry `k` fresh coordinates. -/
theorem card_le_two_mul_of_aggregate_high_core_fresh_supply
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h)
    (href : line1.2 - line0.2 ≠ 0)
    (source : F → LineParameter F)
    (hsource : ∀ gamma ∈ family.G,
      source gamma ∈ highCoreLines family h)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma))
    (hsupply : ∀ gamma ∈ family.G, k ≤
      (aggregateHighCoreFresh family h gamma (source gamma)).card) :
    family.G.card ≤ 2 * h := by
  have hdeg0 := lineParameter_degree_lt family
    ((mem_highCoreLines_iff family h line0).mp hline0).1
  have hdeg1 := lineParameter_degree_lt family
    ((mem_highCoreLines_iff family h line1).mp hline1).1
  have hrefDeg : (line1.2 - line0.2).natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt hdeg1.2 hdeg0.2)
  apply card_le_two_mul_of_transverse_high_core_supply
    family hk hn hrate line0 line1 hline0 hline1 source hsource hsourceOn
  intro gamma hgamma
  exact exists_transverse_target_of_aggregateHighCoreFresh
    family h hk line0 line1 (source gamma) gamma href hrefDeg
      (hsupply gamma hgamma)

/-- The exact forbidden-union criterion closes both the uncovered and starved
branches at once. -/
theorem card_le_two_mul_of_high_core_forbidden_lt_agreement
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h)
    (source : F → LineParameter F)
    (hsource : ∀ gamma ∈ family.G,
      source gamma ∈ highCoreLines family h)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma))
    (hroom : ∀ gamma ∈ family.G,
      (highCoreTransverseForbidden family h line0 line1
          (source gamma)).card <
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    family.G.card ≤ 2 * h := by
  apply card_le_two_mul_of_transverse_high_core_supply
    family hk hn hrate line0 line1 hline0 hline1 source hsource hsourceOn
  intro gamma hgamma
  exact exists_transverse_target_of_forbidden_card_lt
    family h line0 line1 (source gamma) gamma (hroom gamma hgamma)

/-- A checkable cardinal inequality implies aggregate supply and therefore
closes the family.  It measures exactly the agreement slack beyond the source
core and the coordinates missed by the high-core union. -/
theorem card_le_two_mul_of_high_core_union_slack
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h)
    (href : line1.2 - line0.2 ≠ 0)
    (source : F → LineParameter F)
    (hsource : ∀ gamma ∈ family.G,
      source gamma ∈ highCoreLines family h)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma))
    (hslack : ∀ gamma ∈ family.G,
      (jointCore dom (u 0) (u 1)
          (source gamma).1 (source gamma).2).card +
          (Finset.univ \ highCoreUnion family h).card + k ≤
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    family.G.card ≤ 2 * h := by
  apply card_le_two_mul_of_aggregate_high_core_fresh_supply
    family hk hn hrate line0 line1 hline0 hline1 href
      source hsource hsourceOn
  intro gamma hgamma
  exact aggregateHighCoreFresh_card_ge_of_union_slack
    family h gamma (source gamma) (hslack gamma hgamma)

/-- **Full-union exact-core closure.**  Suppose every selected scalar lies on
a relevant half-core line, all such source cores have size at most `h`, their
union covers the domain, and every source core contains the singular locus of
the fixed reference pair.  Richness at `h+1` then puts an agreement coordinate
outside the exact half-core and outside the singular locus.  That coordinate
lies in another high core, so the family has at most `2h` scalars. -/
theorem card_le_two_mul_of_full_high_core_union_and_singular_containment
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊)
    (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h)
    (hpointCover : ∀ gamma ∈ family.G,
      ∃ source ∈ highCoreLines family h,
        gamma ∈ pointsOn family source)
    (hcoreUpper : ∀ source ∈ highCoreLines family h,
      (jointCore dom (u 0) (u 1) source.1 source.2).card ≤ h)
    (hunion : highCoreUnion family h = Finset.univ)
    (hsingular : ∀ source ∈ highCoreLines family h,
      referenceSingularCoordinates dom line0 line1 ⊆
        jointCore dom (u 0) (u 1) source.1 source.2) :
    family.G.card ≤ 2 * h := by
  classical
  let source : F → LineParameter F := fun gamma =>
    if hgamma : gamma ∈ family.G then
      Classical.choose (hpointCover gamma hgamma)
    else
      line0
  have hsourceSpec : ∀ gamma ∈ family.G,
      source gamma ∈ highCoreLines family h ∧
      gamma ∈ pointsOn family (source gamma) := by
    intro gamma hgamma
    simp only [source, dif_pos hgamma]
    exact Classical.choose_spec (hpointCover gamma hgamma)
  apply card_le_two_mul_of_high_core_forbidden_lt_agreement
    family hk hn hrate line0 line1 hline0 hline1 source
      (fun gamma hgamma => (hsourceSpec gamma hgamma).1)
      (fun gamma hgamma => (hsourceSpec gamma hgamma).2)
  intro gamma hgamma
  let S := jointCore dom (u 0) (u 1)
    (source gamma).1 (source gamma).2
  let B := highCoreTransverseForbidden family h line0 line1 (source gamma)
  have hBsub : B ⊆ S := by
    intro i hi
    simp only [B, highCoreTransverseForbidden, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    rcases hi with (hiS | hiSingular) | hiMiss
    · simpa only [S] using hiS
    · exact hsingular (source gamma) (hsourceSpec gamma hgamma).1 hiSingular
    · exact (hiMiss (by simpa only [hunion] using Finset.mem_univ i)).elim
  have hBcard : B.card ≤ h :=
    (Finset.card_le_card hBsub).trans
      (hcoreUpper (source gamma) (hsourceSpec gamma hgamma).1)
  have hAcard : h + 1 ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card :=
    hthreshold.trans (family.threshold_le gamma hgamma)
  simpa only [B] using (show B.card <
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card by omega)

/-- **Exact residual decomposition.**  With two fixed reference half-cores,
either the family is domain-bounded, a selected scalar lies on no high-core
line, or some covered scalar has no cardinal room outside its source core,
the reference singular locus, and the coordinates missed by all high cores.
This replaces the universal one-target starvation conclusion by one explicit
global set obstruction. -/
theorem card_le_two_mul_or_uncovered_or_forbidden_capacity
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h) :
    family.G.card ≤ 2 * h ∨
      (∃ gamma ∈ family.G, ∀ source ∈ highCoreLines family h,
        gamma ∉ pointsOn family source) ∨
      ∃ gamma ∈ family.G, ∃ source ∈ highCoreLines family h,
        gamma ∈ pointsOn family source ∧
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card ≤
          (highCoreTransverseForbidden family h line0 line1 source).card := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  apply Or.inr
  by_cases hcoverage : ∀ gamma ∈ family.G,
      ∃ source ∈ highCoreLines family h,
        gamma ∈ pointsOn family source
  · let source : F → LineParameter F := fun gamma =>
      if hgamma : gamma ∈ family.G then
        Classical.choose (hcoverage gamma hgamma)
      else
        line0
    have hsourceSpec : ∀ gamma ∈ family.G,
        source gamma ∈ highCoreLines family h ∧
        gamma ∈ pointsOn family (source gamma) := by
      intro gamma hgamma
      simp only [source, dif_pos hgamma]
      exact Classical.choose_spec (hcoverage gamma hgamma)
    apply Or.inr
    by_contra hcapacity
    have hroom : ∀ gamma ∈ family.G,
        (highCoreTransverseForbidden family h line0 line1
            (source gamma)).card <
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card := by
      intro gamma hgamma
      by_contra hnot
      apply hcapacity
      exact ⟨gamma, hgamma, source gamma,
        (hsourceSpec gamma hgamma).1,
        (hsourceSpec gamma hgamma).2, by omega⟩
    exact hcard <| card_le_two_mul_of_high_core_forbidden_lt_agreement
      family hk hn hrate line0 line1 hline0 hline1 source
        (fun gamma hgamma => (hsourceSpec gamma hgamma).1)
        (fun gamma hgamma => (hsourceSpec gamma hgamma).2) hroom
  · apply Or.inl
    have hfailure : ∃ gamma ∈ family.G,
        ¬ ∃ source ∈ highCoreLines family h,
          gamma ∈ pointsOn family source := by
      by_contra hnone
      apply hcoverage
      intro gamma hgamma
      by_contra hgammaNone
      exact hnone ⟨gamma, hgamma, hgammaNone⟩
    obtain ⟨gamma, hgamma, hgammaUncovered⟩ := hfailure
    refine ⟨gamma, hgamma, ?_⟩
    intro source hsource hgammaOn
    exact hgammaUncovered ⟨source, hsource, hgammaOn⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply
#print axioms exists_transverse_target_of_forbidden_card_lt
#print axioms exists_transverse_target_of_aggregateHighCoreFresh
#print axioms aggregateHighCoreFresh_card_ge_of_union_slack
#print axioms card_le_two_mul_of_transverse_high_core_supply
#print axioms card_le_two_mul_of_aggregate_high_core_fresh_supply
#print axioms card_le_two_mul_of_high_core_forbidden_lt_agreement
#print axioms card_le_two_mul_of_high_core_union_slack
#print axioms card_le_two_mul_of_full_high_core_union_and_singular_containment
#print axioms card_le_two_mul_or_uncovered_or_forbidden_capacity
