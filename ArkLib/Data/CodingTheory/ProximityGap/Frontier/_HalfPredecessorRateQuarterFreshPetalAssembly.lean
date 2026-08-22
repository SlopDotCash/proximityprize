/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCollapsedClusterInjection

/-!
# Fresh-petal assembly for a collapsed rate-quarter cluster

A large agreement set must meet another decoded-line core if the source core
together with the complement of the cluster core union has insufficient room.
This supplies the coordinate and target-line choices required by the collapsed
cluster injection theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalAssembly

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Union of the joint cores carried by a finite set of decoded polynomial
lines. -/
noncomputable def clusterCoreUnion
    (dom : I ↪ F) (u0 u1 : I → F)
    (targets : Finset (PolynomialLine F)) : Finset I :=
  targets.biUnion fun line => jointCore dom u0 u1 line.1 line.2

/-- An agreement set of size at least `h+1` has a fresh coordinate in another
target core whenever the source core and the complement of the target-core
union together have size at most `h`. -/
theorem exists_fresh_petal_in_clusterCoreUnion
    (dom : I ↪ F) (u0 u1 : I → F)
    (targets : Finset (PolynomialLine F))
    (source : PolynomialLine F) (gamma : F) (h : ℕ)
    (hlarge : h + 1 ≤
      (fullAgreement dom u0 u1 gamma
        (source.1 + C gamma * source.2)).card)
    (hcoverage :
      (jointCore dom u0 u1 source.1 source.2).card +
          (Finset.univ \ clusterCoreUnion dom u0 u1 targets).card ≤ h) :
    ∃ i : I, ∃ target : PolynomialLine F,
      target ∈ targets ∧ target ≠ source ∧
      i ∈ fullAgreement dom u0 u1 gamma
        (source.1 + C gamma * source.2) ∧
      i ∈ jointCore dom u0 u1 target.1 target.2 ∧
      i ∉ jointCore dom u0 u1 source.1 source.2 := by
  classical
  let A := fullAgreement dom u0 u1 gamma
    (source.1 + C gamma * source.2)
  let S := jointCore dom u0 u1 source.1 source.2
  let U := clusterCoreUnion dom u0 u1 targets
  have hex : ∃ i : I, i ∈ A ∧ i ∉ S ∧ i ∈ U := by
    by_contra hnone
    have hsub : A ⊆ S ∪ (Finset.univ \ U) := by
      intro i hiA
      by_cases hiS : i ∈ S
      · exact Finset.mem_union_left _ hiS
      · have hiU : i ∉ U := by
          intro hiU
          exact hnone ⟨i, hiA, hiS, hiU⟩
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiU⟩)
    have hcardA : A.card ≤ (S ∪ (Finset.univ \ U)).card :=
      Finset.card_le_card hsub
    have hunion : (S ∪ (Finset.univ \ U)).card ≤
        S.card + (Finset.univ \ U).card :=
      Finset.card_union_le _ _
    have hsmall : A.card ≤ h := by
      exact hcardA.trans (hunion.trans (by simpa only [S, U] using hcoverage))
    have : h + 1 ≤ A.card := by simpa only [A] using hlarge
    omega
  obtain ⟨i, hiA, hiS, hiU⟩ := hex
  have hiU' : i ∈ targets.biUnion
      (fun line => jointCore dom u0 u1 line.1 line.2) := by
    simpa only [U, clusterCoreUnion] using hiU
  obtain ⟨target, htarget, hitarget⟩ := Finset.mem_biUnion.mp hiU'
  refine ⟨i, target, htarget, ?_, ?_, hitarget, ?_⟩
  · intro heq
    apply hiS
    simpa only [S, heq] using hitarget
  · simpa only [A] using hiA
  · simpa only [S] using hiS

/-- **Fresh-petal assembly.** Suppose the source lines and every line in a
finite target cluster are determinant-collapsed with a fixed reference pair.
If every selected scalar has `h+1` agreements and its source core plus the
coordinates missed by the target-core union has size at most `h`, then the
fresh-petal coordinates required by the collapsed-cluster injection exist
automatically. Hence the scalar family has size at most the domain length. -/
theorem card_le_domain_of_collapsed_clusterCoreUnion
    (dom : I ↪ F) (u0 u1 : I → F) (G : Finset F) (h : ℕ)
    (line0 line1 : PolynomialLine F)
    (source : F → PolynomialLine F)
    (targets : Finset (PolynomialLine F))
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htargets : ∀ target ∈ targets,
      lineDeterminant line0 line1 target = 0)
    (href : ∀ i ∈ clusterCoreUnion dom u0 u1 targets,
      (line1.2 - line0.2).eval (dom i) ≠ 0)
    (hlarge : ∀ gamma ∈ G, h + 1 ≤
      (fullAgreement dom u0 u1 gamma
        ((source gamma).1 + C gamma * (source gamma).2)).card)
    (hcoverage : ∀ gamma ∈ G,
      (jointCore dom u0 u1 (source gamma).1 (source gamma).2).card +
          (Finset.univ \ clusterCoreUnion dom u0 u1 targets).card ≤ h) :
    G.card ≤ Fintype.card I := by
  classical
  by_cases hG : G.Nonempty
  · obtain ⟨gamma0, hgamma0⟩ := hG
    have hw : ∀ gamma ∈ G, ∃ p : I × PolynomialLine F,
        p.2 ∈ targets ∧ p.2 ≠ source gamma ∧
        p.1 ∈ fullAgreement dom u0 u1 gamma
          ((source gamma).1 + C gamma * (source gamma).2) ∧
        p.1 ∈ jointCore dom u0 u1 p.2.1 p.2.2 ∧
        p.1 ∉ jointCore dom u0 u1 (source gamma).1 (source gamma).2 := by
      intro gamma hgamma
      obtain ⟨i, target, htarget, hne, hagree, hcore, hfresh⟩ :=
        exists_fresh_petal_in_clusterCoreUnion
          dom u0 u1 targets (source gamma) gamma h
            (hlarge gamma hgamma) (hcoverage gamma hgamma)
      exact ⟨(i, target), htarget, hne, hagree, hcore, hfresh⟩
    obtain ⟨p0, hp0⟩ := hw gamma0 hgamma0
    let picked : F → I × PolynomialLine F := fun gamma =>
      if hgamma : gamma ∈ G then Classical.choose (hw gamma hgamma) else p0
    let coord : F → I := fun gamma => (picked gamma).1
    let target : F → PolynomialLine F := fun gamma => (picked gamma).2
    have hpicked : ∀ gamma ∈ G,
        target gamma ∈ targets ∧ target gamma ≠ source gamma ∧
        coord gamma ∈ fullAgreement dom u0 u1 gamma
          ((source gamma).1 + C gamma * (source gamma).2) ∧
        coord gamma ∈ jointCore dom u0 u1
          (target gamma).1 (target gamma).2 ∧
        coord gamma ∉ jointCore dom u0 u1
          (source gamma).1 (source gamma).2 := by
      intro gamma hgamma
      simpa only [target, coord, picked, dif_pos hgamma] using
        (Classical.choose_spec (hw gamma hgamma))
    apply card_le_domain_of_collapsed_fresh_petals
      dom u0 u1 G line0 line1 source target coord hsource
    · intro gamma hgamma
      exact htargets (target gamma) (hpicked gamma hgamma).1
    · intro gamma hgamma
      apply href (coord gamma)
      simp only [clusterCoreUnion, Finset.mem_biUnion]
      exact ⟨target gamma, (hpicked gamma hgamma).1,
        (hpicked gamma hgamma).2.2.2.1⟩
    · intro gamma hgamma
      exact (hpicked gamma hgamma).2.2.1
    · intro gamma hgamma
      exact (hpicked gamma hgamma).2.2.2.1
    · intro gamma hgamma
      exact (hpicked gamma hgamma).2.2.2.2
  · rw [Finset.not_nonempty_iff_eq_empty.mp hG]
    simp

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalAssembly

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalAssembly
#print axioms exists_fresh_petal_in_clusterCoreUnion
#print axioms card_le_domain_of_collapsed_clusterCoreUnion
