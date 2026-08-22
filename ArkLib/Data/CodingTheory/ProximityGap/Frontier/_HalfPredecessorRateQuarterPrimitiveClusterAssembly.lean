/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterFreshPetalAssembly

/-!
# Fresh-petal assembly with a primitive collapsed direction

This is the core-union assembly theorem with the obsolete reference-slope-root
condition removed.  Coverage supplies one fresh cross-core coordinate for each
scalar; primitive normalization makes every such coordinate automatically
transverse to the common cluster direction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalAssembly

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveClusterAssembly

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Primitive fresh-petal assembly.**  If the target-core union leaves too
few coordinates to contain the source core and an `h+1` agreement set, every
scalar has a fresh cross-core coordinate.  Distinct references and
determinant collapse then give the domain bound without any exceptional root
set. -/
theorem card_le_domain_of_primitive_collapsed_clusterCoreUnion
    (dom : I ↪ F) (u0 u1 : I → F) (G : Finset F) (h : ℕ)
    (line0 line1 : PolynomialLine F)
    (source : F → PolynomialLine F)
    (targets : Finset (PolynomialLine F))
    (hne : line0 ≠ line1)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htargets : ∀ target ∈ targets,
      lineDeterminant line0 line1 target = 0)
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
        p.1 ∉ jointCore dom u0 u1
          (source gamma).1 (source gamma).2 := by
      intro gamma hgamma
      obtain ⟨i, target, htarget, htargetNe, hagree, hcore, hfresh⟩ :=
        exists_fresh_petal_in_clusterCoreUnion
          dom u0 u1 targets (source gamma) gamma h
            (hlarge gamma hgamma) (hcoverage gamma hgamma)
      exact ⟨(i, target), htarget, htargetNe, hagree, hcore, hfresh⟩
    obtain ⟨p0, _hp0⟩ := hw gamma0 hgamma0
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
    apply card_le_domain_of_primitive_collapsed_fresh_petals
      dom u0 u1 G line0 line1 source target coord hne hsource
    · intro gamma hgamma
      exact htargets (target gamma) (hpicked gamma hgamma).1
    · intro gamma hgamma
      exact (hpicked gamma hgamma).2.2.1
    · intro gamma hgamma
      exact (hpicked gamma hgamma).2.2.2.1
    · intro gamma hgamma
      exact (hpicked gamma hgamma).2.2.2.2
  · rw [Finset.not_nonempty_iff_eq_empty.mp hG]
    simp

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveClusterAssembly

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveClusterAssembly
#print axioms card_le_domain_of_primitive_collapsed_clusterCoreUnion
