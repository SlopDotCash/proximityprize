/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourDependentSyndromeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCompactEdgeCollinearity

/-!
# Rate-quarter `n = 16`, `k = 4`: two contained columns collapse

Suppose the punctured quotient row plane contains two coordinate columns.
Four-wise independence makes those columns a basis of the rank-two plane.
A regular outsider has an exact two-column syndrome representation whose two
coefficients are nonzero.  Its support cannot use an outside column: one
outside endpoint would force that column into the plane, while two outside
endpoints would place four independent columns in a space of dimension at
most three.  Hence every regular missed edge is the same contained pair.

The common missed edge is a compact missed-edge population.  The established
compact-edge collinearity theorem puts all regular outsiders on a second
decoded line and contradicts uniqueness of the source eight-core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Module Submodule Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeChordBound
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourDependentSyndromeCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCompactEdgeCollinearity

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourTwoColumnCollapse

attribute [local instance] Classical.propDecidable

/-! ## Abstract two-column support collapse -/

variable {F V J : Type} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V] [Fintype J] [DecidableEq J]

/-- A rank-two MDS plane containing two frame columns admits no other
two-column support with both coefficients nonzero. -/
theorem support_eq_contained_pair_of_nonzero_chord
    (P : Submodule F V) (v : J -> V)
    (hP : finrank F P <= 2)
    (hMDS4 : IndependentUpTo (F := F) v 4)
    {key1 key2 left right : J}
    (hkeys : key1 ≠ key2)
    (hkey1 : v key1 ∈ P) (hkey2 : v key2 ∈ P)
    (hlr : left ≠ right)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcombNe : a • v left + b • v right ≠ 0)
    (hcombP : a • v left + b • v right ∈ P) :
    ({left, right} : Finset J) = {key1, key2} := by
  classical
  have hnoOther : ∀ x : J, x ≠ key1 -> x ≠ key2 -> v x ∉ P := by
    intro x hx1 hx2 hxPmem
    let S : Finset J := {key1, key2, x}
    have hScard : S.card = 3 := by
      dsimp only [S]
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hx2)]
      intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hkeys h
      · exact hx1 h.symm
    have hSLI : LinearIndependent F (fun j : S => v j.1) :=
      hMDS4 S (by omega)
    have hspanLe :
        span F (Set.range (fun j : S => v j.1)) <= P := by
      rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      have hj : j.1 = key1 ∨ j.1 = key2 ∨ j.1 = x := by
        simpa only [S, Finset.mem_insert, Finset.mem_singleton] using j.2
      rcases hj with h | h | h
      · simpa only [h] using hkey1
      · simpa only [h] using hkey2
      · simpa only [h] using hxPmem
    have hmono := Submodule.finrank_mono hspanLe
    have hlower : 3 <= finrank F P := by
      rw [finrank_span_eq_card hSLI] at hmono
      simpa only [Fintype.card_coe, hScard] using hmono
    omega
  have hnotBothOutside :
      ¬ ((left ≠ key1 ∧ left ≠ key2) ∧
        (right ≠ key1 ∧ right ≠ key2)) := by
    rintro ⟨⟨hl1, hl2⟩, ⟨hr1, hr2⟩⟩
    have hchord : ChordMeets P v left right :=
      ⟨hlr, a, b, hcombNe, hcombP⟩
    let W : Submodule F V := P ⊔ span F ({v left} : Set V)
    have hrightW : v right ∈ W :=
      right_mem_sup_span_of_chordMeets P v
        (hnoOther left hl1 hl2) hchord
    let S : Finset J := {key1, key2, left, right}
    have hScard : S.card = 4 := by
      dsimp only [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair hlr]
      · intro hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact hl2 h.symm
        · exact hr2 h.symm
      · intro hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · exact hkeys h
        · exact hl1 h.symm
        · exact hr1 h.symm
    have hSLI : LinearIndependent F (fun j : S => v j.1) :=
      hMDS4 S (by omega)
    have hvaluesW : ∀ j : S, v j.1 ∈ W := by
      intro j
      have hj : j.1 = key1 ∨ j.1 = key2 ∨
          j.1 = left ∨ j.1 = right := by
        simpa only [S, Finset.mem_insert, Finset.mem_singleton] using j.2
      rcases hj with h | h | h | h
      · exact (show P <= W from le_sup_left) (by simpa only [h] using hkey1)
      · exact (show P <= W from le_sup_left) (by simpa only [h] using hkey2)
      · rw [h]
        exact (show span F ({v left} : Set V) <= W from le_sup_right)
          (subset_span (by simp))
      · simpa only [h] using hrightW
    have hspanLe :
        span F (Set.range (fun j : S => v j.1)) <= W := by
      rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      exact hvaluesW j
    have hLower : 4 <= finrank F W := by
      have hmono := Submodule.finrank_mono hspanLe
      rw [finrank_span_eq_card hSLI] at hmono
      simpa only [Fintype.card_coe, hScard] using hmono
    have hsingle : finrank F (span F ({v left} : Set V)) <= 1 := by
      have hspan : finrank F (span F ({v left} : Set V)) <=
          ({v left} : Finset V).card := by
        simpa using finrank_span_finset_le_card (R := F)
          ({v left} : Finset V)
      simpa only [Finset.card_singleton] using hspan
    have hUpper : finrank F W <= 3 := by
      calc
        finrank F W <= finrank F P +
            finrank F (span F ({v left} : Set V)) :=
          Submodule.finrank_add_le_finrank_add_finrank P
            (span F ({v left} : Set V))
        _ <= 2 + 1 := Nat.add_le_add hP hsingle
        _ = 3 := by norm_num
    omega
  have hsome :
      (left = key1 ∨ left = key2) ∨
        (right = key1 ∨ right = key2) := by
    by_contra hnone
    simp only [not_or] at hnone
    exact hnotBothOutside
      ⟨⟨hnone.1.1, hnone.1.2⟩, ⟨hnone.2.1, hnone.2.2⟩⟩
  have hleft : left = key1 ∨ left = key2 := by
    rcases hsome with hleft | hright
    · exact hleft
    · have hvrightP : v right ∈ P := by
        rcases hright with h | h
        · simpa only [h] using hkey1
        · simpa only [h] using hkey2
      have havleftP : a • v left ∈ P := by
        have hsub := P.sub_mem hcombP (P.smul_mem b hvrightP)
        simpa only [add_sub_cancel_right] using hsub
      have hvleftP : v left ∈ P := by
        have hscaled := P.smul_mem a⁻¹ havleftP
        simpa only [inv_smul_smul₀ ha] using hscaled
      by_contra hout
      simp only [not_or] at hout
      exact (hnoOther left hout.1 hout.2) hvleftP
  have hvleftP : v left ∈ P := by
    rcases hleft with h | h
    · simpa only [h] using hkey1
    · simpa only [h] using hkey2
  have hbwrightP : b • v right ∈ P := by
    have hsub := P.sub_mem hcombP (P.smul_mem a hvleftP)
    simpa only [add_sub_cancel_left] using hsub
  have hvrightP : v right ∈ P := by
    have hscaled := P.smul_mem b⁻¹ hbwrightP
    simpa only [inv_smul_smul₀ hb] using hscaled
  have hright : right = key1 ∨ right = key2 := by
    by_contra hout
    simp only [not_or] at hout
    exact (hnoOther right hout.1 hout.2) hvrightP
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact hleft
    · exact hright
  · rw [Finset.card_pair hkeys, Finset.card_pair hlr]

/-! ## Concrete unique-core closure -/

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Fintype F] [DecidableEq F]

/-- Two contained quotient columns force every regular missed edge to be
their underlying coordinate pair. -/
theorem regularMissedEdge_eq_of_two_contained_columns
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (key1 key2 : ↑(sourceComplement family line))
    (hkeys : key1 ≠ key2)
    (hkey1 : quotientColumn (sourceComplementCode family line) key1 ∈
      span F ({
        (sourceComplementCode family line).mkQ
          (sourceComplementRow0 family line),
        (sourceComplementCode family line).mkQ
          (sourceComplementRow1 family line)} :
            Set ((↑(sourceComplement family line) -> F) ⧸
              sourceComplementCode family line)))
    (hkey2 : quotientColumn (sourceComplementCode family line) key2 ∈
      span F ({
        (sourceComplementCode family line).mkQ
          (sourceComplementRow0 family line),
        (sourceComplementCode family line).mkQ
          (sourceComplementRow1 family line)} :
            Set ((↑(sourceComplement family line) -> F) ⧸
              sourceComplementCode family line)))
    {gamma : F} (hgamma : gamma ∈ regularOutsideLine family line) :
    regularMissedEdge family line gamma = {key1.1, key2.1} := by
  classical
  let V := sourceComplement family line
  let domV := sourceComplementDomain family line
  let C0 := sourceComplementCode family line
  let v0 := sourceComplementRow0 family line
  let v1 := sourceComplementRow1 family line
  let P := span F ({C0.mkQ v0, C0.mkQ v1} : Set ((↑V -> F) ⧸ C0))
  let col : ↑V -> ((↑V -> F) ⧸ C0) := quotientColumn C0
  let rep := Classical.choice
    (regular_missedEdgeSyndromeRepresentation
      family hn hline hcore hgamma)
  have hVcard : Fintype.card ↑V = 8 := by
    rw [Fintype.card_coe]
    simp only [V, sourceComplement, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hn, hcore]
  have hMDS4 : IndependentUpTo (F := F) col 4 := by
    simpa only [col, C0, sourceComplementCode, domV] using
      reedSolomon_eight_four_quotientColumns_independentUpTo_four
        domV hVcard
  have hpairs : ({rep.left, rep.right} : Finset ↑V) = {key1, key2} := by
    apply support_eq_contained_pair_of_nonzero_chord
      P col (rowPlane_finrank_le_two C0 v0 v1) hMDS4
        hkeys hkey1 hkey2 rep.left_ne_right
        rep.leftCoeff rep.rightCoeff
        rep.leftCoeff_ne_zero rep.rightCoeff_ne_zero
    · rw [<- rep.syndrome]
      exact rep.syndrome_ne_zero
    · rw [<- rep.syndrome]
      exact quotientAffinePoint_mem_rowPlane C0 v0 v1 gamma
  have hpairsVal := congrArg
    (fun S : Finset ↑V => S.image Subtype.val) hpairs
  calc
    regularMissedEdge family line gamma =
        {rep.left.1, rep.right.1} := rep.endpoint_pair.symm
    _ = {key1.1, key2.1} := by
      simpa only [Finset.image_insert, Finset.image_singleton] using hpairsVal

/-- **Two-contained-column branch closed.**  A unique-eight-core residual
cannot have two quotient coordinate columns in its punctured row plane. -/
theorem uniqueEightCoreResidual_false_of_two_contained_columns
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 <=
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (residual : UniqueEightCoreResidual family)
    (key1 key2 : ↑(sourceComplement family residual.source))
    (hkeys : key1 ≠ key2)
    (hkey1 : quotientColumn
        (sourceComplementCode family residual.source) key1 ∈
      span F ({
        (sourceComplementCode family residual.source).mkQ
          (sourceComplementRow0 family residual.source),
        (sourceComplementCode family residual.source).mkQ
          (sourceComplementRow1 family residual.source)} :
            Set ((↑(sourceComplement family residual.source) -> F) ⧸
              sourceComplementCode family residual.source)))
    (hkey2 : quotientColumn
        (sourceComplementCode family residual.source) key2 ∈
      span F ({
        (sourceComplementCode family residual.source).mkQ
          (sourceComplementRow0 family residual.source),
        (sourceComplementCode family residual.source).mkQ
          (sourceComplementRow1 family residual.source)} :
            Set ((↑(sourceComplement family residual.source) -> F) ⧸
              sourceComplementCode family residual.source))) :
    False := by
  classical
  have htwo : 1 <
      (regularOutsideLine family residual.source).card := by
    have height := residual.eight_regular_outsiders
    omega
  obtain ⟨gamma, hgamma, beta, hbeta, hne⟩ :=
    Finset.one_lt_card.mp htwo
  apply uniqueEightCoreResidual_false_of_compact_missed_edges
    family hn hthreshold residual hgamma hbeta hne
  intro theta htheta
  have hgammaEdge := regularMissedEdge_eq_of_two_contained_columns
    family hn residual.source_mem residual.source_core_card
      key1 key2 hkeys hkey1 hkey2 hgamma
  have hbetaEdge := regularMissedEdge_eq_of_two_contained_columns
    family hn residual.source_mem residual.source_core_card
      key1 key2 hkeys hkey1 hkey2 hbeta
  have hthetaEdge := regularMissedEdge_eq_of_two_contained_columns
    family hn residual.source_mem residual.source_core_card
      key1 key2 hkeys hkey1 hkey2 htheta
  rw [hgammaEdge, hbetaEdge, hthetaEdge,
    Finset.union_self, Finset.union_self]
  rcases Finset.card_pair_eq_one_or_two
      (a := key1.1) (b := key2.1) with h | h <;> omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourTwoColumnCollapse

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourTwoColumnCollapse
#print axioms support_eq_contained_pair_of_nonzero_chord
#print axioms regularMissedEdge_eq_of_two_contained_columns
#print axioms uniqueEightCoreResidual_false_of_two_contained_columns
