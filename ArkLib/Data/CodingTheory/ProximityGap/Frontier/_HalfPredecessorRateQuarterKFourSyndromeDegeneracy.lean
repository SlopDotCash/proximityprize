/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourWeightTwoSyndrome
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterExceptionalDirectionPuncture
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSyndrome

/-!
# Degenerate quotient rows in the `n = 16`, `k = 4` syndrome argument

The regular-outsider quotient argument has two exceptional inputs:

* the two punctured received-row classes may be dependent; or
* their quotient row plane may contain a coordinate column.

Both have concrete consequences.  If the rows are dependent, any one
nonzero weight-two affine syndrome forces the direction class itself into the
same two-column span.  Lifting through the punctured `[8,4]` Reed--Solomon
quotient produces a global degree-`<4` direction polynomial agreeing with the
received direction on at least six coordinates.  In a family larger than
sixteen, the very-high-core puncturing theorem localizes this direction to
the exact exceptional band `6..13`.

If a quotient coordinate column lies in an independent row plane, there are
two cases.  It is either the point at infinity, making the direction class
weight one and again producing an exceptional direction (now with at least
seven agreements), or it is a unique affine point of the quotient pencil.
The latter is the honest weight-one/long-outsider residual at the abstract
level.  For the concrete unique-eight-core quotient, however, exactly one
contained column is impossible: projective injectivity gives at most one
regular point on chords through it, and deleting it leaves at most six chord
supports on the seven remaining columns.  Thus only the separate
two-contained-column/common-edge configuration remains for that branch.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterExceptionalDirectionPuncture
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeChordBound
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeDegeneracy

attribute [local instance] Classical.propDecidable

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype I] [Nonempty I] [DecidableEq I]

/-! ## Abstract quotient-plane degeneracies -/

/-- Failure of quotient-row independence supplies an explicit nontrivial
linear relation between the two row classes. -/
theorem exists_nontrivial_quotient_row_relation
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hdep : ¬ QuotientRowsIndependent C u0 u1) :
    ∃ a b : F, (a ≠ 0 ∨ b ≠ 0) ∧
      a • C.mkQ u0 + b • C.mkQ u1 = 0 := by
  rw [QuotientRowsIndependent] at hdep
  push Not at hdep
  obtain ⟨a, b, hrel, hnontrivial⟩ := hdep
  refine ⟨a, b, ?_, hrel⟩
  by_cases ha : a = 0
  · exact Or.inr (hnontrivial ha)
  · exact Or.inl ha

/-- In a dependent quotient row pencil, every nonzero affine point spans the
direction class. -/
theorem directionClass_mem_span_of_rows_dependent
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hdep : ¬ QuotientRowsIndependent C u0 u1)
    (gamma : F)
    (hpoint : quotientAffinePoint C u0 u1 gamma ≠ 0)
    (P : Submodule F ((I -> F) ⧸ C))
    (hpointP : quotientAffinePoint C u0 u1 gamma ∈ P) :
    C.mkQ u1 ∈ P := by
  obtain ⟨a, b, hab, hrel⟩ :=
    exists_nontrivial_quotient_row_relation C u0 u1 hdep
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by
      rcases hab with ha | hb
      · exact (ha rfl).elim
      · exact hb
    simp only [zero_smul, zero_add] at hrel
    have hy : C.mkQ u1 = 0 := by
      exact (smul_eq_zero.mp hrel).resolve_left hb
    rw [hy]
    exact P.zero_mem
  · let c : F := gamma - a⁻¹ * b
    have hx : C.mkQ u0 = -(a⁻¹ * b) • C.mkQ u1 := by
      have hax : a • C.mkQ u0 = -(b • C.mkQ u1) :=
        eq_neg_of_add_eq_zero_left hrel
      calc
        C.mkQ u0 = a⁻¹ • (a • C.mkQ u0) := by
          rw [inv_smul_smul₀ ha]
        _ = a⁻¹ • (-(b • C.mkQ u1)) := by rw [hax]
        _ = -(a⁻¹ * b) • C.mkQ u1 := by
          simp only [smul_neg, smul_smul, neg_smul]
    have hp : quotientAffinePoint C u0 u1 gamma =
        c • C.mkQ u1 := by
      simp only [quotientAffinePoint, hx, c]
      module
    have hc : c ≠ 0 := by
      intro hc
      apply hpoint
      rw [hp, hc, zero_smul]
    have hscaled : c⁻¹ • quotientAffinePoint C u0 u1 gamma ∈ P :=
      P.smul_mem c⁻¹ hpointP
    rw [hp, inv_smul_smul₀ hc] at hscaled
    exact hscaled

/-- A dependent row pencil plus one nonzero two-column affine syndrome puts
the direction class in that same two-column span. -/
theorem directionClass_mem_pairSpan_of_rows_dependent
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hdep : ¬ QuotientRowsIndependent C u0 u1)
    (gamma : F)
    (hpoint : quotientAffinePoint C u0 u1 gamma ≠ 0)
    (left right : I)
    (hspan : quotientAffinePoint C u0 u1 gamma ∈
      span F ({quotientColumn C left, quotientColumn C right} :
        Set ((I -> F) ⧸ C))) :
    C.mkQ u1 ∈
      span F ({quotientColumn C left, quotientColumn C right} :
        Set ((I -> F) ⧸ C)) := by
  exact directionClass_mem_span_of_rows_dependent
    C u0 u1 hdep gamma hpoint _ hspan

/-- Classification of a coordinate column lying in an independent quotient
row plane.  A column at infinity is proportional to the direction class;
otherwise it is represented by one affine point with nonzero scale. -/
theorem column_mem_rowPlane_direction_or_affine_weight_one
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (_hrows : QuotientRowsIndependent C u0 u1)
    (i : I) (hcolumnNe : quotientColumn C i ≠ 0)
    (hcolumn : quotientColumn C i ∈
      span F ({C.mkQ u0, C.mkQ u1} : Set ((I -> F) ⧸ C))) :
    (∃ b : F, b ≠ 0 ∧ quotientColumn C i = b • C.mkQ u1) ∨
      ∃ gamma c : F, c ≠ 0 ∧
        quotientAffinePoint C u0 u1 gamma = c • quotientColumn C i := by
  rw [Submodule.mem_span_pair] at hcolumn
  obtain ⟨a, b, hab⟩ := hcolumn
  by_cases ha : a = 0
  · left
    subst a
    simp only [zero_smul, zero_add] at hab
    have hb : b ≠ 0 := by
      intro hb
      apply hcolumnNe
      rw [← hab, hb, zero_smul]
    exact ⟨b, hb, hab.symm⟩
  · right
    refine ⟨a⁻¹ * b, a⁻¹, inv_ne_zero ha, ?_⟩
    simp only [quotientAffinePoint]
    have hscaled := congrArg (fun x : (I -> F) ⧸ C => a⁻¹ • x) hab
    simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul] at hscaled
    exact hscaled

/-- The affine scalar in the column classification is unique. -/
theorem affine_weight_one_scalar_unique
    (C : Submodule F (I -> F)) (u0 u1 : I -> F)
    (hrows : QuotientRowsIndependent C u0 u1)
    {i : I} {gamma beta c d : F}
    (hgamma : quotientAffinePoint C u0 u1 gamma =
      c • quotientColumn C i)
    (hbeta : quotientAffinePoint C u0 u1 beta =
      d • quotientColumn C i) :
    gamma = beta := by
  by_cases hc : c = 0
  · subst c
    have hzero : quotientAffinePoint C u0 u1 gamma = 0 := by
      simpa only [zero_smul] using hgamma
    exact (quotientAffinePoint_ne_zero C u0 u1 hrows gamma hzero).elim
  · have hprop : (d * c⁻¹) • quotientAffinePoint C u0 u1 gamma =
        quotientAffinePoint C u0 u1 beta := by
      rw [hgamma, hbeta, smul_smul]
      congr 1
      field_simp
    exact quotientAffinePoint_projectively_injective
      C u0 u1 hrows hprop

/-! ## One contained column -/

/-- Four-wise independence survives deletion of one indexed column. -/
theorem independentUpTo_four_delete
    {V : Type*} [AddCommGroup V] [Module F V]
    (v : I -> V) (hMDS4 : IndependentUpTo (F := F) v 4) (key : I) :
    IndependentUpTo (F := F) (fun i : {j : I // j ≠ key} => v i.1) 4 := by
  classical
  intro J hJ
  let emb : {j : I // j ≠ key} ↪ I :=
    ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
  let K : Finset I := J.map emb
  have hKcard : K.card = J.card := by
    simp only [K, Finset.card_map]
  have hKLI : LinearIndependent F (fun j : K => v j.1) := by
    apply hMDS4 K
    omega
  let e : J -> K := fun j =>
    ⟨j.1.1, Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => z.1) hxy
  have hcomp := hKLI.comp e he
  simpa only [Function.comp_apply, e] using hcomp

/-- If exactly one column of an eight-column MDS frame lies in a syndrome
plane, a projectively injective chord assignment still has size at most
seven.  Chords through the contained column carry at most one projective
point; deleting that column leaves the strict six-edge bound on seven
columns. -/
theorem card_le_seven_of_projectively_injective_chord_assignment_one_column
    {V Gamma : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [DecidableEq Gamma]
    (P : Submodule F V) (v : I -> V)
    (hI : Fintype.card I = 8)
    (hP : finrank F P <= 2)
    (hMDS4 : IndependentUpTo (F := F) v 4)
    (key : I) (hkey : v key ∈ P)
    (hnoOther : ∀ i, i ≠ key -> v i ∉ P)
    (G : Finset Gamma) (left right : Gamma -> I) (point : Gamma -> V)
    (hendpoints : ∀ gamma ∈ G, left gamma ≠ right gamma)
    (hpointNe : ∀ gamma ∈ G, point gamma ≠ 0)
    (hpointP : ∀ gamma ∈ G, point gamma ∈ P)
    (hpointSpan : ∀ gamma ∈ G,
      point gamma ∈ span F ({v (left gamma), v (right gamma)} : Set V))
    (hprojective : ∀ gamma ∈ G, ∀ beta ∈ G,
      (∃ c : F, c • point gamma = point beta) -> gamma = beta) :
    G.card <= 7 := by
  classical
  let incident : Gamma -> Prop := fun gamma =>
    left gamma = key ∨ right gamma = key
  let H : Finset Gamma := G.filter incident
  let A : Finset Gamma := G.filter fun gamma => ¬ incident gamma
  have hkeyNe : v key ≠ 0 := by
    have hsingle := hMDS4 ({key} : Finset I) (by simp)
    simpa using hsingle.ne_zero ⟨key, by simp⟩
  have hincidentProp : ∀ gamma ∈ H,
      ∃ a : F, a ≠ 0 ∧ a • v key = point gamma := by
    intro gamma hgamma
    have hgammaData := Finset.mem_filter.mp hgamma
    have hgammaG : gamma ∈ G := hgammaData.1
    have hends := hendpoints gamma hgammaG
    have hpointSpan' := hpointSpan gamma hgammaG
    rcases hgammaData.2 with hleft | hright
    · have hrightNe : right gamma ≠ key := by
        intro h
        exact hends (hleft.trans h.symm)
      obtain ⟨a, ha⟩ := proportional_of_mem_plane_mem_pairSpan
        P v (right gamma) key (hnoOther _ hrightNe)
          hkeyNe hkey (subset_span (by simp))
          (hpointP gamma hgammaG) (by
            simpa only [hleft, Set.pair_comm] using hpointSpan')
      have haNe : a ≠ 0 := by
        intro ha0
        apply hpointNe gamma hgammaG
        rw [<- ha, ha0, zero_smul]
      exact ⟨a, haNe, ha⟩
    · have hleftNe : left gamma ≠ key := by
        intro h
        exact hends (h.trans hright.symm)
      obtain ⟨a, ha⟩ := proportional_of_mem_plane_mem_pairSpan
        P v (left gamma) key (hnoOther _ hleftNe)
          hkeyNe hkey (subset_span (by simp))
          (hpointP gamma hgammaG) (by
            simpa only [hright] using hpointSpan')
      have haNe : a ≠ 0 := by
        intro ha0
        apply hpointNe gamma hgammaG
        rw [<- ha, ha0, zero_smul]
      exact ⟨a, haNe, ha⟩
  have hHcard : H.card <= 1 := by
    rw [Finset.card_le_one]
    intro gamma hgamma beta hbeta
    obtain ⟨a, ha, hgammaPoint⟩ := hincidentProp gamma hgamma
    obtain ⟨b, _hb, hbetaPoint⟩ := hincidentProp beta hbeta
    have hgammaG := (Finset.mem_filter.mp hgamma).1
    have hbetaG := (Finset.mem_filter.mp hbeta).1
    apply hprojective gamma hgammaG beta hbetaG
    refine ⟨b * a⁻¹, ?_⟩
    rw [<- hgammaPoint, <- hbetaPoint, smul_smul]
    congr 1
    field_simp
  let I0 := {i : I // i ≠ key}
  let v0 : I0 -> V := fun i => v i.1
  have hI0 : Fintype.card I0 = 7 := by
    change Fintype.card {i : I // ¬ i = key} = 7
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hI]
  have hMDS0 : IndependentUpTo (F := F) v0 4 := by
    simpa only [I0, v0] using independentUpTo_four_delete v hMDS4 key
  have hno0 : ∀ i : I0, v0 i ∉ P := by
    intro i
    exact hnoOther i.1 i.2
  let GA := {gamma : Gamma // gamma ∈ A}
  let left0 : GA -> I0 := fun gamma =>
    ⟨left gamma.1, by
      have hnot := (Finset.mem_filter.mp gamma.2).2
      simp only [incident, not_or] at hnot
      exact hnot.1⟩
  let right0 : GA -> I0 := fun gamma =>
    ⟨right gamma.1, by
      have hnot := (Finset.mem_filter.mp gamma.2).2
      simp only [incident, not_or] at hnot
      exact hnot.2⟩
  let point0 : GA -> V := fun gamma => point gamma.1
  have hAcard : A.card <= 6 := by
    have hassign : (Finset.univ : Finset GA).card <=
        (chordGraph P v0).edgeFinset.card := by
      apply card_le_chords_of_projectively_injective_chord_assignment
        P v0 hno0 (Finset.univ : Finset GA) left0 right0 point0
      · intro gamma _
        have hgammaG := (Finset.mem_filter.mp gamma.2).1
        intro heq
        apply hendpoints gamma.1 hgammaG
        exact congrArg Subtype.val heq
      · intro gamma _
        have hgammaG := (Finset.mem_filter.mp gamma.2).1
        simpa only [point0] using hpointNe gamma.1 hgammaG
      · intro gamma _
        have hgammaG := (Finset.mem_filter.mp gamma.2).1
        simpa only [point0] using hpointP gamma.1 hgammaG
      · intro gamma _
        have hgammaG := (Finset.mem_filter.mp gamma.2).1
        simpa only [point0, v0, left0, right0] using
          hpointSpan gamma.1 hgammaG
      · intro gamma _ beta _ hprop
        apply Subtype.ext
        exact hprojective gamma.1
          (Finset.mem_filter.mp gamma.2).1 beta.1
          (Finset.mem_filter.mp beta.2).1 hprop
    have hedge : (chordGraph P v0).edgeFinset.card <= 6 :=
      chordGraph_edgeFinset_card_le_six
        P v0 hI0 hP hMDS0 hno0
    have huniv : (Finset.univ : Finset GA).card = A.card := by
      simp only [Finset.card_univ, Fintype.card_coe, GA]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G) (p := incident)
  change H.card + A.card = G.card at hsplit
  omega

/-- Existential weight-two representations satisfy the same seven-point
bound when the quotient row plane contains exactly one coordinate column. -/
theorem weightTwoSyndromeLine_card_le_seven_of_representations_one_column
    {J : Type} [Fintype J] [Nonempty J] [DecidableEq J]
    (C : Submodule F (J -> F)) (v0 v1 : J -> F)
    (hJ : Fintype.card J = 8)
    (hrows : QuotientRowsIndependent C v0 v1)
    (hMDS4 : IndependentUpTo (F := F) (quotientColumn C) 4)
    (key : J)
    (hkey : quotientColumn C key ∈
      span F ({C.mkQ v0, C.mkQ v1} : Set ((J -> F) ⧸ C)))
    (hnoOther : ∀ i, i ≠ key -> quotientColumn C i ∉
      span F ({C.mkQ v0, C.mkQ v1} : Set ((J -> F) ⧸ C)))
    (G : Finset F)
    (hrepr : ∀ gamma ∈ G,
      Nonempty (WeightTwoRepresentation C v0 v1 gamma)) :
    G.card ≤ 7 := by
  classical
  let P : Submodule F ((J -> F) ⧸ C) :=
    span F ({C.mkQ v0, C.mkQ v1} : Set ((J -> F) ⧸ C))
  let rep (gamma : F) (hgamma : gamma ∈ G) :
      WeightTwoRepresentation C v0 v1 gamma :=
    Classical.choice (hrepr gamma hgamma)
  let fallback : J := Classical.choice (inferInstance : Nonempty J)
  let left : F -> J := fun gamma =>
    if hgamma : gamma ∈ G then (rep gamma hgamma).left else fallback
  let right : F -> J := fun gamma =>
    if hgamma : gamma ∈ G then (rep gamma hgamma).right else fallback
  let point : F -> (J -> F) ⧸ C := fun gamma =>
    quotientAffinePoint C v0 v1 gamma
  apply card_le_seven_of_projectively_injective_chord_assignment_one_column
    P (quotientColumn C) hJ (rowPlane_finrank_le_two C v0 v1)
      hMDS4 key hkey hnoOther G left right point
  · intro gamma hgamma
    simp only [left, right, dif_pos hgamma]
    exact (rep gamma hgamma).left_ne_right
  · intro gamma _hgamma
    exact quotientAffinePoint_ne_zero C v0 v1 hrows gamma
  · intro gamma _hgamma
    exact quotientAffinePoint_mem_rowPlane C v0 v1 gamma
  · intro gamma hgamma
    simp only [left, right, point, dif_pos hgamma]
    rw [Submodule.mem_span_pair]
    exact ⟨(rep gamma hgamma).leftCoeff,
      (rep gamma hgamma).rightCoeff,
      (rep gamma hgamma).syndrome.symm⟩
  · intro gamma _hgamma beta _hbeta hprop
    obtain ⟨c, hc⟩ := hprop
    exact quotientAffinePoint_projectively_injective
      C v0 v1 hrows hc

/-- A unique-eight-core residual cannot have independent quotient rows and
exactly one coordinate column in their row plane. -/
theorem uniqueEightCoreResidual_not_exactly_one_contained_column
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual :
      HalfPredecessorRateQuarterKFourGlobalCoreSynthesis.UniqueEightCoreResidual
        family)
    (hrows : QuotientRowsIndependent
      (sourceComplementCode family residual.source)
      (sourceComplementRow0 family residual.source)
      (sourceComplementRow1 family residual.source))
    (key : ↑(sourceComplement family residual.source))
    (hkey : quotientColumn
        (sourceComplementCode family residual.source) key ∈
      span F ({
        (sourceComplementCode family residual.source).mkQ
          (sourceComplementRow0 family residual.source),
        (sourceComplementCode family residual.source).mkQ
          (sourceComplementRow1 family residual.source)} :
            Set ((↑(sourceComplement family residual.source) -> F) ⧸
              sourceComplementCode family residual.source)))
    (hnoOther : ∀ i : ↑(sourceComplement family residual.source),
      i ≠ key ->
        quotientColumn (sourceComplementCode family residual.source) i ∉
          span F ({
            (sourceComplementCode family residual.source).mkQ
              (sourceComplementRow0 family residual.source),
            (sourceComplementCode family residual.source).mkQ
              (sourceComplementRow1 family residual.source)} :
                Set ((↑(sourceComplement family residual.source) -> F) ⧸
                  sourceComplementCode family residual.source))) :
    False := by
  classical
  let V := sourceComplement family residual.source
  let domV := sourceComplementDomain family residual.source
  let C0 := sourceComplementCode family residual.source
  let v0 := sourceComplementRow0 family residual.source
  let v1 := sourceComplementRow1 family residual.source
  let G := regularOutsideLine family residual.source
  have hVcard : Fintype.card ↑V = 8 := by
    rw [Fintype.card_coe]
    simp only [V, sourceComplement, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hn,
      residual.source_core_card]
  haveI : Nonempty ↑V := by
    apply Finset.Nonempty.to_subtype
    apply Finset.card_pos.mp
    rw [<- Fintype.card_coe, hVcard]
    norm_num
  have hMDS4 : IndependentUpTo (F := F) (quotientColumn C0) 4 := by
    simpa only [C0, sourceComplementCode, domV] using
      reedSolomon_eight_four_quotientColumns_independentUpTo_four
        domV hVcard
  have hrepr : ∀ gamma ∈ G,
      Nonempty (WeightTwoRepresentation C0 v0 v1 gamma) := by
    intro gamma hgamma
    simpa only [G, C0, v0, v1] using
      regular_weightTwoSyndromeRepresentation
        family hn residual.source_mem residual.source_core_card hgamma
  let keyV : ↑V := ⟨key.1, key.2⟩
  have hrows' : QuotientRowsIndependent C0 v0 v1 := by
    simpa only [C0, v0, v1] using hrows
  have hkey' : quotientColumn C0 keyV ∈
      span F ({C0.mkQ v0, C0.mkQ v1} : Set ((↑V -> F) ⧸ C0)) := by
    simpa only [V, C0, v0, v1, keyV] using hkey
  have hnoOther' : ∀ i : ↑V, i ≠ keyV ->
      quotientColumn C0 i ∉
        span F ({C0.mkQ v0, C0.mkQ v1} : Set ((↑V -> F) ⧸ C0)) := by
    simpa only [V, C0, v0, v1, keyV] using hnoOther
  have hupper : G.card ≤ 7 := by
    exact weightTwoSyndromeLine_card_le_seven_of_representations_one_column
      C0 v0 v1 hVcard hrows' hMDS4 keyV hkey' hnoOther' G hrepr
  have hlower : 8 ≤ G.card := by
    simpa only [G] using residual.eight_regular_outsiders
  omega

/-! ## Lifting sparse punctured direction classes -/

/-- Restrict the evaluation domain to the complement of a coordinate set. -/
def puncturedDomain (dom : I ↪ F) (D : Finset I) :
    {i : I // i ∉ D} ↪ F :=
  ⟨fun i => dom i.1, fun _ _ h => Subtype.ext (dom.injective h)⟩

/-- The received direction after subtracting a fixed source slope and
puncturing the source core. -/
def puncturedResidualDirection
    (dom : I ↪ F) (u1 : I -> F) (sourceSlope : F[X])
    (D : Finset I) : {i : I // i ∉ D} -> F :=
  fun i => u1 i.1 - sourceSlope.eval (dom i.1)

/-- The received base row after subtracting a fixed source intercept and
puncturing the source core. -/
def puncturedResidualBase
    (dom : I ↪ F) (u0 : I -> F) (sourceIntercept : F[X])
    (D : Finset I) : {i : I // i ∉ D} -> F :=
  fun i => u0 i.1 - sourceIntercept.eval (dom i.1)

/-- A sparse representative of the punctured direction quotient lifts to a
global direction polynomial.  If the punctured domain has eight coordinates
and the representative is supported on at most `d`, the global direction
core has size at least `8-d`. -/
theorem exists_direction_core_of_sparse_punctured_class
    (dom : I ↪ F) (u1 : I -> F) (D : Finset I)
    (sourceSlope : F[X]) (hsourceSlope : sourceSlope.natDegree < 4)
    (hcomplement : Fintype.card {i : I // i ∉ D} = 8)
    (e : {i : I // i ∉ D} -> F) (J : Finset {i : I // i ∉ D})
    (d : ℕ) (hJ : J.card ≤ d)
    (heSupport : ∀ i, i ∉ J → e i = 0)
    (hquot :
      (ReedSolomon.code (puncturedDomain dom D) 4).mkQ
          (puncturedResidualDirection dom u1 sourceSlope D) =
        (ReedSolomon.code (puncturedDomain dom D) 4).mkQ e) :
    ∃ r : F[X], r.natDegree < 4 ∧
      8 - d ≤ (directionAgreement dom u1 r).card := by
  let C : Submodule F ({i : I // i ∉ D} -> F) :=
    ReedSolomon.code (puncturedDomain dom D) 4
  let w := puncturedResidualDirection dom u1 sourceSlope D
  have hzero : C.mkQ (w - e) = 0 := by
    rw [map_sub]
    change C.mkQ w - C.mkQ e = 0
    exact sub_eq_zero.mpr hquot
  have hmem : w - e ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hzero
  obtain ⟨p, hpdeg, hpEval⟩ :=
    ReedSolomon.mem_code_iff_exists_polynomial.mp hmem
  have hpNat : p.natDegree < 4 := by
    by_cases hp0 : p = 0
    · simp only [hp0, natDegree_zero]
      norm_num
    · rwa [Polynomial.natDegree_lt_iff_degree_lt hp0]
  let r := sourceSlope + p
  have hr : r.natDegree < 4 :=
    lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt hsourceSlope hpNat)
  let good : Finset {i : I // i ∉ D} := Finset.univ \ J
  have hgoodCard : 8 - d ≤ good.card := by
    have hcard : good.card = 8 - J.card := by
      simp only [good, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, hcomplement]
    omega
  let emb : {i : I // i ∉ D} ↪ I :=
    ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
  have hmap : good.map emb ⊆ directionAgreement dom u1 r := by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hjNotJ : j ∉ J := (Finset.mem_sdiff.mp hj).2
    have he0 := heSupport j hjNotJ
    have hpAt := congrFun hpEval j
    simp only [w, puncturedResidualDirection, Pi.sub_apply,
      ReedSolomon.evalOnPoints] at hpAt
    change u1 j.1 - sourceSlope.eval (dom j.1) - e j =
      p.eval (dom j.1) at hpAt
    simp only [directionAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and, r, eval_add]
    change sourceSlope.eval (dom j.1) + p.eval (dom j.1) = u1 j.1
    rw [he0] at hpAt
    linear_combination -hpAt
  refine ⟨r, hr, ?_⟩
  have hcardMap := Finset.card_le_card hmap
  rw [Finset.card_map] at hcardMap
  exact hgoodCard.trans hcardMap

/-- A punctured direction class carried by two quotient columns lifts to a
global direction core of size at least six. -/
theorem exists_direction_core_six_of_pairSpan
    (dom : I ↪ F) (u1 : I -> F) (D : Finset I)
    (sourceSlope : F[X]) (hsourceSlope : sourceSlope.natDegree < 4)
    (hcomplement : Fintype.card {i : I // i ∉ D} = 8)
    (left right : {i : I // i ∉ D})
    (hspan :
      (ReedSolomon.code (puncturedDomain dom D) 4).mkQ
          (puncturedResidualDirection dom u1 sourceSlope D) ∈
        span F
          ({quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) left,
            quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) right} :
            Set (({i : I // i ∉ D} -> F) ⧸
              ReedSolomon.code (puncturedDomain dom D) 4))) :
    ∃ r : F[X], r.natDegree < 4 ∧
      6 ≤ (directionAgreement dom u1 r).card := by
  let C : Submodule F ({i : I // i ∉ D} -> F) :=
    ReedSolomon.code (puncturedDomain dom D) 4
  let w := puncturedResidualDirection dom u1 sourceSlope D
  rw [Submodule.mem_span_pair] at hspan
  obtain ⟨a, b, hab⟩ := hspan
  let e : {i : I // i ∉ D} -> F :=
    a • (Pi.single left 1 : {i : I // i ∉ D} -> F) +
      b • (Pi.single right 1 : {i : I // i ∉ D} -> F)
  let J : Finset {i : I // i ∉ D} := {left, right}
  have hJ : J.card ≤ 2 := by
    rcases Finset.card_pair_eq_one_or_two (a := left) (b := right) with h | h
    · change ({left, right} : Finset {i : I // i ∉ D}).card ≤ 2
      omega
    · change ({left, right} : Finset {i : I // i ∉ D}).card ≤ 2
      omega
  have heSupport : ∀ i, i ∉ J → e i = 0 := by
    intro i hi
    have hil : i ≠ left := by
      intro h
      subst i
      apply hi
      simp only [J, Finset.mem_insert, true_or]
    have hir : i ≠ right := by
      intro h
      subst i
      apply hi
      simp only [J, Finset.mem_insert, Finset.mem_singleton, or_true]
    simp only [e, Pi.single_apply, hil, hir, if_false,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]
  have hquot : C.mkQ w = C.mkQ e := by
    change C.mkQ w = C.mkQ
      (a • (Pi.single left 1 : {i : I // i ∉ D} -> F) +
        b • (Pi.single right 1 : {i : I // i ∉ D} -> F))
    rw [map_add, map_smul, map_smul]
    change C.mkQ w =
      a • quotientColumn C left + b • quotientColumn C right
    exact hab.symm
  have hlift := exists_direction_core_of_sparse_punctured_class
    dom u1 D sourceSlope hsourceSlope hcomplement e J 2 hJ
      heSupport hquot
  simpa only [Nat.reduceSub] using hlift

/-- A punctured direction class proportional to one quotient coordinate
column lifts to a global direction core of size at least seven. -/
theorem exists_direction_core_seven_of_direction_column
    (dom : I ↪ F) (u1 : I -> F) (D : Finset I)
    (sourceSlope : F[X]) (hsourceSlope : sourceSlope.natDegree < 4)
    (hcomplement : Fintype.card {i : I // i ∉ D} = 8)
    (i : {i : I // i ∉ D}) (b : F) (hb : b ≠ 0)
    (hcolumn :
      quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) i =
        b • (ReedSolomon.code (puncturedDomain dom D) 4).mkQ
          (puncturedResidualDirection dom u1 sourceSlope D)) :
    ∃ r : F[X], r.natDegree < 4 ∧
      7 ≤ (directionAgreement dom u1 r).card := by
  let C : Submodule F ({i : I // i ∉ D} -> F) :=
    ReedSolomon.code (puncturedDomain dom D) 4
  let w := puncturedResidualDirection dom u1 sourceSlope D
  let e : {i : I // i ∉ D} -> F :=
    b⁻¹ • (Pi.single i 1 : {i : I // i ∉ D} -> F)
  let J : Finset {i : I // i ∉ D} := {i}
  have heSupport : ∀ j, j ∉ J → e j = 0 := by
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      apply hj
      simp only [J, Finset.mem_singleton]
    simp only [e, Pi.single_apply, hji, if_false, Pi.smul_apply,
      smul_eq_mul, mul_zero]
  have hquot : C.mkQ w = C.mkQ e := by
    change C.mkQ w = C.mkQ
      (b⁻¹ • (Pi.single i 1 : {i : I // i ∉ D} -> F))
    rw [map_smul]
    change C.mkQ w = b⁻¹ • quotientColumn C i
    have hscaled := congrArg (fun x : ({i : I // i ∉ D} -> F) ⧸ C =>
      b⁻¹ • x) hcolumn
    simp only [smul_smul, inv_mul_cancel₀ hb, one_smul] at hscaled
    exact hscaled.symm
  have hlift := exists_direction_core_of_sparse_punctured_class
    dom u1 D sourceSlope hsourceSlope hcomplement e J 1
      (by simp only [J, Finset.card_singleton]; omega) heSupport hquot
  simpa only [Nat.reduceSub] using hlift

/-- **Dependent-row routing.**  One nonzero weight-two affine syndrome in a
dependent punctured row pencil forces a global exceptional direction core of
size at least six. -/
theorem dependent_punctured_rows_produce_direction_core_six
    (dom : I ↪ F) (u1 : I -> F) (D : Finset I)
    (sourceSlope : F[X]) (hsourceSlope : sourceSlope.natDegree < 4)
    (hcomplement : Fintype.card {i : I // i ∉ D} = 8)
    (u0p : {i : I // i ∉ D} -> F)
    (gamma : F)
    (hdep : ¬ QuotientRowsIndependent
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom u1 sourceSlope D))
    (hpoint : quotientAffinePoint
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom u1 sourceSlope D) gamma ≠ 0)
    (left right : {i : I // i ∉ D})
    (hpointSpan : quotientAffinePoint
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom u1 sourceSlope D) gamma ∈
      span F
        ({quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) left,
          quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) right} :
          Set (({i : I // i ∉ D} -> F) ⧸
            ReedSolomon.code (puncturedDomain dom D) 4))) :
    ∃ r : F[X], r.natDegree < 4 ∧
      6 ≤ (directionAgreement dom u1 r).card := by
  letI : Nonempty {i : I // i ∉ D} :=
    Fintype.card_pos_iff.mp (by rw [hcomplement]; norm_num)
  have hdirSpan := directionClass_mem_pairSpan_of_rows_dependent
    (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom u1 sourceSlope D)
      hdep gamma hpoint left right hpointSpan
  exact exists_direction_core_six_of_pairSpan
    dom u1 D sourceSlope hsourceSlope hcomplement left right hdirSpan

/-- A concrete direction core of size at least six in a family larger than
sixteen lies in the surviving exceptional band `6..13`, and no-jointness
supplies the common fresh-coordinate certificate. -/
theorem direction_core_six_routes_to_exceptional_band
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = 9)
    (hcard : 16 < family.G.card)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : 6 ≤ (directionAgreement dom (u 1) r).card) :
    r.natDegree < 4 ∧
      6 ≤ (directionAgreement dom (u 1) r).card ∧
      (directionAgreement dom (u 1) r).card ≤ 13 ∧
      ∀ gamma ∈ family.G, ∃ i : I,
        i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
        i ∉ directionAgreement dom (u 1) r := by
  have hupper : (directionAgreement dom (u 1) r).card ≤ 13 := by
    by_contra hnot
    have hhigh : 14 ≤ (directionAgreement dom (u 1) r).card := by omega
    have hle := card_le_sixteen_of_fourteen_le_direction_core
      family hn hthreshold.ge r hr hhigh
    omega
  refine ⟨hr, hcore, hupper, ?_⟩
  intro gamma hgamma
  exact exists_fullAgreement_outside_directionAgreement
    family hgamma r hr

/-- The dependent-row quotient degeneracy is therefore absorbed by the
exceptional-direction band in every hypothetical `|G|>16` family. -/
theorem dependent_punctured_rows_route_to_exceptional_band
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = 9)
    (hcard : 16 < family.G.card)
    (D : Finset I) (sourceSlope : F[X])
    (hsourceSlope : sourceSlope.natDegree < 4)
    (hcomplement : Fintype.card {i : I // i ∉ D} = 8)
    (u0p : {i : I // i ∉ D} -> F) (gamma : F)
    (hdep : ¬ QuotientRowsIndependent
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom (u 1) sourceSlope D))
    (hpoint : quotientAffinePoint
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom (u 1) sourceSlope D) gamma ≠ 0)
    (left right : {i : I // i ∉ D})
    (hpointSpan : quotientAffinePoint
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom (u 1) sourceSlope D) gamma ∈
      span F
        ({quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) left,
          quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) right} :
          Set (({i : I // i ∉ D} -> F) ⧸
            ReedSolomon.code (puncturedDomain dom D) 4))) :
    ∃ r : F[X], r.natDegree < 4 ∧
      6 ≤ (directionAgreement dom (u 1) r).card ∧
      (directionAgreement dom (u 1) r).card ≤ 13 ∧
      ∀ beta ∈ family.G, ∃ i : I,
        i ∈ fullAgreement dom (u 0) (u 1) beta (family.q beta) ∧
        i ∉ directionAgreement dom (u 1) r := by
  obtain ⟨r, hr, hcore⟩ :=
    dependent_punctured_rows_produce_direction_core_six
      dom (u 1) D sourceSlope hsourceSlope hcomplement u0p gamma
        hdep hpoint left right hpointSpan
  exact ⟨r, direction_core_six_routes_to_exceptional_band
    family hn hthreshold hcard r hr hcore⟩

/-- **Column-degeneracy routing before the family count.**  A quotient
coordinate column in an independent punctured row plane is either the point
at infinity, which yields a global direction core of size at least seven, or
a genuine affine weight-one point. -/
theorem column_degeneracy_produces_direction_core_seven_or_affine_weight_one
    (dom : I ↪ F) (u1 : I -> F) (D : Finset I)
    (sourceSlope : F[X]) (hsourceSlope : sourceSlope.natDegree < 4)
    (hcomplement : Fintype.card {i : I // i ∉ D} = 8)
    (u0p : {i : I // i ∉ D} -> F)
    (hrows : QuotientRowsIndependent
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom u1 sourceSlope D))
    (i : {i : I // i ∉ D})
    (hcolumnNe :
      quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) i ≠ 0)
    (hcolumn :
      quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) i ∈
        span F
          ({(ReedSolomon.code (puncturedDomain dom D) 4).mkQ u0p,
            (ReedSolomon.code (puncturedDomain dom D) 4).mkQ
              (puncturedResidualDirection dom u1 sourceSlope D)} :
            Set (({i : I // i ∉ D} -> F) ⧸
              ReedSolomon.code (puncturedDomain dom D) 4))) :
    (∃ r : F[X], r.natDegree < 4 ∧
      7 ≤ (directionAgreement dom u1 r).card) ∨
      ∃ gamma c : F, c ≠ 0 ∧
        quotientAffinePoint
            (ReedSolomon.code (puncturedDomain dom D) 4) u0p
            (puncturedResidualDirection dom u1 sourceSlope D) gamma =
          c • quotientColumn
            (ReedSolomon.code (puncturedDomain dom D) 4) i := by
  letI : Nonempty {i : I // i ∉ D} :=
    Fintype.card_pos_iff.mp (by rw [hcomplement]; norm_num)
  rcases column_mem_rowPlane_direction_or_affine_weight_one
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom u1 sourceSlope D)
      hrows i hcolumnNe hcolumn with
    ⟨b, hb, hdirection⟩ | ⟨gamma, c, hc, haffine⟩
  · left
    exact exists_direction_core_seven_of_direction_column
      dom u1 D sourceSlope hsourceSlope hcomplement i b hb hdirection
  · exact Or.inr ⟨gamma, c, hc, haffine⟩

/-- The affine side of the column degeneracy really is a punctured
weight-one point: a degree-`<4` polynomial agrees with the affine received
word away from the displayed coordinate. -/
theorem exists_punctured_codeword_off_column_of_affine_weight_one
    (dom : I ↪ F) (D : Finset I)
    (u0p u1p : {i : I // i ∉ D} -> F)
    (gamma c : F) (i : {i : I // i ∉ D})
    (haffine :
      quotientAffinePoint (ReedSolomon.code (puncturedDomain dom D) 4)
          u0p u1p gamma =
        c • quotientColumn
          (ReedSolomon.code (puncturedDomain dom D) 4) i) :
    ∃ p : F[X], p.natDegree < 4 ∧
      ∀ j : {i : I // i ∉ D}, j ≠ i →
        p.eval (dom j.1) = u0p j + gamma * u1p j := by
  let C : Submodule F ({i : I // i ∉ D} -> F) :=
    ReedSolomon.code (puncturedDomain dom D) 4
  let w : {i : I // i ∉ D} -> F := fun j =>
    u0p j + gamma * u1p j
  let e : {i : I // i ∉ D} -> F :=
    c • (Pi.single i 1 : {i : I // i ∉ D} -> F)
  have hquot : C.mkQ w = C.mkQ e := by
    change C.mkQ (fun j => u0p j + gamma * u1p j) =
      C.mkQ (c • (Pi.single i 1 : {i : I // i ∉ D} -> F))
    rw [map_smul]
    change C.mkQ (u0p + gamma • u1p) =
      c • quotientColumn C i
    rw [map_add, map_smul]
    exact haffine
  have hzero : C.mkQ (w - e) = 0 := by
    rw [map_sub, hquot, sub_self]
  have hmem : w - e ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hzero
  obtain ⟨p, hpdeg, hpEval⟩ :=
    ReedSolomon.mem_code_iff_exists_polynomial.mp hmem
  have hpNat : p.natDegree < 4 := by
    by_cases hp0 : p = 0
    · simp only [hp0, natDegree_zero]
      norm_num
    · rwa [Polynomial.natDegree_lt_iff_degree_lt hp0]
  refine ⟨p, hpNat, ?_⟩
  intro j hji
  have hpAt := congrFun hpEval j
  have he0 : e j = 0 := by
    simp only [e, Pi.single_apply, hji, if_false, Pi.smul_apply,
      smul_eq_mul, mul_zero]
  change w j - e j = p.eval (dom j.1) at hpAt
  rw [he0, sub_zero] at hpAt
  exact hpAt.symm

/-- **Complete column-degeneracy residual.**  In a hypothetical family larger
than sixteen, a quotient column in the independent row plane either routes to
an exceptional direction core in the band `7..13`, or leaves one unique
affine weight-one quotient point. -/
theorem column_degeneracy_routes_to_exceptional_band_or_affine_weight_one
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = 9)
    (hcard : 16 < family.G.card)
    (D : Finset I) (sourceSlope : F[X])
    (hsourceSlope : sourceSlope.natDegree < 4)
    (hcomplement : Fintype.card {i : I // i ∉ D} = 8)
    (u0p : {i : I // i ∉ D} -> F)
    (hrows : QuotientRowsIndependent
      (ReedSolomon.code (puncturedDomain dom D) 4) u0p
      (puncturedResidualDirection dom (u 1) sourceSlope D))
    (i : {i : I // i ∉ D})
    (hcolumnNe :
      quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) i ≠ 0)
    (hcolumn :
      quotientColumn (ReedSolomon.code (puncturedDomain dom D) 4) i ∈
        span F
          ({(ReedSolomon.code (puncturedDomain dom D) 4).mkQ u0p,
            (ReedSolomon.code (puncturedDomain dom D) 4).mkQ
              (puncturedResidualDirection dom (u 1) sourceSlope D)} :
            Set (({i : I // i ∉ D} -> F) ⧸
              ReedSolomon.code (puncturedDomain dom D) 4))) :
    (∃ r : F[X], r.natDegree < 4 ∧
      7 ≤ (directionAgreement dom (u 1) r).card ∧
      (directionAgreement dom (u 1) r).card ≤ 13 ∧
      ∀ beta ∈ family.G, ∃ j : I,
        j ∈ fullAgreement dom (u 0) (u 1) beta (family.q beta) ∧
        j ∉ directionAgreement dom (u 1) r) ∨
      ∃ gamma c : F, c ≠ 0 ∧
        quotientAffinePoint
            (ReedSolomon.code (puncturedDomain dom D) 4) u0p
            (puncturedResidualDirection dom (u 1) sourceSlope D) gamma =
          c • quotientColumn
            (ReedSolomon.code (puncturedDomain dom D) 4) i := by
  rcases column_degeneracy_produces_direction_core_seven_or_affine_weight_one
      dom (u 1) D sourceSlope hsourceSlope hcomplement u0p hrows
      i hcolumnNe hcolumn with
    ⟨r, hr, hseven⟩ | ⟨gamma, c, hc, haffine⟩
  · left
    have hband := direction_core_six_routes_to_exceptional_band
      family hn hthreshold hcard r hr (hseven.trans' (by norm_num))
    exact ⟨r, hband.1, hseven, hband.2.2.1, hband.2.2.2⟩
  · exact Or.inr ⟨gamma, c, hc, haffine⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeDegeneracy

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeDegeneracy
#print axioms directionClass_mem_span_of_rows_dependent
#print axioms column_mem_rowPlane_direction_or_affine_weight_one
#print axioms affine_weight_one_scalar_unique
#print axioms independentUpTo_four_delete
#print axioms card_le_seven_of_projectively_injective_chord_assignment_one_column
#print axioms weightTwoSyndromeLine_card_le_seven_of_representations_one_column
#print axioms uniqueEightCoreResidual_not_exactly_one_contained_column
#print axioms exists_direction_core_of_sparse_punctured_class
#print axioms exists_direction_core_six_of_pairSpan
#print axioms exists_direction_core_seven_of_direction_column
#print axioms dependent_punctured_rows_produce_direction_core_six
#print axioms direction_core_six_routes_to_exceptional_band
#print axioms dependent_punctured_rows_route_to_exceptional_band
#print axioms column_degeneracy_produces_direction_core_seven_or_affine_weight_one
#print axioms exists_punctured_codeword_off_column_of_affine_weight_one
#print axioms column_degeneracy_routes_to_exceptional_band_or_affine_weight_one
