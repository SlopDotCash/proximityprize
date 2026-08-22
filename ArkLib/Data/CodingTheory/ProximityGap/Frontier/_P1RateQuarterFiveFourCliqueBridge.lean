/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAgreementOverlapGraph
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorThirdMomentUpper

/-!
# Five-to-four local rigidity needs only a six-clique

The first clique-consolidation proposal asked directly for five collinear
members in a large overlap clique.  Exact miniature search found the sharp
local obstruction instead: a five-clique can split as four collinear points
plus one outsider.  This file proves that this is already enough globally.

The abstract bridge is elementary but strong.  In a six-point set, suppose
every five-subset contains four points on a line and two distinct points
determine at most one line.  Choose one such four-point line, delete one of
its points, and apply the hypothesis to the remaining five points.  The new
four-point line contains at least two of the three surviving old-line points,
so it is the old line; its fourth point extends that line to five points.

Thus any *domain-specific* proof that every five-vertex overlap clique contains
four collinear polynomial explanations needs no Ramsey growth beyond a
six-clique.  The domain-uniform version is false: the exact `[32,8]` probe
`probe_rate_quarter_five_clique_general_position_counterexample.py` realizes
a rich five-clique with no collinear triple on an adversarial evaluation set.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterFiveFourCliqueBridge

open HalfPredecessorThirdMomentUpper
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines
open P1RateQuarterAgreementOverlapGraph

attribute [local instance] Classical.propDecidable

variable {Point Line : Type*}
variable [DecidableEq Point] [DecidableEq Line]

/-- **Six-point amplification.**  If every five-subset of a six-point set
contains four points on one line, and a pair determines at most one line,
then some line contains five of the six points. -/
theorem five_local_four_collinear_implies_five_collinear_of_card_six
    (G : Finset Point) (onLine : Line → Point → Prop)
    (hG : G.card = 6)
    (hpairUnique : ∀ ell ell' x y, x ≠ y →
      onLine ell x → onLine ell y →
      onLine ell' x → onLine ell' y → ell = ell')
    (hlocal : ∀ S ∈ G.powersetCard 5,
      ∃ ell, 4 ≤ (linePoints S onLine ell).card) :
    ∃ ell, 5 ≤ (linePoints G onLine ell).card := by
  by_contra hnone
  have hlineFour : ∀ ell, (linePoints G onLine ell).card ≤ 4 := by
    intro ell
    have hnot : ¬ 5 ≤ (linePoints G onLine ell).card := by
      intro hfive
      exact hnone ⟨ell, hfive⟩
    omega
  obtain ⟨S, hSG, hScard⟩ :=
    Finset.exists_subset_card_eq (show 5 ≤ G.card by omega)
  have hSpow : S ∈ G.powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hSG, hScard⟩
  obtain ⟨ell, hellFour⟩ := hlocal S hSpow
  have hlineSsub : linePoints S onLine ell ⊆ linePoints G onLine ell := by
    intro z hz
    exact Finset.mem_filter.mpr
      ⟨hSG (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
  have hlineSle : (linePoints S onLine ell).card ≤ 4 :=
    le_trans (Finset.card_le_card hlineSsub) (hlineFour ell)
  have hlineScard : (linePoints S onLine ell).card = 4 := by omega
  let A := linePoints S onLine ell
  have hAcard : A.card = 4 := hlineScard
  have hAG : A ⊆ G := by
    intro z hz
    exact (Finset.mem_filter.mp (hlineSsub hz)).1
  obtain ⟨x, hxA⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
  have hxG : x ∈ G := hAG hxA
  have hxLine : onLine ell x := (Finset.mem_filter.mp hxA).2
  let S' := G.erase x
  have hS'card : S'.card = 5 := by
    simp only [S', Finset.card_erase_of_mem hxG]
    omega
  have hS'pow : S' ∈ G.powersetCard 5 := by
    exact Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, hS'card⟩
  obtain ⟨ell', hell'Four⟩ := hlocal S' hS'pow
  let B := linePoints S' onLine ell'
  have hBcard : 4 ≤ B.card := hell'Four
  have hBsubG : B ⊆ G := by
    intro z hz
    exact Finset.erase_subset x G (Finset.mem_filter.mp hz).1
  have hBAcard : 2 ≤ (B ∩ A).card := by
    have hBAdecomp : (B ∩ A).card + (B \ A).card = B.card :=
      Finset.card_inter_add_card_sdiff B A
    have hBdiffSub : B \ A ⊆ G \ A :=
      Finset.sdiff_subset_sdiff hBsubG (by rfl)
    have hGdiffCard : (G \ A).card = 2 := by
      rw [Finset.card_sdiff_of_subset hAG, hG, hAcard]
    have hBdiffCard : (B \ A).card ≤ 2 := by
      exact le_trans (Finset.card_le_card hBdiffSub) (le_of_eq hGdiffCard)
    omega
  obtain ⟨P, hPsub, hPcard⟩ :=
    Finset.exists_subset_card_eq (show 2 ≤ (B ∩ A).card from hBAcard)
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hPcard
  have hpBA : p ∈ B ∩ A := hPsub (by simp)
  have hqBA : q ∈ B ∩ A := hPsub (by simp)
  have hpA : p ∈ A := (Finset.mem_inter.mp hpBA).2
  have hqA : q ∈ A := (Finset.mem_inter.mp hqBA).2
  have hpB : p ∈ B := (Finset.mem_inter.mp hpBA).1
  have hqB : q ∈ B := (Finset.mem_inter.mp hqBA).1
  have hellEq : ell = ell' :=
    hpairUnique ell ell' p q hpq
      (Finset.mem_filter.mp hpA).2 (Finset.mem_filter.mp hqA).2
      (Finset.mem_filter.mp hpB).2 (Finset.mem_filter.mp hqB).2
  have hlineEraseFour : 4 ≤ (linePoints (G.erase x) onLine ell).card := by
    simpa only [S', hellEq] using hell'Four
  have hlineEraseEq :
      linePoints (G.erase x) onLine ell = (linePoints G onLine ell).erase x := by
    ext z
    simp [linePoints, and_assoc]
  have hxLinePoints : x ∈ linePoints G onLine ell :=
    Finset.mem_filter.mpr ⟨hxG, hxLine⟩
  have hfive : 5 ≤ (linePoints G onLine ell).card := by
    rw [hlineEraseEq, Finset.card_erase_of_mem hxLinePoints] at hlineEraseFour
    omega
  exact hnone ⟨ell, hfive⟩

/-! ## The exact remaining local algebraic residual -/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Agreement-overlap graph on scalar labels, with selected-family membership
folded into adjacency.  This scalar-valued version is convenient for passing
ordinary finsets of labels to the six-point bridge. -/
noncomputable def scalarOverlapGraph
    {N K : ℕ} {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u) : SimpleGraph F where
  Adj x y := x ≠ y ∧ x ∈ family.G ∧ y ∈ family.G ∧
    K ≤ (fullAgreement dom (u 0) (u 1) x (family.q x) ∩
      fullAgreement dom (u 0) (u 1) y (family.q y)).card
  symm := by
    rintro x y ⟨hxy, hx, hy, hcard⟩
    exact ⟨hxy.symm, hy, hx, by simpa only [Finset.inter_comm] using hcard⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- Domain-uniform five-to-four clique rigidity.

**Status: REFUTED.**  The exact `n=32,k=8,t=18` general-position certificate
in `probe_rate_quarter_five_clique_general_position_counterexample.py`
satisfies the rich-vertex, pair-overlap, and no-joint conditions while having
no collinear triple.  The proposition remains useful as the precise premise
of the abstract implication below, and a roots-of-unity-restricted analogue
is not refuted by that certificate. -/
def DomainUniformFiveCliqueFourCollinear : Prop :=
  ∀ {N K : ℕ} [NeZero N] {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (C : Finset F), C ⊆ family.G →
      (scalarOverlapGraph family).IsNClique 5 C →
      ∃ line : LineParameter F,
        4 ≤ (C ∩ pointsOn family line).card

/-- **Local-to-global clique consolidation.**  The sharp five-to-four local
rigidity statement already makes every six-clique contain five collinear
members. -/
theorem sixClique_fiveCollinear_of_fiveCliqueFourCollinear
    (h54 : DomainUniformFiveCliqueFourCollinear (F := F))
    {N K : ℕ} [NeZero N] {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (C : Finset F) (hCG : C ⊆ family.G)
    (hC : (scalarOverlapGraph family).IsNClique 6 C) :
    ∃ line : LineParameter F,
      5 ≤ (C ∩ pointsOn family line).card := by
  let onLine : LineParameter F → F → Prop :=
    fun line gamma => gamma ∈ pointsOn family line
  have hpairUnique : ∀ ell ell' x y, x ≠ y →
      onLine ell x → onLine ell y →
      onLine ell' x → onLine ell' y → ell = ell' := by
    intro ell ell' x y hxy hxell hyell hxell' hyell'
    have hell := secantParameter_eq_of_mem_pointsOn family ell hxell hyell hxy
    have hell' := secantParameter_eq_of_mem_pointsOn family ell' hxell' hyell' hxy
    exact hell.symm.trans hell'
  have hlocal : ∀ S ∈ C.powersetCard 5,
      ∃ line, 4 ≤ (linePoints S onLine line).card := by
    intro S hS
    have hSC : S ⊆ C := (Finset.mem_powersetCard.mp hS).1
    have hSclique : (scalarOverlapGraph family).IsNClique 5 S := by
      refine ⟨hC.isClique.subset hSC, ?_⟩
      exact (Finset.mem_powersetCard.mp hS).2
    obtain ⟨line, hline⟩ := h54 family S (hSC.trans hCG) hSclique
    refine ⟨line, ?_⟩
    have heq : linePoints S onLine line = S ∩ pointsOn family line := by
      ext gamma
      simp [linePoints, onLine]
    rw [heq]
    exact hline
  obtain ⟨line, hline⟩ :=
    five_local_four_collinear_implies_five_collinear_of_card_six
      C onLine hC.card_eq hpairUnique hlocal
  refine ⟨line, ?_⟩
  have heq : linePoints C onLine line = C ∩ pointsOn family line := by
    ext gamma
    simp [linePoints, onLine]
  rw [← heq]
  exact hline

end ArkLib.ProximityGap.Frontier.P1RateQuarterFiveFourCliqueBridge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterFiveFourCliqueBridge
#print axioms five_local_four_collinear_implies_five_collinear_of_card_six
#print axioms sixClique_fiveCollinear_of_fiveCliqueFourCollinear
