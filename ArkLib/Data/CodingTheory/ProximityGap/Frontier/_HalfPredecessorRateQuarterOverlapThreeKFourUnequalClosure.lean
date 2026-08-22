/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFourUnequalResidual

/-!
# The unequal-slope `n = 16`, `k = 4` overlap-three closure

This module combines the common-cubic normal form, the determinant root
budget, and the exact adjacency graph on the ten three-subsets of a
five-coordinate petal. Two distinct off-line points cannot have root blocks
overlapping in two coordinates in both petals. If all ten signatures were
used, however, the two bijective signature maps would force exactly such a
pair: every triple has six overlap-two neighbours inside a ten-element
signature space, and two six-element neighbourhoods inside nine remaining
indices must meet.

Consequently the unequal-slope off-line population is at most nine. Together
with the seven-point reference-line union bound, this closes the final
overlap-three/core-cap cell at `|G| <= 16`.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourPopulation
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalResidual

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

def adjacentTriples (L S : Finset I) : Finset (Finset I) :=
  (L.powersetCard 3).filter fun T => (S ∩ T).card = 2

theorem adjacentTriples_card_eq_six
    (L S : Finset I) (hL : L.card = 5)
    (hSsub : S ⊆ L) (hS : S.card = 3) :
    (adjacentTriples L S).card = 6 := by
  let source := S ×ˢ (L \ S)
  let f : I × I → Finset I := fun p => insert p.2 (S.erase p.1)
  have hLS : (L \ S).card = 2 := by
    rw [Finset.card_sdiff_of_subset hSsub, hL, hS]
  have hsource : source.card = 6 := by
    change (S ×ˢ (L \ S)).card = 6
    rw [Finset.card_product, hS, hLS]
  rw [← hsource]
  symm
  refine Finset.card_bij (fun p _ => f p) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    have hxS : p.1 ∈ S := hp'.1
    have hyLS : p.2 ∈ L \ S := hp'.2
    have hyL : p.2 ∈ L := (Finset.mem_sdiff.mp hyLS).1
    have hyS : p.2 ∉ S := (Finset.mem_sdiff.mp hyLS).2
    rw [adjacentTriples, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · constructor
      · exact Finset.insert_subset hyL (Finset.erase_subset _ _ |>.trans hSsub)
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_erase_of_mem hxS, hS]
        · exact fun hy => hyS (Finset.mem_of_mem_erase hy)
    · have hinter : S ∩ insert p.2 (S.erase p.1) = S.erase p.1 := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hzS, rfl | hz⟩
          · exact (hyS hzS).elim
          · exact hz
        · intro hz
          exact ⟨hz.2, Or.inr hz⟩
      rw [hinter, Finset.card_erase_of_mem hxS, hS]
  · intro p hp q hq heq
    have hp' := Finset.mem_product.mp hp
    have hq' := Finset.mem_product.mp hq
    have hpx : p.1 ∈ S := hp'.1
    have hqx : q.1 ∈ S := hq'.1
    have hpy : p.2 ∉ S := (Finset.mem_sdiff.mp hp'.2).2
    have hqy : q.2 ∉ S := (Finset.mem_sdiff.mp hq'.2).2
    have hx : p.1 = q.1 := by
      have hdiff : S \ f p = S \ f q := congrArg (fun T => S \ T) heq
      have hpDiff : S \ f p = {p.1} := by
        ext z
        simp only [f, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_erase, Finset.mem_singleton]
        aesop
      have hqDiff : S \ f q = {q.1} := by
        ext z
        simp only [f, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_erase, Finset.mem_singleton]
        aesop
      rw [hpDiff, hqDiff] at hdiff
      exact Finset.singleton_inj.mp hdiff
    have hy : p.2 = q.2 := by
      have hdiff : f p \ S = f q \ S :=
        congrArg (fun T => T \ S) heq
      have hpDiff : f p \ S = {p.2} := by
        ext z
        simp only [f, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_erase, Finset.mem_singleton]
        aesop
      have hqDiff : f q \ S = {q.2} := by
        ext z
        simp only [f, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_erase, Finset.mem_singleton]
        aesop
      rw [hpDiff, hqDiff] at hdiff
      exact Finset.singleton_inj.mp hdiff
    exact Prod.ext hx hy
  · intro T hT
    have hT' := Finset.mem_filter.mp hT
    have hTsub : T ⊆ L := (Finset.mem_powersetCard.mp hT'.1).1
    have hTcard : T.card = 3 := (Finset.mem_powersetCard.mp hT'.1).2
    have hinter : (S ∩ T).card = 2 := hT'.2
    have hSmT : (S \ T).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_comm T S, hinter, hS]
    have hTmS : (T \ S).card = 1 := by
      rw [Finset.card_sdiff, hinter, hTcard]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hSmT
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hTmS
    have hxmem : x ∈ S \ T := by rw [hx]; simp
    have hymem : y ∈ T \ S := by rw [hy]; simp
    refine ⟨(x, y), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp hxmem).1,
        Finset.mem_sdiff.mpr ⟨hTsub (Finset.mem_sdiff.mp hymem).1,
          (Finset.mem_sdiff.mp hymem).2⟩⟩
    · apply Finset.ext
      intro z
      simp only [f, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | hz)
        · exact (Finset.mem_sdiff.mp hymem).1
        · by_contra hzT
          have hzDiff : z ∈ S \ T := Finset.mem_sdiff.mpr ⟨hz.2, hzT⟩
          rw [hx] at hzDiff
          exact hz.1 (Finset.mem_singleton.mp hzDiff)
      · intro hzT
        by_cases hzS : z ∈ S
        · by_cases hzx : z = x
          · subst z
            exact ((Finset.mem_sdiff.mp hxmem).2 hzT).elim
          · exact Or.inr ⟨hzx, hzS⟩
        · have hzDiff : z ∈ T \ S := Finset.mem_sdiff.mpr ⟨hzT, hzS⟩
          rw [hy] at hzDiff
          exact Or.inl (Finset.mem_singleton.mp hzDiff)

theorem paired_triples_exists_double_adjacent
    {J : Type} [Fintype J] [DecidableEq J]
    (G : Finset J) (L R : Finset I)
    (A B : J → Finset I)
    (hG : G.card = 10) (hL : L.card = 5) (hR : R.card = 5)
    (hAdata : ∀ j ∈ G, A j ⊆ L ∧ (A j).card = 3)
    (hBdata : ∀ j ∈ G, B j ⊆ R ∧ (B j).card = 3)
    (hAinj : Set.InjOn A (G : Set J))
    (hBinj : Set.InjOn B (G : Set J))
    (hAsurj : ∀ S ∈ L.powersetCard 3, ∃ j ∈ G, A j = S)
    (hBsurj : ∀ T ∈ R.powersetCard 3, ∃ j ∈ G, B j = T) :
    ∃ i ∈ G, ∃ j ∈ G, i ≠ j ∧
      (A i ∩ A j).card = 2 ∧ (B i ∩ B j).card = 2 := by
  have hGpos : 0 < G.card := by omega
  obtain ⟨i, hiG⟩ := Finset.card_pos.mp hGpos
  let NA := (G.erase i).filter fun j => (A i ∩ A j).card = 2
  let NB := (G.erase i).filter fun j => (B i ∩ B j).card = 2
  have hAicard : (A i).card = 3 := (hAdata i hiG).2
  have hBicard : (B i).card = 3 := (hBdata i hiG).2
  have hNA : NA.card = (adjacentTriples L (A i)).card := by
    refine Finset.card_bij (fun j _ => A j) ?_ ?_ ?_
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hjG : j ∈ G := Finset.mem_of_mem_erase hj'.1
      rw [adjacentTriples, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨hAdata j hjG, hj'.2⟩
    · intro j hj k hk heq
      have hjG : j ∈ G :=
        Finset.mem_of_mem_erase (Finset.mem_filter.mp hj).1
      have hkG : k ∈ G :=
        Finset.mem_of_mem_erase (Finset.mem_filter.mp hk).1
      exact hAinj hjG hkG heq
    · intro S hS
      have hS' := Finset.mem_filter.mp hS
      obtain ⟨j, hjG, hjA⟩ := hAsurj S hS'.1
      have hji : j ≠ i := by
        intro hji
        subst j
        have : (A i ∩ A i).card = 2 := by simpa only [hjA] using hS'.2
        simp only [Finset.inter_self, hAicard] at this
        omega
      refine ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hji, hjG⟩, ?_⟩, hjA⟩
      simpa only [hjA] using hS'.2
  have hNB : NB.card = (adjacentTriples R (B i)).card := by
    refine Finset.card_bij (fun j _ => B j) ?_ ?_ ?_
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hjG : j ∈ G := Finset.mem_of_mem_erase hj'.1
      rw [adjacentTriples, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨hBdata j hjG, hj'.2⟩
    · intro j hj k hk heq
      have hjG : j ∈ G :=
        Finset.mem_of_mem_erase (Finset.mem_filter.mp hj).1
      have hkG : k ∈ G :=
        Finset.mem_of_mem_erase (Finset.mem_filter.mp hk).1
      exact hBinj hjG hkG heq
    · intro T hT
      have hT' := Finset.mem_filter.mp hT
      obtain ⟨j, hjG, hjB⟩ := hBsurj T hT'.1
      have hji : j ≠ i := by
        intro hji
        subst j
        have : (B i ∩ B i).card = 2 := by simpa only [hjB] using hT'.2
        simp only [Finset.inter_self, hBicard] at this
        omega
      refine ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hji, hjG⟩, ?_⟩, hjB⟩
      simpa only [hjB] using hT'.2
  have hNAcard : NA.card = 6 := by
    rw [hNA]
    exact adjacentTriples_card_eq_six L (A i) hL (hAdata i hiG).1 hAicard
  have hNBcard : NB.card = 6 := by
    rw [hNB]
    exact adjacentTriples_card_eq_six R (B i) hR (hBdata i hiG).1 hBicard
  have hNA_sub : NA ⊆ G.erase i := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hNB_sub : NB ⊆ G.erase i := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hunionSub : NA ∪ NB ⊆ G.erase i := Finset.union_subset hNA_sub hNB_sub
  have hunionCard := Finset.card_le_card hunionSub
  have heraseCard : (G.erase i).card = 9 := by
    rw [Finset.card_erase_of_mem hiG, hG]
  have hsum := Finset.card_union_add_card_inter NA NB
  have hinterPos : 0 < (NA ∩ NB).card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hinterPos
  have hjNA := (Finset.mem_inter.mp hj).1
  have hjNB := (Finset.mem_inter.mp hj).2
  have hjNA' := Finset.mem_filter.mp hjNA
  have hjNB' := Finset.mem_filter.mp hjNB
  have hjErase := Finset.mem_erase.mp hjNA'.1
  exact ⟨i, hiG, j, hjErase.2, fun h => hjErase.1 h.symm,
    hjNA'.2, hjNB'.2⟩

theorem cubicLocatorCompatible_left_unique
    (dom : I ↪ F) (C0 L S S' T : Finset I)
    (hdisj : Disjoint C0 L)
    (hLcard : L.card = 5)
    (hSsub : S ⊆ L) (hScard : S.card = 3)
    (hS'sub : S' ⊆ L) (hS'card : S'.card = 3)
    (hcompat : CubicLocatorCompatible dom C0 S T)
    (hcompat' : CubicLocatorCompatible dom C0 S' T) :
    S = S' := by
  have hswap : CubicLocatorCompatible dom C0 T S := by
    obtain ⟨a, b, c, ha, hb, hrel⟩ := hcompat
    refine ⟨b, a, -c, hb, ha, ?_⟩
    simp only [map_neg]
    linear_combination -hrel
  have hswap' : CubicLocatorCompatible dom C0 T S' := by
    obtain ⟨a, b, c, ha, hb, hrel⟩ := hcompat'
    refine ⟨b, a, -c, hb, ha, ?_⟩
    simp only [map_neg]
    linear_combination -hrel
  exact cubicLocatorCompatible_right_unique
    dom C0 L T S S' hdisj hLcard hSsub hScard hS'sub hS'card
      hswap hswap'

theorem firstRootBlockAt_injOn_of_relevant_core_cap
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8) :
    Set.InjOn (firstRootBlockAt family line1)
      (offBothPoints family line1 line2 : Set F) := by
  let C0 := commonCoreBlock dom (u 0) (u 1) line1 line2
  let R := jointCore dom (u 0) (u 1) line2.1 line2.2 \ C0
  have hRcard : R.card = 5 := by
    simpa only [R, C0] using
      second_petal_card_eq_five (dom := dom) (u 0) (u 1)
        line1 line2 hcore2 hinter
  have hdisj : Disjoint C0 R := by
    rw [Finset.disjoint_left]
    intro i hiC hiR
    exact (Finset.mem_sdiff.mp hiR).2 hiC
  intro gamma hgamma beta hbeta hfirstEq
  have hgammaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter (by simpa using hgamma)
  have hbetaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter (by simpa using hbeta)
  have hsecondEq : secondRootBlockAt family line2 gamma =
      secondRootBlockAt family line2 beta := by
    apply cubicLocatorCompatible_right_unique
      dom C0 R (firstRootBlockAt family line1 gamma)
        (secondRootBlockAt family line2 gamma)
        (secondRootBlockAt family line2 beta)
        hdisj hRcard
    · simpa only [R, C0] using hgammaData.second_subset
    · exact hgammaData.second_card
    · simpa only [R, C0] using hbetaData.second_subset
    · exact hbetaData.second_card
    · exact hgammaData.compatible
    · simpa only [hfirstEq] using hbetaData.compatible
  have hagreementEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) =
        fullAgreement dom (u 0) (u 1) beta (family.q beta) := by
    calc
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) =
          ((firstRootBlockAt family line1 gamma ∪
            secondRootBlockAt family line2 gamma) ∪
              (Finset.univ \
                (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
                  jointCore dom (u 0) (u 1) line2.1 line2.2))) :=
        hgammaData.agreement_partition
      _ = ((firstRootBlockAt family line1 beta ∪
            secondRootBlockAt family line2 beta) ∪
              (Finset.univ \
                (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
                  jointCore dom (u 0) (u 1) line2.1 line2.2))) := by
        rw [hfirstEq, hsecondEq]
      _ = fullAgreement dom (u 0) (u 1) beta (family.q beta) :=
        hbetaData.agreement_partition.symm
  by_contra hne
  let sec := secantParameter family gamma beta
  have hsec : sec ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaData.gamma_mem hbetaData.gamma_mem hne
  have hgammaOn := first_point_mem_pointsOn_secant
    family (beta := beta) hgammaData.gamma_mem
  have hbetaOn := second_point_mem_pointsOn_secant
    family (gamma := gamma) hbetaData.gamma_mem hne
  have hgammaEq := (mem_pointsOn_iff family sec gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family sec beta).mp hbetaOn |>.2
  have hintersection :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) =
        jointCore dom (u 0) (u 1) sec.1 sec.2 := by
    simpa only [hgammaEq, hbetaEq] using
      (fullAgreement_inter_eq_jointCore
        dom (u 0) (u 1) sec.1 sec.2 hne)
  have hcoreNine :
      (jointCore dom (u 0) (u 1) sec.1 sec.2).card = 9 := by
    rw [← hintersection, hagreementEq, Finset.inter_self]
    exact hbetaData.agreement_card
  have hle := hcoreCap sec hsec
  omega

theorem off_secant_lineDeterminant_ne_zero_of_unequal_slope
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hslope : line2.2 ≠ line1.2)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8)
    {gamma beta : F}
    (hgamma : gamma ∈ offBothPoints family line1 line2)
    (hbeta : beta ∈ offBothPoints family line1 line2)
    (hne : gamma ≠ beta) :
    lineDeterminant line1 line2 (secantParameter family gamma beta) ≠ 0 := by
  have hgammaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter hgamma
  have hbetaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter hbeta
  obtain ⟨qa, qr, alpha, rho, _hqa0, _hqr0, _hqaC, _hqrC,
      _hfactorA0, _hfactorR0, hfactorA, hfactorR, _hprop, _hdegree⟩ :=
    decoded_line_differences_kfour_common_factor
      family line1 line2 hline1 hline2 hinter
  have hrho : rho ≠ 0 := by
    intro hrho
    apply hslope
    have hzero : line2.2 - line1.2 = 0 := by
      rw [hfactorR, hrho]
      simp
    exact sub_eq_zero.mp hzero
  let P := domainRootProduct dom
    (commonCoreBlock dom (u 0) (u 1) line1 line2)
  have hP : P ≠ 0 := by
    exact (domainRootProduct_monic dom
      (commonCoreBlock dom (u 0) (u 1) line1 line2)).ne_zero
  let sec := secantParameter family gamma beta
  have hsec : sec ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaData.gamma_mem hbetaData.gamma_mem hne
  have hgammaOn := first_point_mem_pointsOn_secant
    family (beta := beta) hgammaData.gamma_mem
  have hbetaOn := second_point_mem_pointsOn_secant
    family (gamma := gamma) hbetaData.gamma_mem hne
  have hgammaEq := (mem_pointsOn_iff family sec gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family sec beta).mp hbetaOn |>.2
  intro hdet
  have hcolumn :
      C alpha * (sec.2 - line1.2) - C rho * (sec.1 - line1.1) = 0 := by
    have hprod : P *
        (C alpha * (sec.2 - line1.2) - C rho * (sec.1 - line1.1)) = 0 := by
      calc
        P * (C alpha * (sec.2 - line1.2) - C rho * (sec.1 - line1.1)) =
            lineDeterminant line1 line2 sec := by
          rw [lineDeterminant, hfactorA, hfactorR]
          simp only [P]
          ring
        _ = 0 := hdet
    exact (mul_eq_zero.mp hprod).resolve_left hP
  let lam : F[X] := C rho⁻¹ * (sec.2 - line1.2)
  have hsecR : sec.2 - line1.2 = C rho * lam := by
    simp only [lam]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hrho, map_one, one_mul]
  have hCrho : C rho ≠ (0 : F[X]) := by
    rw [C_ne_zero]
    exact hrho
  have hsecA : sec.1 - line1.1 = C alpha * lam := by
    apply mul_left_cancel₀ hCrho
    calc
      C rho * (sec.1 - line1.1) = C alpha * (sec.2 - line1.2) :=
        (sub_eq_zero.mp hcolumn).symm
      _ = C rho * (C alpha * lam) := by
        rw [hsecR]
        ring
  have hinter' :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3 := by
    simpa only [commonCoreBlock] using hinter
  obtain ⟨cg, _cg2, hcg, _hcg2, _hdg1, _hdg2, hgammaFactor, _⟩ :=
    overlap_three_residual_factorizations
      family (by norm_num) (h := 8) (by simpa using hn) rfl
        (by simpa using hthreshold) line1 line2 hline1 hline2
        hcore1 hcore2 hinter' hgammaData.gamma_mem
        (Finset.mem_filter.mp hgamma).2.1
        (Finset.mem_filter.mp hgamma).2.2
  obtain ⟨cb, _cb2, hcb, _hcb2, _hdb1, _hdb2, hbetaFactor, _⟩ :=
    overlap_three_residual_factorizations
      family (by norm_num) (h := 8) (by simpa using hn) rfl
        (by simpa using hthreshold) line1 line2 hline1 hline2
        hcore1 hcore2 hinter' hbetaData.gamma_mem
        (Finset.mem_filter.mp hbeta).2.1
        (Finset.mem_filter.mp hbeta).2.2
  let Sg := firstRootBlockAt family line1 gamma
  let Sb := firstRootBlockAt family line1 beta
  have hgammaLocator :
      C cg * domainRootProduct dom Sg =
        C (alpha + gamma * rho) * lam := by
    calc
      C cg * domainRootProduct dom Sg =
          lineResidual (family.q gamma) gamma line1 := by
        simpa only [Sg, firstRootBlockAt] using hgammaFactor.symm
      _ = (sec.1 - line1.1) + C gamma * (sec.2 - line1.2) := by
        rw [lineResidual, hgammaEq]
        ring
      _ = C (alpha + gamma * rho) * lam := by
        rw [hsecA, hsecR, C_add, C_mul]
        ring
  have hbetaLocator :
      C cb * domainRootProduct dom Sb =
        C (alpha + beta * rho) * lam := by
    calc
      C cb * domainRootProduct dom Sb =
          lineResidual (family.q beta) beta line1 := by
        simpa only [Sb, firstRootBlockAt] using hbetaFactor.symm
      _ = (sec.1 - line1.1) + C beta * (sec.2 - line1.2) := by
        rw [lineResidual, hbetaEq]
        ring
      _ = C (alpha + beta * rho) * lam := by
        rw [hsecA, hsecR, C_add, C_mul]
        ring
  have htg : alpha + gamma * rho ≠ 0 := by
    intro hzero
    have hleft : C cg * domainRootProduct dom Sg ≠ 0 :=
      mul_ne_zero (by simpa using hcg)
        (domainRootProduct_monic dom Sg).ne_zero
    apply hleft
    rw [hgammaLocator, hzero]
    simp
  have htb : alpha + beta * rho ≠ 0 := by
    intro hzero
    have hleft : C cb * domainRootProduct dom Sb ≠ 0 :=
      mul_ne_zero (by simpa using hcb)
        (domainRootProduct_monic dom Sb).ne_zero
    apply hleft
    rw [hbetaLocator, hzero]
    simp
  have hlocators :
      C ((alpha + beta * rho) * cg) * domainRootProduct dom Sg =
        C ((alpha + gamma * rho) * cb) * domainRootProduct dom Sb := by
    calc
      C ((alpha + beta * rho) * cg) * domainRootProduct dom Sg =
          C (alpha + beta * rho) *
            (C cg * domainRootProduct dom Sg) := by
        rw [C_mul]
        ring
      _ = C (alpha + beta * rho) *
          (C (alpha + gamma * rho) * lam) := by rw [hgammaLocator]
      _ = C (alpha + gamma * rho) *
          (C (alpha + beta * rho) * lam) := by ring
      _ = C (alpha + gamma * rho) *
          (C cb * domainRootProduct dom Sb) := by rw [← hbetaLocator]
      _ = C ((alpha + gamma * rho) * cb) * domainRootProduct dom Sb := by
        rw [C_mul]
        ring
  have hscalar : (alpha + beta * rho) * cg =
      (alpha + gamma * rho) * cb := by
    have hlead := congrArg Polynomial.leadingCoeff hlocators
    simpa only [leadingCoeff_mul, leadingCoeff_C,
      (domainRootProduct_monic dom Sg).leadingCoeff,
      (domainRootProduct_monic dom Sb).leadingCoeff, mul_one] using hlead
  have hscale0 : C ((alpha + beta * rho) * cg) ≠ (0 : F[X]) := by
    rw [C_ne_zero]
    exact mul_ne_zero htb hcg
  have hrootProductEq : domainRootProduct dom Sg = domainRootProduct dom Sb := by
    apply mul_left_cancel₀ hscale0
    rw [hlocators, hscalar]
  have hfirstEq : firstRootBlockAt family line1 gamma =
      firstRootBlockAt family line1 beta := by
    ext i
    rw [← eval_domainRootProduct_eq_zero_iff_mem dom Sg i,
      ← eval_domainRootProduct_eq_zero_iff_mem dom Sb i, hrootProductEq]
  let C0 := commonCoreBlock dom (u 0) (u 1) line1 line2
  let R := jointCore dom (u 0) (u 1) line2.1 line2.2 \ C0
  have hRcard : R.card = 5 := by
    simpa only [R, C0] using
      second_petal_card_eq_five (dom := dom) (u 0) (u 1)
        line1 line2 hcore2 hinter
  have hdisj : Disjoint C0 R := by
    rw [Finset.disjoint_left]
    intro i hiC hiR
    exact (Finset.mem_sdiff.mp hiR).2 hiC
  have hsecondEq : secondRootBlockAt family line2 gamma =
      secondRootBlockAt family line2 beta := by
    apply cubicLocatorCompatible_right_unique
      dom C0 R (firstRootBlockAt family line1 gamma)
        (secondRootBlockAt family line2 gamma)
        (secondRootBlockAt family line2 beta)
        hdisj hRcard
    · simpa only [R, C0] using hgammaData.second_subset
    · exact hgammaData.second_card
    · simpa only [R, C0] using hbetaData.second_subset
    · exact hbetaData.second_card
    · exact hgammaData.compatible
    · simpa only [hfirstEq] using hbetaData.compatible
  have hagreementEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) =
        fullAgreement dom (u 0) (u 1) beta (family.q beta) := by
    calc
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) =
          ((firstRootBlockAt family line1 gamma ∪
            secondRootBlockAt family line2 gamma) ∪
              (Finset.univ \
                (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
                  jointCore dom (u 0) (u 1) line2.1 line2.2))) :=
        hgammaData.agreement_partition
      _ = ((firstRootBlockAt family line1 beta ∪
            secondRootBlockAt family line2 beta) ∪
              (Finset.univ \
                (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
                  jointCore dom (u 0) (u 1) line2.1 line2.2))) := by
        rw [hfirstEq, hsecondEq]
      _ = fullAgreement dom (u 0) (u 1) beta (family.q beta) :=
        hbetaData.agreement_partition.symm
  have hintersection :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) =
        jointCore dom (u 0) (u 1) sec.1 sec.2 := by
    simpa only [hgammaEq, hbetaEq] using
      (fullAgreement_inter_eq_jointCore
        dom (u 0) (u 1) sec.1 sec.2 hne)
  have hcoreNine :
      (jointCore dom (u 0) (u 1) sec.1 sec.2).card = 9 := by
    rw [← hintersection, hagreementEq, Finset.inter_self]
    exact hbetaData.agreement_card
  have hle := hcoreCap sec hsec
  omega

theorem off_rootBlocks_not_both_inter_card_two_of_unequal_slope
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hslope : line2.2 ≠ line1.2)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8)
    {gamma beta : F}
    (hgamma : gamma ∈ offBothPoints family line1 line2)
    (hbeta : beta ∈ offBothPoints family line1 line2)
    (hne : gamma ≠ beta) :
    ¬ ((firstRootBlockAt family line1 gamma ∩
          firstRootBlockAt family line1 beta).card = 2 ∧
       (secondRootBlockAt family line2 gamma ∩
          secondRootBlockAt family line2 beta).card = 2) := by
  intro hoverlap
  have hgammaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter hgamma
  have hbetaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter hbeta
  let S := firstRootBlockAt family line1 gamma ∩
    firstRootBlockAt family line1 beta
  let T := secondRootBlockAt family line2 gamma ∩
    secondRootBlockAt family line2 beta
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let U := Finset.univ \ (D1 ∪ D2)
  let W := (S ∪ T) ∪ U
  have hScard : S.card = 2 := by simpa only [S] using hoverlap.1
  have hTcard : T.card = 2 := by simpa only [T] using hoverlap.2
  have hUcard : U.card = 3 := by
    have hunionInter := Finset.card_union_add_card_inter D1 D2
    have hD1 : D1.card = 8 := by simpa only [D1] using hcore1
    have hD2 : D2.card = 8 := by simpa only [D2] using hcore2
    have hC : (D1 ∩ D2).card = 3 := by
      simpa only [D1, D2, commonCoreBlock] using hinter
    have hU : U.card = Fintype.card I - (D1 ∪ D2).card := by
      simp only [U, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    omega
  have hSTdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    have hiSg := (Finset.mem_inter.mp hiS).1
    have hiTg := (Finset.mem_inter.mp hiT).1
    have hiL := hgammaData.first_subset hiSg
    have hiR := hgammaData.second_subset hiTg
    have hiD1 : i ∈ D1 := by
      exact (Finset.mem_sdiff.mp (by
        simpa only [D1, commonCoreBlock] using hiL)).1
    have hiD2 : i ∈ D2 := by
      exact (Finset.mem_sdiff.mp (by
        simpa only [D2, commonCoreBlock] using hiR)).1
    have hiC : i ∈ commonCoreBlock dom (u 0) (u 1) line1 line2 := by
      simpa only [commonCoreBlock, D1, D2] using
        (Finset.mem_inter.mpr ⟨hiD1, hiD2⟩)
    exact (Finset.mem_sdiff.mp (by
      simpa only [D1, commonCoreBlock] using hiL)).2 hiC
  have hSTUdisj : Disjoint (S ∪ T) U := by
    rw [Finset.disjoint_left]
    intro i hiST hiU
    have hiNot := (Finset.mem_sdiff.mp hiU).2
    rcases Finset.mem_union.mp hiST with hiS | hiT
    · have hiSg := (Finset.mem_inter.mp hiS).1
      have hiL := hgammaData.first_subset hiSg
      apply hiNot
      exact Finset.mem_union_left _
        (Finset.mem_sdiff.mp (by
          simpa only [D1, commonCoreBlock] using hiL)).1
    · have hiTg := (Finset.mem_inter.mp hiT).1
      have hiR := hgammaData.second_subset hiTg
      apply hiNot
      exact Finset.mem_union_right _
        (Finset.mem_sdiff.mp (by
          simpa only [D2, commonCoreBlock] using hiR)).1
  have hWcard : W.card = 7 := by
    change ((S ∪ T) ∪ U).card = 7
    rw [Finset.card_union_of_disjoint hSTUdisj,
      Finset.card_union_of_disjoint hSTdisj, hScard, hTcard, hUcard]
  have hWsub : W ⊆
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        fullAgreement dom (u 0) (u 1) beta (family.q beta) := by
    intro i hiW
    change i ∈ (S ∪ T) ∪ U at hiW
    rw [hgammaData.agreement_partition, hbetaData.agreement_partition]
    rcases Finset.mem_union.mp hiW with hiST | hiU
    · rcases Finset.mem_union.mp hiST with hiS | hiT
      · have hiPair := Finset.mem_inter.mp hiS
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hiPair.1),
            Finset.mem_union_left _ (Finset.mem_union_left _ hiPair.2)⟩
      · have hiPair := Finset.mem_inter.mp hiT
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hiPair.1),
            Finset.mem_union_left _ (Finset.mem_union_right _ hiPair.2)⟩
    · have hiU' : i ∈ Finset.univ \
          (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
            jointCore dom (u 0) (u 1) line2.1 line2.2) := by
        simpa only [U, D1, D2] using hiU
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ hiU', Finset.mem_union_right _ hiU'⟩
  let sec := secantParameter family gamma beta
  have hsec : sec ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaData.gamma_mem hbetaData.gamma_mem hne
  have hgammaOn := first_point_mem_pointsOn_secant
    family (beta := beta) hgammaData.gamma_mem
  have hbetaOn := second_point_mem_pointsOn_secant
    family (gamma := gamma) hbetaData.gamma_mem hne
  have hgammaEq := (mem_pointsOn_iff family sec gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family sec beta).mp hbetaOn |>.2
  have hintersection :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) =
        jointCore dom (u 0) (u 1) sec.1 sec.2 := by
    simpa only [hgammaEq, hbetaEq] using
      (fullAgreement_inter_eq_jointCore
        dom (u 0) (u 1) sec.1 sec.2 hne)
  have hcoreSec : 7 ≤
      (jointCore dom (u 0) (u 1) sec.1 sec.2).card := by
    rw [← hintersection]
    exact hWcard ▸ Finset.card_le_card hWsub
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  have hdegSec := lineParameter_degree_lt family hsec
  have hdeg : ∀ line ∈ ({line1, line2, sec} : Finset (PolynomialLine F)),
      line.1.natDegree < 4 ∧ line.2.natDegree < 4 := by
    intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline
    rcases hline with rfl | rfl | rfl
    · exact hdeg1
    · exact hdeg2
    · exact hdegSec
  have hcoreUnion :
      (coreUnion dom (u 0) (u 1) line1 line2 sec).card ≤ 16 := by
    have hsub : coreUnion dom (u 0) (u 1) line1 line2 sec ⊆ Finset.univ :=
      Finset.subset_univ _
    have := Finset.card_le_card hsub
    simpa only [Finset.card_univ, hn] using this
  have hdetZero : lineDeterminant line1 line2 sec = 0 := by
    apply lineDeterminant_eq_zero_of_two_mul_pred_add_coreUnion_lt_coreSum
      (k := 4) (by norm_num) dom (u 0) (u 1) line1 line2 sec hdeg
    omega
  exact (off_secant_lineDeterminant_ne_zero_of_unequal_slope
    family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
      hinter hslope hcoreCap hgamma hbeta hne) hdetZero

/-- The second root-block signature is also injective on off-both points.
This is the symmetric locator-matching consequence, followed by injectivity
of the first signature. -/
theorem secondRootBlockAt_injOn_of_relevant_core_cap
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8) :
    Set.InjOn (secondRootBlockAt family line2)
      (offBothPoints family line1 line2 : Set F) := by
  let C0 := commonCoreBlock dom (u 0) (u 1) line1 line2
  let L := jointCore dom (u 0) (u 1) line1.1 line1.2 \ C0
  have hLcard : L.card = 5 := by
    simpa only [L, C0] using
      first_petal_card_eq_five (dom := dom) (u 0) (u 1)
        line1 line2 hcore1 hinter
  have hdisj : Disjoint C0 L := by
    rw [Finset.disjoint_left]
    intro i hiC hiL
    exact (Finset.mem_sdiff.mp hiL).2 hiC
  have hfirstInj := firstRootBlockAt_injOn_of_relevant_core_cap
    family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
      hinter hcoreCap
  intro gamma hgamma beta hbeta hsecondEq
  have hgammaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter (by simpa using hgamma)
  have hbetaData := kfourOffPointData family hn hthreshold line1 line2
    hline1 hline2 hcore1 hcore2 hinter (by simpa using hbeta)
  apply hfirstInj hgamma hbeta
  apply cubicLocatorCompatible_left_unique
    dom C0 L
      (firstRootBlockAt family line1 gamma)
      (firstRootBlockAt family line1 beta)
      (secondRootBlockAt family line2 gamma)
      hdisj hLcard
  · simpa only [L, C0] using hgammaData.first_subset
  · exact hgammaData.first_card
  · simpa only [L, C0] using hbetaData.first_subset
  · exact hbetaData.first_card
  · exact hgammaData.compatible
  · simpa only [hsecondEq] using hbetaData.compatible

/-- **Unequal-slope off-both bound.**  Ten off-both points would realize all
ten three-subsets in each five-coordinate petal.  The paired-neighbourhood
count then forces two points with overlap two in both petals, contradicting
the determinant root budget. -/
theorem offBothPoints_card_le_nine_of_unequal_slope
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hslope : line2.2 ≠ line1.2)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8) :
    (offBothPoints family line1 line2).card ≤ 9 := by
  let O := offBothPoints family line1 line2
  let C0 := commonCoreBlock dom (u 0) (u 1) line1 line2
  let L := jointCore dom (u 0) (u 1) line1.1 line1.2 \ C0
  let R := jointCore dom (u 0) (u 1) line2.1 line2.2 \ C0
  by_contra hnot
  have hgt : 9 < (offBothPoints family line1 line2).card :=
    Nat.lt_of_not_ge hnot
  have hleTen := offBothPoints_card_le_ten_of_relevant_core_cap
    family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
      hinter hcoreCap
  have hOcard : O.card = 10 := by
    have hle : O.card ≤ 10 := by simpa only [O] using hleTen
    have hgt' : 9 < O.card := by simpa only [O] using hgt
    omega
  have hLcard : L.card = 5 := by
    simpa only [L, C0] using
      first_petal_card_eq_five (dom := dom) (u 0) (u 1)
        line1 line2 hcore1 hinter
  have hRcard : R.card = 5 := by
    simpa only [R, C0] using
      second_petal_card_eq_five (dom := dom) (u 0) (u 1)
        line1 line2 hcore2 hinter
  let A : F → Finset I := firstRootBlockAt family line1
  let B : F → Finset I := secondRootBlockAt family line2
  have hAdata : ∀ gamma ∈ O, A gamma ⊆ L ∧ (A gamma).card = 3 := by
    intro gamma hgamma
    have hdata := kfourOffPointData family hn hthreshold line1 line2
      hline1 hline2 hcore1 hcore2 hinter (by simpa only [O] using hgamma)
    exact ⟨by simpa only [A, L, C0] using hdata.first_subset,
      by simpa only [A] using hdata.first_card⟩
  have hBdata : ∀ gamma ∈ O, B gamma ⊆ R ∧ (B gamma).card = 3 := by
    intro gamma hgamma
    have hdata := kfourOffPointData family hn hthreshold line1 line2
      hline1 hline2 hcore1 hcore2 hinter (by simpa only [O] using hgamma)
    exact ⟨by simpa only [B, R, C0] using hdata.second_subset,
      by simpa only [B] using hdata.second_card⟩
  have hAinj : Set.InjOn A (O : Set F) := by
    simpa only [A, O] using
      (firstRootBlockAt_injOn_of_relevant_core_cap
        family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
          hinter hcoreCap)
  have hBinj : Set.InjOn B (O : Set F) := by
    simpa only [B, O] using
      (secondRootBlockAt_injOn_of_relevant_core_cap
        family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
          hinter hcoreCap)
  have hLPcard : (L.powersetCard 3).card = 10 := by
    rw [Finset.card_powersetCard, hLcard]
    norm_num [Nat.choose]
  have hRPcard : (R.powersetCard 3).card = 10 := by
    rw [Finset.card_powersetCard, hRcard]
    norm_num [Nat.choose]
  have hAimage : O.image A = L.powersetCard 3 := by
    apply Finset.eq_of_subset_of_card_le
    · intro S hS
      obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hS
      exact Finset.mem_powersetCard.mpr (hAdata gamma hgamma)
    · rw [Finset.card_image_of_injOn hAinj, hOcard, hLPcard]
  have hBimage : O.image B = R.powersetCard 3 := by
    apply Finset.eq_of_subset_of_card_le
    · intro T hT
      obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hT
      exact Finset.mem_powersetCard.mpr (hBdata gamma hgamma)
    · rw [Finset.card_image_of_injOn hBinj, hOcard, hRPcard]
  have hAsurj : ∀ S ∈ L.powersetCard 3, ∃ gamma ∈ O, A gamma = S := by
    intro S hS
    rw [← hAimage] at hS
    exact Finset.mem_image.mp hS
  have hBsurj : ∀ T ∈ R.powersetCard 3, ∃ gamma ∈ O, B gamma = T := by
    intro T hT
    rw [← hBimage] at hT
    exact Finset.mem_image.mp hT
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hfirstInter, hsecondInter⟩ :=
    paired_triples_exists_double_adjacent
      O L R A B hOcard hLcard hRcard hAdata hBdata
        hAinj hBinj hAsurj hBsurj
  apply off_rootBlocks_not_both_inter_card_two_of_unequal_slope
    family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
      hinter hslope hcoreCap
      (by simpa only [O] using hgamma) (by simpa only [O] using hbeta) hne
  exact ⟨by simpa only [A] using hfirstInter,
    by simpa only [B] using hsecondInter⟩

/-- **Complete `n = 16`, `k = 4` overlap-three/core-cap closure.**  Equal
reference slopes use the direction-error line cap; unequal slopes use the
paired cubic-locator adjacency obstruction. -/
theorem card_le_sixteen_of_overlap_three_core_cap
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8) :
    family.G.card ≤ 16 := by
  by_cases hslope : line2.2 = line1.2
  · exact card_le_sixteen_of_equal_slope_overlap_three_core_cap
      family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
        hinter hslope hcoreCap
  · have hlines := reference_pointsOn_union_card_le_seven
      family hn line1 line2 hline1 hline2 hcore1 hcore2 hinter
    have hoff := offBothPoints_card_le_nine_of_unequal_slope
      family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
        hinter hslope hcoreCap
    have hcover : family.G ⊆
        (pointsOn family line1 ∪ pointsOn family line2) ∪
          offBothPoints family line1 line2 := by
      intro gamma hgamma
      by_cases hfirst :
          family.q gamma = line1.1 + C gamma * line1.2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          ((mem_pointsOn_iff family line1 gamma).mpr ⟨hgamma, hfirst⟩))
      by_cases hsecond :
          family.q gamma = line2.1 + C gamma * line2.2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((mem_pointsOn_iff family line2 gamma).mpr ⟨hgamma, hsecond⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hgamma, hfirst, hsecond⟩)
    have hcoverCard := Finset.card_le_card hcover
    have hall := Finset.card_union_le
      (pointsOn family line1 ∪ pointsOn family line2)
      (offBothPoints family line1 line2)
    omega

#print axioms adjacentTriples_card_eq_six
#print axioms paired_triples_exists_double_adjacent
#print axioms off_secant_lineDeterminant_ne_zero_of_unequal_slope
#print axioms off_rootBlocks_not_both_inter_card_two_of_unequal_slope
#print axioms offBothPoints_card_le_nine_of_unequal_slope
#print axioms card_le_sixteen_of_overlap_three_core_cap

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure
