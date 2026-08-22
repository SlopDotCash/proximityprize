/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines

/-!
# P1 rate-quarter predecessor: iterated forced secants and pencil consolidation

The agreement-overlap graph theorem forces, among any six predecessor
explanations, a pair whose unique polynomial secant has a joint core of size at
least `K = 2^28`.  This file iterates that forcing.

* **Subset forcing.**  The six-scalar statement holds inside any subset of the
  selected family, since the forcing only inspects the six chosen agreement
  sets.
* **Forced secant matching.**  Greedy removal of forced pairs turns
  independence at most five into a near-perfect matching: every selected family
  contains a pairwise-disjoint set of scalar pairs, each with a `K`-core
  secant, covering all but at most five scalars.  An over-budget family
  (`N < |G|`) therefore contains at least `2^29 - 2` disjoint forced pairs.
* **Pencil consolidation rigidity.**  Distinct polynomial lines with
  components of degree `< K` have joint cores meeting in at most `K - 1`
  coordinates.  Hence any two forced pairs whose secant cores overlap in at
  least `K` coordinates lie on one common source pencil.  Consolidating the
  matched pairs into few pencils is exactly a clustering of their cores under
  this `K`-overlap relation.
* **Saturation ceiling (honest barrier).**  The constant-weight Plotkin
  denominator `T^2 - N*lambda` is positive only for overlap thresholds
  `lambda < 327272222`.  The saturated two-fresh core size `T - 2 = 592794964`
  lies far above this ceiling, so no pairwise Plotkin count — with any number
  of sets — can force saturated-core overlaps directly.  The remaining
  consolidation step (at most four saturated pencils) genuinely requires
  geometric input beyond pairwise agreement counting.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open Finset Polynomial
open _root_.ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching

open ConstantWeightPlotkinBound
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines

attribute [local instance] Classical.propDecidable

/-- Prize length.  (Same value as in `_P1RateQuarterAgreementOverlapGraph`;
restated locally to keep this file's build independent.) -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter Reed--Solomon dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement threshold at the lattice predecessor of the saturated
common-factor endpoint. -/
abbrev T : Nat := 592794966

/-! ## Distinct-line core rigidity -/

section Rigidity

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Distinct-line core cap.**  Two polynomial lines that differ in intercept
or slope, with all components of degree `< k`, have joint cores meeting in at
most `k - 1` coordinates. -/
theorem jointCore_inter_card_le_of_ne
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {a r a' r' : F[X]}
    (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    (hadeg' : a'.natDegree < k) (hrdeg' : r'.natDegree < k)
    (hne : a ≠ a' ∨ r ≠ r') :
    (jointCore dom u₀ u₁ a r ∩ jointCore dom u₀ u₁ a' r').card ≤ k - 1 := by
  rcases hne with hne | hne
  · have hp0 : a - a' ≠ 0 := sub_ne_zero.mpr hne
    have hpdeg : (a - a').natDegree < k :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hadeg hadeg')
    refine le_trans (Finset.card_le_card ?_)
      (domain_root_card_le_pred dom hk _ hp0 hpdeg)
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub]
    rw [hi.1.1, hi.2.1, sub_self]
  · have hp0 : r - r' ≠ 0 := sub_ne_zero.mpr hne
    have hpdeg : (r - r').natDegree < k :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hrdeg hrdeg')
    refine le_trans (Finset.card_le_card ?_)
      (domain_root_card_le_pred dom hk _ hp0 hpdeg)
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub]
    rw [hi.1.2, hi.2.2, sub_self]

end Rigidity

/-! ## Iterated forcing at the P1 predecessor -/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Shorthand for the joint core of the canonical secant through two selected
scalars. -/
noncomputable def secantCore
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (gamma beta : F) : Finset (Fin N) :=
  jointCore dom (u 0) (u 1)
    (secantParameter family gamma beta).1
    (secantParameter family gamma beta).2

/-- **Six-set overlap forcing.**  Among any six subsets of the P1 coordinate
set, each of cardinality at least the predecessor agreement threshold, two
distinct sets overlap in at least the Reed--Solomon dimension `K`.  (Local
restatement of the pin in `_P1RateQuarterAgreementOverlapGraph`.) -/
theorem exists_pair_inter_card_ge_K_of_six
    (A : Fin 6 → Finset (Fin N))
    (hsize : ∀ i, T ≤ (A i).card) :
    ∃ i j : Fin 6, i ≠ j ∧ K ≤ (A i ∩ A j).card := by
  classical
  by_contra hnot
  push Not at hnot
  let A' : Fin 6 → Finset (Fin N) := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hA'sub : ∀ i, A' i ⊆ A i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hA'card : ∀ i, (A' i).card = T := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hpair : ∀ i j, i ≠ j → (A' i ∩ A' j).card ≤ K - 1 := by
    intro i j hij
    have hsmall : (A i ∩ A j).card < K := hnot i j hij
    have hsub : A' i ∩ A' j ⊆ A i ∩ A j :=
      Finset.inter_subset_inter (hA'sub i) (hA'sub j)
    have hle := Finset.card_le_card hsub
    omega
  have hplot := constantWeight_plotkin A' T (K - 1) hA'card hpair
  simp only [Fintype.card_fin] at hplot
  norm_num [N, K, T] at hplot

/-- **Subset forcing.**  The six-scalar overlap forcing localizes to any
subset of the selected family: six scalars drawn from the subset already
contain a pair with a `K`-core secant. -/
theorem exists_pair_large_secant_core_of_subset
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {S : Finset F} (hS : S ⊆ family.G) (hcard : 6 ≤ S.card)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    ∃ gamma ∈ S, ∃ beta ∈ S, gamma ≠ beta ∧
      K ≤ (secantCore family gamma beta).card := by
  classical
  obtain ⟨S6, hS6sub, hS6card⟩ := Finset.exists_subset_card_eq hcard
  have he : S6 ≃ Fin 6 := by
    rw [← hS6card]
    exact S6.equivFin
  let label : Fin 6 → F := fun i => (he.symm i : F)
  have hinjective : Function.Injective label := by
    intro i j hij
    apply he.symm.injective
    exact Subtype.ext hij
  have hlabelS : ∀ i, label i ∈ S := by
    intro i
    exact hS6sub (he.symm i).2
  have hlabel : ∀ i, label i ∈ family.G := fun i => hS (hlabelS i)
  let A : Fin 6 → Finset (Fin N) := fun i =>
    fullAgreement dom (u 0) (u 1) (label i) (family.q (label i))
  obtain ⟨i, j, hij, hoverlap⟩ :=
    exists_pair_inter_card_ge_K_of_six A
      (fun i => hsize (label i) (hlabel i))
  have hscalar : label i ≠ label j := hinjective.ne hij
  let line := secantParameter family (label i) (label j)
  have hiOn : label i ∈ pointsOn family line :=
    first_point_mem_pointsOn_secant family (beta := label j) (hlabel i)
  have hjOn : label j ∈ pointsOn family line :=
    second_point_mem_pointsOn_secant family (gamma := label i)
      (hlabel j) hscalar
  have hiLine := (mem_pointsOn_iff family line (label i)).mp hiOn |>.2
  have hjLine := (mem_pointsOn_iff family line (label j)).mp hjOn |>.2
  refine ⟨label i, hlabelS i, label j, hlabelS j, hscalar, ?_⟩
  show K ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card
  rw [← fullAgreement_inter_eq_jointCore
    dom (u 0) (u 1) line.1 line.2 hscalar]
  simpa only [A, line, hiLine, hjLine] using hoverlap

/-- A forced secant matching inside a scalar set `S`: pairwise-disjoint pairs
of distinct members of `S`, each with a `K`-core canonical secant. -/
def ForcedSecantMatching
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (S : Finset F) (M : Finset (F × F)) : Prop :=
  (∀ p ∈ M, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧
    K ≤ (secantCore family p.1 p.2).card) ∧
  ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

/-- Forced secant matchings are monotone in the ambient scalar set. -/
theorem ForcedSecantMatching.mono
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    {family : BadScalarRichPointFamily dom K delta u}
    {S S' : Finset F} {M : Finset (F × F)}
    (hM : ForcedSecantMatching family S M) (hsub : S ⊆ S') :
    ForcedSecantMatching family S' M := by
  refine ⟨fun p hp => ?_, hM.2⟩
  obtain ⟨h1, h2, h3, h4⟩ := hM.1 p hp
  exact ⟨hsub h1, hsub h2, h3, h4⟩

/-- **Greedy matching extraction.**  Iterating the subset forcing removes
disjoint forced pairs until at most five scalars remain: every subset of the
selected family carries a forced secant matching covering all but at most
five of its members. -/
theorem exists_forced_secant_matching_on
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    ∀ n : ℕ, ∀ S : Finset F, S ⊆ family.G → S.card ≤ n →
      ∃ M : Finset (F × F),
        ForcedSecantMatching family S M ∧ S.card ≤ 2 * M.card + 5 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS hcard
    by_cases hsmall : S.card ≤ 5
    · exact ⟨∅, ⟨fun p hp => absurd hp (Finset.notMem_empty p),
        fun p hp => absurd hp (Finset.notMem_empty p)⟩, by omega⟩
    · have hsix : 6 ≤ S.card := by omega
      obtain ⟨gamma, hgammaS, beta, hbetaS, hne, hcore⟩ :=
        exists_pair_large_secant_core_of_subset family hS hsix hsize
      set S' : Finset F := (S.erase gamma).erase beta with hS'def
      have hS'subErase : S' ⊆ S.erase gamma := Finset.erase_subset _ _
      have hS'sub : S' ⊆ S := hS'subErase.trans (Finset.erase_subset _ _)
      have hbetaMem : beta ∈ S.erase gamma :=
        Finset.mem_erase.mpr ⟨Ne.symm hne, hbetaS⟩
      have hcardErase : (S.erase gamma).card = S.card - 1 :=
        Finset.card_erase_of_mem hgammaS
      have hcardS' : S'.card = S.card - 2 := by
        rw [hS'def, Finset.card_erase_of_mem hbetaMem, hcardErase]
        omega
      have hgammaNot : gamma ∉ S' := by
        intro hmem
        exact Finset.notMem_erase gamma S (hS'subErase hmem)
      have hbetaNot : beta ∉ S' := by
        intro hmem
        exact Finset.notMem_erase beta (S.erase gamma) hmem
      obtain ⟨M', hM', hcount'⟩ := ih (n - 2) (by omega) S'
        (hS'sub.trans hS) (by omega)
      have hpairNot : (gamma, beta) ∉ M' := by
        intro hmem
        exact hgammaNot (hM'.1 (gamma, beta) hmem).1
      refine ⟨insert (gamma, beta) M', ⟨?_, ?_⟩, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact ⟨hgammaS, hbetaS, hne, hcore⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hM'.1 p hp'
          exact ⟨hS'sub h1, hS'sub h2, h3, h4⟩
      · intro p hp q hq hpq
        rcases Finset.mem_insert.mp hp with rfl | hp' <;>
          rcases Finset.mem_insert.mp hq with hq | hq'
        · exact absurd hq.symm hpq
        · obtain ⟨h1, h2, _h3, _h4⟩ := hM'.1 q hq'
          exact ⟨fun h => hgammaNot (by rw [← h] at h1; exact h1),
            fun h => hgammaNot (by rw [← h] at h2; exact h2),
            fun h => hbetaNot (by rw [← h] at h1; exact h1),
            fun h => hbetaNot (by rw [← h] at h2; exact h2)⟩
        · obtain ⟨h1, h2, _h3, _h4⟩ := hM'.1 p hp'
          subst hq
          exact ⟨fun h => hgammaNot (by rw [h] at h1; exact h1),
            fun h => hbetaNot (by rw [h] at h1; exact h1),
            fun h => hgammaNot (by rw [h] at h2; exact h2),
            fun h => hbetaNot (by rw [h] at h2; exact h2)⟩
        · exact hM'.2 p hp' q hq' hpq
      · rw [Finset.card_insert_of_notMem hpairNot]
        omega

/-- **Full-family matching.**  The selected family at the P1 predecessor
carries a forced secant matching covering all but at most five scalars. -/
theorem exists_forced_secant_matching
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    ∃ M : Finset (F × F),
      ForcedSecantMatching family family.G M ∧
        family.G.card ≤ 2 * M.card + 5 :=
  exists_forced_secant_matching_on family hsize family.G.card family.G
    (fun _ h => h) le_rfl

/-- **Over-budget iteration.**  A selected family exceeding the bad-count
budget `N` contains at least `2^29 - 2` pairwise-disjoint scalar pairs, each
with a `K`-core canonical secant. -/
theorem exists_forced_secant_matching_of_over_budget
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)
    (hover : N < family.G.card) :
    ∃ M : Finset (F × F),
      ForcedSecantMatching family family.G M ∧
        2 ^ 29 - 2 ≤ M.card := by
  obtain ⟨M, hM, hcount⟩ := exists_forced_secant_matching family hsize
  refine ⟨M, hM, ?_⟩
  have hN : N = 1073741824 := by norm_num [N]
  have h29 : (2 : ℕ) ^ 29 = 536870912 := by norm_num
  omega

/-! ## Pencil consolidation rigidity -/

/-- **Consolidation criterion.**  Two forced pairs whose secant cores overlap
in at least `K` coordinates lie on one common source pencil: their canonical
secant parameters are equal.  Clustering the matched pairs of an over-budget
family therefore reduces to the `K`-overlap relation on their cores. -/
theorem secantParameter_eq_of_core_overlap
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {gamma beta gamma' beta' : F}
    (hgamma : gamma ∈ family.G) (hbeta : beta ∈ family.G)
    (hne : gamma ≠ beta)
    (hgamma' : gamma' ∈ family.G) (hbeta' : beta' ∈ family.G)
    (hne' : gamma' ≠ beta')
    (hoverlap : K ≤
      (secantCore family gamma beta ∩ secantCore family gamma' beta').card) :
    secantParameter family gamma beta = secantParameter family gamma' beta' := by
  by_contra hlines
  have hmem := secantParameter_mem_lineParameters family hgamma hbeta hne
  have hmem' := secantParameter_mem_lineParameters family hgamma' hbeta' hne'
  have hdeg := lineParameter_degree_lt family hmem
  have hdeg' := lineParameter_degree_lt family hmem'
  have hcomp : (secantParameter family gamma beta).1 ≠
        (secantParameter family gamma' beta').1 ∨
      (secantParameter family gamma beta).2 ≠
        (secantParameter family gamma' beta').2 := by
    by_contra hboth
    push Not at hboth
    exact hlines (Prod.ext hboth.1 hboth.2)
  have hcap := jointCore_inter_card_le_of_ne dom (u 0) (u 1)
    (k := K) (by norm_num [K]) hdeg.1 hdeg.2 hdeg'.1 hdeg'.2 hcomp
  have hcap' : (secantCore family gamma beta ∩
      secantCore family gamma' beta').card ≤ K - 1 := by
    simpa only [secantCore] using hcap
  exact absurd (le_trans hoverlap hcap')
    (Nat.not_le.mpr (Nat.sub_lt (by norm_num [K]) one_pos))

/-! ## The Plotkin saturation ceiling (honest barrier) -/

/-- The least overlap threshold at which the constant-weight Plotkin
denominator `T^2 - N*lambda` becomes nonpositive. -/
abbrev saturationOverlapCeiling : Nat := 327272222

/-- Below the ceiling the Plotkin denominator is positive: pairwise counting
still forces overlaps there. -/
theorem plotkin_denominator_pos_below_ceiling :
    N * (saturationOverlapCeiling - 1) < T ^ 2 := by
  norm_num [N, T, saturationOverlapCeiling]

/-- At the ceiling the Plotkin denominator is nonpositive: the constant-weight
Plotkin bound is vacuous for every overlap threshold at or above
`327272222`, regardless of how many agreement sets are counted. -/
theorem plotkin_denominator_vacuous_at_ceiling :
    T ^ 2 ≤ N * saturationOverlapCeiling := by
  norm_num [N, T, saturationOverlapCeiling]

/-- The saturated two-fresh core size lies strictly above the Plotkin ceiling.
Consequently no pairwise agreement count can directly force two explanations
onto a saturated pencil; consolidating the forced `K`-core matching into at
most four saturated pencils requires geometric input beyond the
constant-weight Plotkin bound. -/
theorem saturation_core_above_ceiling :
    saturationOverlapCeiling < T - 2 := by
  norm_num [T, saturationOverlapCeiling]

end ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.jointCore_inter_card_le_of_ne
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.exists_pair_inter_card_ge_K_of_six
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.exists_pair_large_secant_core_of_subset
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.exists_forced_secant_matching_on
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.exists_forced_secant_matching_of_over_budget
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.secantParameter_eq_of_core_overlap
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.plotkin_denominator_vacuous_at_ceiling
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterForcedSecantMatching.saturation_core_above_ceiling
