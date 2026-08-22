/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines
import ArkLib.Data.CodingTheory.Connections.GCXK25SecondMoment
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
# P1 rate-quarter predecessor: the agreement-overlap graph has independence at most five

At the immediate predecessor of the saturated rate-quarter construction, every explanation
agrees on at least

```text
t = 592794966
```

of the `N = 2^30` coordinates.  Put an edge between two explanations when their agreement sets
overlap on at least `k = 2^28` coordinates.  This file proves that every six vertices contain an
edge.  Equivalently, the large-overlap graph has independence number at most five.

The proof trims six agreement sets to constant weight `t` and applies the exact-diagonal Plotkin
bound with `lambda = k-1`.  Its divided bound is exactly five:

```text
N * (t - (k-1)) / (t^2 - N*(k-1)) = 5.
```

For Reed--Solomon explanations, an overlap of at least `k` coordinates uniquely determines the
polynomial source pencil through the two decoded points.  Thus this is a global forcing input for
the four-pencil extraction programme: a counterexample cannot have six mutually ordinary
explanations whose pairwise agreement overlaps all stay below interpolation dimension.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open Finset
open Polynomial
open _root_.ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph

open ConstantWeightPlotkinBound
open GCXK25SecondMoment
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines

attribute [local instance] Classical.propDecidable

/-- Prize length. -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter Reed--Solomon dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement threshold at the lattice predecessor of the saturated common-factor endpoint. -/
abbrev T : Nat := 592794966

/-- Exact integral onset at which five pairwise-distinct degree-`<K` line cores are impossible. -/
abbrev FourLineCoreFloor : Nat := 590558003

theorem fourLineCoreFloor_le_nearSaturated : FourLineCoreFloor ≤ T - 2 := by
  norm_num [FourLineCoreFloor, T]

/-- The exact Plotkin quotient controlling an independent family of predecessor agreement sets. -/
theorem plotkin_quotient_eq_five :
    (N * (T - (K - 1))) / (T ^ 2 - N * (K - 1)) = 5 := by
  norm_num [N, K, T]

/-- The Plotkin denominator is positive at the P1 rate-quarter predecessor. -/
theorem plotkin_gap_pos : N * (K - 1) < T ^ 2 := by
  norm_num [N, K, T]

/-! ## Integral five-set strengthening -/

/-- The integer improvement over Cauchy--Schwarz for multiplicities bounded by five. -/
theorem five_mul_le_sq_add_six {s : Nat} (hs : s ≤ 5) :
    5 * s ≤ s ^ 2 + 6 := by
  interval_cases s <;> norm_num

/-- Five sets of size at least `z`, with pair intersections at most `lambda`, satisfy the sharp
integral Johnson inequality `20z ≤ 6|U| + 20lambda`. -/
theorem fiveSet_integral_johnson
    {U : Type} [Fintype U] [DecidableEq U]
    (S : Fin 5 → Finset U) {z lambda : Nat}
    (hsize : ∀ i, z ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ lambda) :
    20 * z ≤ 6 * Fintype.card U + 20 * lambda := by
  classical
  let I : Finset (Fin 5) := Finset.univ
  let mass : Nat := ∑ i : Fin 5, (S i).card
  let second : Nat := ∑ i : Fin 5, ∑ j : Fin 5, (S i ∩ S j).card
  have hmassLower : 5 * z ≤ mass := by
    change 5 * z ≤ ∑ i : Fin 5, (S i).card
    rw [show 5 * z = ∑ _i : Fin 5, z by simp]
    exact Finset.sum_le_sum (fun i _ => hsize i)
  have hmultBound : ∀ x : U, mult I S x ≤ 5 := by
    intro x
    calc
      mult I S x = (I.filter fun i => x ∈ S i).card := rfl
      _ ≤ I.card := Finset.card_filter_le _ _
      _ = 5 := by simp [I]
  have hfirstMoment : mass = ∑ x : U, mult I S x := by
    simpa [mass, I] using (sum_card_eq_sum_mult I S)
  have hsecondMoment : second = ∑ x : U, (mult I S x) ^ 2 := by
    simpa [second, I] using (sum_sum_card_inter_eq_sum_mult_sq I S)
  have hintegral : 5 * mass ≤ second + 6 * Fintype.card U := by
    rw [hfirstMoment, Finset.mul_sum]
    calc
      ∑ x : U, 5 * mult I S x
          ≤ ∑ x : U, ((mult I S x) ^ 2 + 6) :=
            Finset.sum_le_sum (fun x _ => five_mul_le_sq_add_six (hmultBound x))
      _ = (∑ x : U, (mult I S x) ^ 2) + 6 * Fintype.card U := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
      _ = second + 6 * Fintype.card U := by rw [hsecondMoment]
  have hoffdiag :
      ∑ i ∈ I, ∑ j ∈ I.erase i, (S i ∩ S j).card ≤ 20 * lambda := by
    have h := offdiag_le I S (B := lambda) (by
      intro i _hi j _hj hij
      exact hpair i j hij)
    simpa [I] using h
  have hsplit := sum_sum_card_inter_eq_diag_add_offdiag I S
  have hsecondUpper : second ≤ mass + 20 * lambda := by
    have hdiag : ∑ i ∈ I, (S i).card = mass := by simp [I, mass]
    have hsecond :
        ∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card = second := by
      simp [I, second]
    rw [hsecond, hdiag] at hsplit
    rw [hsplit]
    exact Nat.add_le_add_left hoffdiag mass
  have hfourMass : 4 * mass ≤ 6 * Fintype.card U + 20 * lambda := by
    have hcombined : 5 * mass ≤ mass + 20 * lambda + 6 * Fintype.card U :=
      hintegral.trans (Nat.add_le_add_right hsecondUpper (6 * Fintype.card U))
    omega
  have htwenty : 20 * z ≤ 4 * mass := by nlinarith
  exact htwenty.trans hfourMass

/-- **Five-set overlap forcing.**  The integral multiplicity correction improves the six-set
Plotkin statement: already among any five predecessor agreement sets, two overlap on at least
`K` coordinates. -/
theorem exists_pair_inter_card_ge_K_of_five
    (S : Fin 5 → Finset (Fin N))
    (hsize : ∀ i, T ≤ (S i).card) :
    ∃ i j : Fin 5, i ≠ j ∧ K ≤ (S i ∩ S j).card := by
  by_contra hnot
  push Not at hnot
  have hpair : ∀ i j : Fin 5, i ≠ j → (S i ∩ S j).card ≤ K - 1 := by
    intro i j hij
    have := hnot i j hij
    omega
  have hJ := fiveSet_integral_johnson S hsize hpair
  simp only [Fintype.card_fin] at hJ
  norm_num [N, K, T] at hJ

/-! ## Global four-line cap at the near-saturated core scale -/

/-- Distinct degree-`<k` polynomial lines have joint cores meeting in at most `k-1`
coordinates. -/
theorem jointCore_inter_card_le_of_line_ne
    {I E : Type} [Fintype I] [DecidableEq I]
    [Field E] [Fintype E] [DecidableEq E]
    (dom : I ↪ E) (u₀ u₁ : I → E) {k : Nat} (hk : 1 ≤ k)
    {a r a' r' : E[X]}
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

/-- Five pairwise-distinct degree-`<K` polynomial lines cannot all have cores of size at least
`FourLineCoreFloor = 590558003`, which is `2236961` coordinates below `T-2`.  The proof is
global: it uses only distinct-line root rigidity and the integral five-set Johnson inequality,
with no primitive-factor or collapsed-cluster hypothesis. -/
theorem no_five_nearSaturated_lines
    {E : Type} [Field E] [Fintype E] [DecidableEq E]
    (dom : Fin N ↪ E) (u₀ u₁ : Fin N → E)
    (line : Fin 5 → E[X] × E[X])
    (hinjective : Function.Injective line)
    (hdeg : ∀ i, (line i).1.natDegree < K ∧ (line i).2.natDegree < K)
    (hcore : ∀ i, FourLineCoreFloor ≤
      (jointCore dom u₀ u₁ (line i).1 (line i).2).card) : False := by
  let D : Fin 5 → Finset (Fin N) := fun i =>
    jointCore dom u₀ u₁ (line i).1 (line i).2
  have hpair : ∀ i j : Fin 5, i ≠ j → (D i ∩ D j).card ≤ K - 1 := by
    intro i j hij
    have hline : line i ≠ line j := hinjective.ne hij
    have hcomp : (line i).1 ≠ (line j).1 ∨ (line i).2 ≠ (line j).2 := by
      by_contra hnot
      push Not at hnot
      exact hline (Prod.ext hnot.1 hnot.2)
    exact jointCore_inter_card_le_of_line_ne dom u₀ u₁
      (k := K) (by norm_num [K])
      (hdeg i).1 (hdeg i).2 (hdeg j).1 (hdeg j).2 hcomp
  have hJ := fiveSet_integral_johnson D hcore hpair
  simp only [Fintype.card_fin] at hJ
  norm_num [N, K, FourLineCoreFloor] at hJ

/-- **Unconditional global four-line floor.**  Any finite collection of pairwise-distinct
degree-`<K` polynomial lines whose joint cores have size at least `590558003` contains at most
four lines. -/
theorem coreFloor_lines_card_le_four
    {E : Type} [Field E] [Fintype E] [DecidableEq E]
    (dom : Fin N ↪ E) (u₀ u₁ : Fin N → E)
    (lines : Finset (E[X] × E[X]))
    (hdeg : ∀ l ∈ lines, l.1.natDegree < K ∧ l.2.natDegree < K)
    (hcore : ∀ l ∈ lines, FourLineCoreFloor ≤
      (jointCore dom u₀ u₁ l.1 l.2).card) :
    lines.card ≤ 4 := by
  by_contra hnot
  have hfive : 5 ≤ lines.card := by omega
  obtain ⟨L5, hL5sub, hL5card⟩ := Finset.exists_subset_card_eq hfive
  have he : L5 ≃ Fin 5 := by
    rw [← hL5card]
    exact L5.equivFin
  let line : Fin 5 → E[X] × E[X] := fun i => (he.symm i : E[X] × E[X])
  have hinjective : Function.Injective line := by
    intro i j hij
    apply he.symm.injective
    exact Subtype.ext hij
  have hmem : ∀ i, line i ∈ lines := fun i => hL5sub (he.symm i).2
  exact no_five_nearSaturated_lines dom u₀ u₁ line hinjective
    (fun i => hdeg _ (hmem i)) (fun i => hcore _ (hmem i))

/-- Near-saturated (`T-2`)-core lines are a fortiori capped by four. -/
theorem nearSaturated_lines_card_le_four
    {E : Type} [Field E] [Fintype E] [DecidableEq E]
    (dom : Fin N ↪ E) (u₀ u₁ : Fin N → E)
    (lines : Finset (E[X] × E[X]))
    (hdeg : ∀ l ∈ lines, l.1.natDegree < K ∧ l.2.natDegree < K)
    (hcore : ∀ l ∈ lines, T - 2 ≤
      (jointCore dom u₀ u₁ l.1 l.2).card) :
    lines.card ≤ 4 :=
  coreFloor_lines_card_le_four dom u₀ u₁ lines hdeg
    (fun l hl => fourLineCoreFloor_le_nearSaturated.trans (hcore l hl))

/-- A line carrying at least `216` selected points at threshold `T` has core at least the exact
four-line floor `590558003`.  The value is sharp for this packing calculation: at core
`590558002`, `215` points still fit, while `216` exceed the universe by `402`. -/
theorem core_ge_fourLineFloor_of_216_points {L z : Nat}
    (hL : 216 ≤ L) (hpack : L * max 1 (T - z) + z ≤ N) :
    FourLineCoreFloor ≤ z := by
  by_cases hz : T ≤ z
  · exact fourLineCoreFloor_le_nearSaturated.trans (by omega)
  · push Not at hz
    have hdiff : 1 ≤ T - z := by omega
    rw [max_eq_right hdiff] at hpack
    have hmul : 216 * (T - z) ≤ L * (T - z) :=
      Nat.mul_le_mul_right _ hL
    have hpack' : 216 * (T - z) + z ≤ N :=
      (Nat.add_le_add_right hmul z).trans hpack
    norm_num [N, T, FourLineCoreFloor] at hpack' ⊢
    omega

/-- **Four big-line cap.**  In a P1 predecessor rich-point family, at most four relevant
secant lines carry `216` or more selected explanations.  This improves the previous unconditional
`95`-point/five-line cap to the endpoint-matching count four. -/
theorem lines_with_216_points_card_le_four
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊) :
    ((lineParameters family).filter
      (fun line => 216 ≤ (pointsOn family line).card)).card ≤ 4 := by
  let bigLines := (lineParameters family).filter
    (fun line => 216 ≤ (pointsOn family line).card)
  apply coreFloor_lines_card_le_four dom (u 0) (u 1) bigLines
  · intro line hline
    exact lineParameter_degree_lt family (Finset.mem_filter.mp hline).1
  · intro line hline
    have hm := Finset.mem_filter.mp hline
    have hpacking := pointsOn_card_mul_max_add_core_le family hm.1
    set z := (jointCore dom (u 0) (u 1) line.1 line.2).card
    set L := (pointsOn family line).card
    have hmono : max 1 (T - z) ≤
        max 1 (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - z) :=
      max_le_max le_rfl (Nat.sub_le_sub_right hthreshold z)
    have hpack : L * max 1 (T - z) + z ≤ N := by
      have hmul : L * max 1 (T - z) ≤
          L * max 1 (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - z) :=
        Nat.mul_le_mul_left L hmono
      have := (Nat.add_le_add_right hmul z).trans hpacking
      simpa only [Fintype.card_fin] using this
    exact core_ge_fourLineFloor_of_216_points hm.2 hpack

/-- **Six-set overlap forcing.**  Among any six subsets of the P1 coordinate set, each of
cardinality at least the predecessor agreement threshold, two distinct sets overlap in at least
the Reed--Solomon dimension `K`.

In the decoded-point geometry this says that every six explanations contain a pair determining a
source pencil on at least `K` common coordinates. -/
theorem exists_pair_inter_card_ge_K_of_six
    (S : Fin 6 → Finset (Fin N))
    (hsize : ∀ i, T ≤ (S i).card) :
    ∃ i j : Fin 6, i ≠ j ∧ K ≤ (S i ∩ S j).card := by
  classical
  by_contra hnot
  push Not at hnot
  let S' : Fin 6 → Finset (Fin N) := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hS'sub : ∀ i, S' i ⊆ S i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hS'card : ∀ i, (S' i).card = T := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hpair : ∀ i j, i ≠ j → (S' i ∩ S' j).card ≤ K - 1 := by
    intro i j hij
    have hsmall : (S i ∩ S j).card < K := hnot i j hij
    have hsub : S' i ∩ S' j ⊆ S i ∩ S j :=
      Finset.inter_subset_inter (hS'sub i) (hS'sub j)
    have hle := Finset.card_le_card hsub
    omega
  have hplot := constantWeight_plotkin S' T (K - 1) hS'card hpair
  simp only [Fintype.card_fin] at hplot
  norm_num [N, K, T] at hplot

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Geometric connector.**  Six distinct selected explanations at the P1 predecessor contain
two whose canonical secant pencil has a joint core of size at least `K`.

This turns the constant-weight overlap statement into the polynomial-line language used by the
four-pencil extraction theorem.  The exact line-core identity identifies the overlap of the two
full agreement sets with the joint core of their unique secant. -/
theorem exists_pair_large_secant_core_of_six
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (label : Fin 6 → F) (hinjective : Function.Injective label)
    (hlabel : ∀ i, label i ∈ family.G)
    (hsize : ∀ i, T ≤
      (fullAgreement dom (u 0) (u 1) (label i)
        (family.q (label i))).card) :
    ∃ i j : Fin 6, i ≠ j ∧
      K ≤ (jointCore dom (u 0) (u 1)
        (secantParameter family (label i) (label j)).1
        (secantParameter family (label i) (label j)).2).card := by
  let S : Fin 6 → Finset (Fin N) := fun i =>
    fullAgreement dom (u 0) (u 1) (label i) (family.q (label i))
  obtain ⟨i, j, hij, hoverlap⟩ :=
    exists_pair_inter_card_ge_K_of_six S hsize
  have hscalar : label i ≠ label j := hinjective.ne hij
  let line := secantParameter family (label i) (label j)
  have hiOn : label i ∈ pointsOn family line :=
    first_point_mem_pointsOn_secant family (beta := label j) (hlabel i)
  have hjOn : label j ∈ pointsOn family line :=
    second_point_mem_pointsOn_secant family (gamma := label i) (hlabel j) hscalar
  have hiLine := (mem_pointsOn_iff family line (label i)).mp hiOn |>.2
  have hjLine := (mem_pointsOn_iff family line (label j)).mp hjOn |>.2
  refine ⟨i, j, hij, ?_⟩
  rw [← fullAgreement_inter_eq_jointCore
    dom (u 0) (u 1) line.1 line.2 hscalar]
  simpa only [S, line, hiLine, hjLine] using hoverlap

/-- **Finite-family form.**  Every selected predecessor family with at least six explanations
contains two distinct scalars whose canonical secant has a `K`-coordinate joint core.

This is the direct interface needed by greedy source-pencil extraction: no six-element indexing
is exposed to downstream consumers. -/
theorem exists_large_secant_core_of_six_le_card
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hcard : 6 ≤ family.G.card)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    ∃ gamma ∈ family.G, ∃ beta ∈ family.G, gamma ≠ beta ∧
      K ≤ (jointCore dom (u 0) (u 1)
        (secantParameter family gamma beta).1
        (secantParameter family gamma beta).2).card := by
  classical
  obtain ⟨G6, hG6sub, hG6card⟩ := Finset.exists_subset_card_eq hcard
  have he : G6 ≃ Fin 6 := by
    rw [← hG6card]
    exact G6.equivFin
  let label : Fin 6 → F := fun i => (he.symm i : F)
  have hinjective : Function.Injective label := by
    intro i j hij
    apply he.symm.injective
    exact Subtype.ext hij
  have hlabel : ∀ i, label i ∈ family.G := by
    intro i
    exact hG6sub (he.symm i).2
  have hsix := exists_pair_large_secant_core_of_six family label hinjective hlabel
    (fun i => hsize (label i) (hlabel i))
  obtain ⟨i, j, hij, hcore⟩ := hsix
  exact ⟨label i, hlabel i, label j, hlabel j, hinjective.ne hij, hcore⟩

/-- The graph on the selected rich points in which two distinct explanations are adjacent when
their full agreement sets overlap on at least the interpolation dimension `K`.

The graph is deliberately defined by agreement overlap, rather than by a chosen secant
parameter.  This makes symmetry tautological; `fullAgreement_inter_eq_jointCore` then transports
every edge to the unique polynomial source pencil through its endpoints. -/
noncomputable def largeOverlapGraph
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u) : SimpleGraph family.G where
  Adj x y := x ≠ y ∧ K ≤
    (fullAgreement dom (u 0) (u 1) x.1 (family.q x.1) ∩
      fullAgreement dom (u 0) (u 1) y.1 (family.q y.1)).card
  symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- **Global graph form of six-point forcing.**  At the P1 predecessor, the complement of the
large-overlap graph contains no six-clique.  Equivalently, the large-overlap graph has
independence number at most five.

This is stronger operationally than merely producing one secant from one chosen six-tuple: it
allows extremal graph and matching arguments to be applied to the entire bad-scalar family. -/
theorem largeOverlapGraph_compl_cliqueFree_six
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    (largeOverlapGraph family)ᶜ.CliqueFree 6 := by
  classical
  intro G6 hG6
  have he : G6 ≃ Fin 6 := by
    rw [← hG6.card_eq]
    exact G6.equivFin
  let vertex : Fin 6 → family.G := fun i => (he.symm i).1
  let S : Fin 6 → Finset (Fin N) := fun i =>
    fullAgreement dom (u 0) (u 1) (vertex i).1 (family.q (vertex i).1)
  have hSsize : ∀ i, T ≤ (S i).card := by
    intro i
    exact hsize (vertex i).1 (vertex i).2
  obtain ⟨i, j, hij, hoverlap⟩ := exists_pair_inter_card_ge_K_of_six S hSsize
  have hvertex_ne : vertex i ≠ vertex j := by
    intro h
    apply hij
    apply he.symm.injective
    exact Subtype.ext h
  have hadj : (largeOverlapGraph family).Adj (vertex i) (vertex j) := by
    exact ⟨hvertex_ne, by simpa only [S] using hoverlap⟩
  have hi : vertex i ∈ G6 := (he.symm i).2
  have hj : vertex j ∈ G6 := (he.symm j).2
  have hcompl := hG6.isClique hi hj hvertex_ne
  exact ((SimpleGraph.compl_adj _ _ _).mp hcompl).2 hadj

/-- **Sharp global graph form.**  The complement of the predecessor large-overlap graph is
already `K₅`-free.  Equivalently, the large-overlap graph has independence number at most four.

This is the exact combinatorial count suggested by the four-pencil endpoint.  The improvement
from six to five vertices is the integer multiplicity correction in
`fiveSet_integral_johnson`; ordinary real-valued Plotkin division misses it. -/
theorem largeOverlapGraph_compl_cliqueFree_five
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    (largeOverlapGraph family)ᶜ.CliqueFree 5 := by
  classical
  intro G5 hG5
  have he : G5 ≃ Fin 5 := by
    rw [← hG5.card_eq]
    exact G5.equivFin
  let vertex : Fin 5 → family.G := fun i => (he.symm i).1
  let S : Fin 5 → Finset (Fin N) := fun i =>
    fullAgreement dom (u 0) (u 1) (vertex i).1 (family.q (vertex i).1)
  have hSsize : ∀ i, T ≤ (S i).card := by
    intro i
    exact hsize (vertex i).1 (vertex i).2
  obtain ⟨i, j, hij, hoverlap⟩ := exists_pair_inter_card_ge_K_of_five S hSsize
  have hvertex_ne : vertex i ≠ vertex j := by
    intro h
    apply hij
    apply he.symm.injective
    exact Subtype.ext h
  have hadj : (largeOverlapGraph family).Adj (vertex i) (vertex j) := by
    exact ⟨hvertex_ne, by simpa only [S] using hoverlap⟩
  have hi : vertex i ∈ G5 := (he.symm i).2
  have hj : vertex j ∈ G5 := (he.symm j).2
  have hcompl := hG5.isClique hi hj hvertex_ne
  exact ((SimpleGraph.compl_adj _ _ _).mp hcompl).2 hadj

/-- Every graph edge is exactly a large-core polynomial secant.  This is the edgewise geometric
interface: extremal information about `largeOverlapGraph` can be counted in the source-pencil
geometry without losing the sharp threshold `K`. -/
theorem jointCore_card_ge_K_of_largeOverlapGraph_adj
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {gamma beta : family.G}
    (hadj : (largeOverlapGraph family).Adj gamma beta) :
    K ≤ (jointCore dom (u 0) (u 1)
      (secantParameter family gamma.1 beta.1).1
      (secantParameter family gamma.1 beta.1).2).card := by
  have hscalar : gamma.1 ≠ beta.1 := by
    intro h
    exact hadj.1 (Subtype.ext h)
  let line := secantParameter family gamma.1 beta.1
  have hgammaOn : gamma.1 ∈ pointsOn family line :=
    first_point_mem_pointsOn_secant family gamma.2
  have hbetaOn : beta.1 ∈ pointsOn family line :=
    second_point_mem_pointsOn_secant family beta.2 hscalar
  have hgammaLine := (mem_pointsOn_iff family line gamma.1).mp hgammaOn |>.2
  have hbetaLine := (mem_pointsOn_iff family line beta.1).mp hbetaOn |>.2
  rw [← fullAgreement_inter_eq_jointCore
    dom (u 0) (u 1) line.1 line.2 hscalar]
  simpa only [line, hgammaLine, hbetaLine] using hadj.2

/-- **Quantitative overlap abundance.**  Write `m` for the number of selected explanations.
At the P1 predecessor, the number of large-core secant pairs is at least the complement of the
exact five-part Turán bound:

```text
choose(m,2) - [((m²-(m mod 5)²)·4)/10 + choose(m mod 5,2)].
```

The bracket is the maximum possible number of *small*-overlap pairs.  Thus the local Plotkin
forcing statement yields a global quadratic supply of large-core secants. -/
theorem turan_lower_bound_largeOverlap_edges
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    let m := Fintype.card family.G
    m.choose 2 -
        ((m ^ 2 - (m % 5) ^ 2) * 4 / 10 + (m % 5).choose 2) ≤
      #(largeOverlapGraph family).edgeFinset := by
  classical
  let G := largeOverlapGraph family
  let m := Fintype.card family.G
  have hfree : Gᶜ.CliqueFree (5 + 1) := by
    simpa only [G, Nat.reduceAdd] using
      largeOverlapGraph_compl_cliqueFree_six family hsize
  have hsmall :
      #Gᶜ.edgeFinset ≤
        (m ^ 2 - (m % 5) ^ 2) * 4 / 10 + (m % 5).choose 2 := by
    simpa only [m, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] using
      (SimpleGraph.CliqueFree.card_edgeFinset_le (G := Gᶜ) (r := 5) hfree)
  have hpartition :
      #G.edgeFinset + #Gᶜ.edgeFinset = m.choose 2 := by
    calc
      #G.edgeFinset + #Gᶜ.edgeFinset = #(G.edgeFinset ∪ Gᶜ.edgeFinset) := by
        rw [Finset.card_union_of_disjoint]
        simp only [SimpleGraph.disjoint_edgeFinset, disjoint_compl_right]
      _ = #((⊤ : SimpleGraph family.G).edgeFinset) := by
        congr 1
        have hset : G.edgeSet ∪ Gᶜ.edgeSet =
            (⊤ : SimpleGraph family.G).edgeSet := by
          rw [← SimpleGraph.edgeSet_sup, sup_compl_eq_top]
        ext e
        simpa only [Finset.mem_union, SimpleGraph.mem_edgeFinset, Set.mem_union] using
          (Set.ext_iff.mp hset e)
      _ = m.choose 2 := by
        simpa only [m] using
          (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := family.G))
  dsimp only
  change m.choose 2 -
      ((m ^ 2 - (m % 5) ^ 2) * 4 / 10 + (m % 5).choose 2) ≤ #G.edgeFinset
  omega

/-- The sharp four-part Turán consequence of `CliqueFree 5`.  This improves the guaranteed
large-core secant density from asymptotic `1/5` to `1/4` of all unordered pairs. -/
theorem turan_fourPart_lower_bound_largeOverlap_edges
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    let m := Fintype.card family.G
    m.choose 2 -
        ((m ^ 2 - (m % 4) ^ 2) * 3 / 8 + (m % 4).choose 2) ≤
      #(largeOverlapGraph family).edgeFinset := by
  classical
  let G := largeOverlapGraph family
  let m := Fintype.card family.G
  have hfree : Gᶜ.CliqueFree (4 + 1) := by
    simpa only [G, Nat.reduceAdd] using
      largeOverlapGraph_compl_cliqueFree_five family hsize
  have hsmall :
      #Gᶜ.edgeFinset ≤
        (m ^ 2 - (m % 4) ^ 2) * 3 / 8 + (m % 4).choose 2 := by
    simpa only [m, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] using
      (SimpleGraph.CliqueFree.card_edgeFinset_le (G := Gᶜ) (r := 4) hfree)
  have hpartition :
      #G.edgeFinset + #Gᶜ.edgeFinset = m.choose 2 := by
    calc
      #G.edgeFinset + #Gᶜ.edgeFinset = #(G.edgeFinset ∪ Gᶜ.edgeFinset) := by
        rw [Finset.card_union_of_disjoint]
        simp only [SimpleGraph.disjoint_edgeFinset, disjoint_compl_right]
      _ = #((⊤ : SimpleGraph family.G).edgeFinset) := by
        congr 1
        have hset : G.edgeSet ∪ Gᶜ.edgeSet =
            (⊤ : SimpleGraph family.G).edgeSet := by
          rw [← SimpleGraph.edgeSet_sup, sup_compl_eq_top]
        ext e
        simpa only [Finset.mem_union, SimpleGraph.mem_edgeFinset, Set.mem_union] using
          (Set.ext_iff.mp hset e)
      _ = m.choose 2 := by
        simpa only [m] using
          (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := family.G))
  dsimp only
  change m.choose 2 -
      ((m ^ 2 - (m % 4) ^ 2) * 3 / 8 + (m % 4).choose 2) ≤ #G.edgeFinset
  omega

end ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.plotkin_quotient_eq_five
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.exists_pair_inter_card_ge_K_of_six
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.exists_pair_large_secant_core_of_six
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.exists_large_secant_core_of_six_le_card
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.largeOverlapGraph_compl_cliqueFree_six
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.exists_pair_inter_card_ge_K_of_five
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.no_five_nearSaturated_lines
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.coreFloor_lines_card_le_four
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.nearSaturated_lines_card_le_four
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.lines_with_216_points_card_le_four
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.largeOverlapGraph_compl_cliqueFree_five
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.jointCore_card_ge_K_of_largeOverlapGraph_adj
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.turan_lower_bound_largeOverlap_edges
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.turan_fourPart_lower_bound_largeOverlap_edges
