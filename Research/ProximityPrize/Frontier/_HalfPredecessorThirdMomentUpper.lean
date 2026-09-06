/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The abstract third-moment upper bound

This module proves the combinatorial upper half of the rate-`1/16`
half-predecessor third-moment argument. Pair uniqueness and a four-point line
cap bound the number of collinear triples; splitting triple weights into a
noncollinear baseline and collinear excess gives the exact falling-factorial
estimate used by the numeric core. The final theorem is the incidence identity
that connects this triple sum to coordinate multiplicities.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper

attribute [local instance] Classical.propDecidable

variable {Point Line U : Type*}
variable [DecidableEq Point] [DecidableEq Line] [DecidableEq U]


/-- Points of `G` incident to a line. -/
noncomputable def linePoints (G : Finset Point) (onLine : Line → Point → Prop) (ell : Line) :
    Finset Point :=
  G.filter (onLine ell)

/-- A finite triple is collinear when one line contains all its points. -/
def Collinear (onLine : Line → Point → Prop) (T : Finset Point) : Prop :=
  ∃ ell : Line, ∀ x ∈ T, onLine ell x

/-- Collinear three-subsets of `G`. -/
noncomputable def collinearTriples (G : Finset Point) (onLine : Line → Point → Prop) :
    Finset (Finset Point) :=
  (G.powersetCard 3).filter (Collinear onLine)

@[simp]
theorem mem_collinearTriples_iff
    (G : Finset Point) (onLine : Line → Point → Prop) (T : Finset Point) :
    T ∈ collinearTriples G onLine ↔
      T ⊆ G ∧ T.card = 3 ∧ Collinear onLine T := by
  simp only [collinearTriples, Finset.mem_filter, Finset.mem_powersetCard]
  aesop

/-- Pair-to-triple fiber for the collinear-triple double count. -/
noncomputable def collinearExtensions (G : Finset Point) (onLine : Line → Point → Prop)
    (P : Finset Point) : Finset (Finset Point) :=
  (collinearTriples G onLine).filter fun T => P ⊆ T

/-- Pair uniqueness and a four-point line cap leave at most two ways to extend a
pair to a collinear triple. -/
theorem collinearExtensions_card_le_two
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineFour : ∀ ell, (linePoints G onLine ell).card ≤ 4)
    (P : Finset Point) (hP : P ∈ G.powersetCard 2) :
    (collinearExtensions G onLine P).card ≤ 2 := by
  have hPsub : P ⊆ G := (Finset.mem_powersetCard.mp hP).1
  have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hPcard
  have hxG : x ∈ G := hPsub (by simp)
  have hyG : y ∈ G := hPsub (by simp)
  let ell := determinedLine x y
  let Lpts := linePoints G onLine ell
  have hxyOn := hpairOn x hxG y hyG hxy
  have hpairSub : ({x, y} : Finset Point) ⊆ Lpts := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hxG, hxyOn.1⟩
    · exact Finset.mem_filter.mpr ⟨hyG, hxyOn.2⟩
  have hdiffCard : (Lpts \ ({x, y} : Finset Point)).card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset hpairSub]
    have hline := hlineFour ell
    change Lpts.card ≤ 4 at hline
    rw [hPcard]
    omega
  let f : Finset Point → Finset Point := fun T => T \ ({x, y} : Finset Point)
  have hmaps : Set.MapsTo f
      (↑(collinearExtensions G onLine {x, y}))
      (↑((Lpts \ ({x, y} : Finset Point)).powersetCard 1)) := by
    intro T hT
    have hText : T ∈ collinearExtensions G onLine {x, y} := hT
    have hTcol : T ∈ collinearTriples G onLine := (Finset.mem_filter.mp hText).1
    have hpairT : ({x, y} : Finset Point) ⊆ T := (Finset.mem_filter.mp hText).2
    obtain ⟨hTG, hTcard, ell', hTline⟩ :=
      (mem_collinearTriples_iff G onLine T).mp hTcol
    have hxT : x ∈ T := hpairT (by simp)
    have hyT : y ∈ T := hpairT (by simp)
    have hell : ell' = ell := by
      exact hpairUnique ell' x y hxy (hTline x hxT) (hTline y hyT)
    have hTsubL : T ⊆ Lpts := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨hTG hz, by simpa only [hell] using hTline z hz⟩
    change f T ∈ (Lpts \ ({x, y} : Finset Point)).powersetCard 1
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff hTsubL (by rfl), ?_⟩
    rw [Finset.card_sdiff_of_subset hpairT, hTcard]
    rw [hPcard]
  have hinj : Set.InjOn f (↑(collinearExtensions G onLine {x, y})) := by
    intro T hT S hS heq
    have hTpair : ({x, y} : Finset Point) ⊆ T :=
      (Finset.mem_filter.mp hT).2
    have hSpair : ({x, y} : Finset Point) ⊆ S :=
      (Finset.mem_filter.mp hS).2
    change T \ ({x, y} : Finset Point) = S \ {x, y} at heq
    calc
      T = {x, y} ∪ (T \ {x, y}) := (Finset.union_sdiff_of_subset hTpair).symm
      _ = {x, y} ∪ (S \ {x, y}) := by rw [heq]
      _ = S := Finset.union_sdiff_of_subset hSpair
  calc
    (collinearExtensions G onLine {x, y}).card
        ≤ ((Lpts \ ({x, y} : Finset Point)).powersetCard 1).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = (Lpts \ ({x, y} : Finset Point)).card := by
      rw [Finset.card_powersetCard, Nat.choose_one_right]
    _ ≤ 2 := hdiffCard

/-- A three-subset has exactly three two-subsets, even when the ambient set is
larger. -/
theorem pair_subsets_of_triple_card
    (G T : Finset Point) (hT : T ∈ G.powersetCard 3) :
    ((G.powersetCard 2).filter fun P => P ⊆ T).card = 3 := by
  have hTG : T ⊆ G := (Finset.mem_powersetCard.mp hT).1
  have hTcard : T.card = 3 := (Finset.mem_powersetCard.mp hT).2
  have heq : (G.powersetCard 2).filter (fun P => P ⊆ T) = T.powersetCard 2 := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hPG, hPcard⟩, hPT⟩
      exact ⟨hPT, hPcard⟩
    · rintro ⟨hPT, hPcard⟩
      exact ⟨⟨hPT.trans hTG, hPcard⟩, hPT⟩
  rw [heq, Finset.card_powersetCard, hTcard]
  norm_num

/-- The double count of collinear triples against their three constituent
pairs.  Four-point lines make each pair occur in at most two such triples. -/
theorem three_mul_collinearTriples_card_le_two_mul_choose_two
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineFour : ∀ ell, (linePoints G onLine ell).card ≤ 4) :
    3 * (collinearTriples G onLine).card ≤ 2 * G.card.choose 2 := by
  let C := collinearTriples G onLine
  let Pairs := G.powersetCard 2
  have hleft :
      ∑ T ∈ C, ((Pairs.filter fun P => P ⊆ T).card) = 3 * C.card := by
    rw [Finset.sum_const_nat (m := 3)]
    · omega
    · intro T hT
      exact pair_subsets_of_triple_card G T
        ((Finset.mem_filter.mp hT).1)
  have hswap :
      ∑ T ∈ C, ((Pairs.filter fun P => P ⊆ T).card) =
        ∑ P ∈ Pairs, (collinearExtensions G onLine P).card := by
    simp only [Finset.card_eq_sum_ones, collinearExtensions,
      Finset.sum_filter]
    rw [Finset.sum_comm]
  have hright :
      ∑ P ∈ Pairs, (collinearExtensions G onLine P).card ≤
        ∑ _P ∈ Pairs, 2 := by
    exact Finset.sum_le_sum fun P hP =>
      collinearExtensions_card_le_two G onLine determinedLine
        hpairOn hpairUnique hlineFour P hP
  have hpairs : Pairs.card = G.card.choose 2 := by
    exact Finset.card_powersetCard 2 G
  calc
    3 * C.card = ∑ T ∈ C, ((Pairs.filter fun P => P ⊆ T).card) := hleft.symm
    _ = ∑ P ∈ Pairs, (collinearExtensions G onLine P).card := hswap
    _ ≤ ∑ _P ∈ Pairs, 2 := hright
    _ = 2 * G.card.choose 2 := by simp [hpairs, mul_comm]

/-- Falling-factorial version of the collinear-triple count used by the final
third-moment estimate. -/
theorem six_mul_collinearTriples_card_le_two_mul_fallingPair
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineFour : ∀ ell, (linePoints G onLine ell).card ≤ 4) :
    6 * (collinearTriples G onLine).card ≤
      2 * G.card * (G.card - 1) := by
  have hcol := three_mul_collinearTriples_card_le_two_mul_choose_two
    G onLine determinedLine hpairOn hpairUnique hlineFour
  have hchoose := Nat.choose_succ_right_eq G.card 1
  simp only [Nat.choose_one_right] at hchoose
  nlinarith

/-- **Abstract third-moment upper bound, choose-number form.**  Every
noncollinear triple has weight at most `d`; a collinear triple has at most `c`
additional weight.  Pair uniqueness and the four-point line cap control the
number of triples receiving that excess. -/
theorem weightedTripleSum_upper_choose
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line)
    (weight : Finset Point → ℕ) (d c : ℕ)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineFour : ∀ ell, (linePoints G onLine ell).card ≤ 4)
    (hnoncol : ∀ T ∈ G.powersetCard 3, ¬ Collinear onLine T → weight T ≤ d)
    (hcol : ∀ T ∈ collinearTriples G onLine, weight T ≤ d + c) :
    6 * (∑ T ∈ G.powersetCard 3, weight T) ≤
      6 * d * G.card.choose 3 + 4 * c * G.card.choose 2 := by
  let All := G.powersetCard 3
  let C := collinearTriples G onLine
  have hpoint : ∀ T ∈ All,
      weight T ≤ d + if Collinear onLine T then c else 0 := by
    intro T hT
    by_cases hTc : Collinear onLine T
    · simp only [hTc, ↓reduceIte]
      apply hcol T
      exact Finset.mem_filter.mpr ⟨hT, hTc⟩
    · simp only [hTc, ↓reduceIte, add_zero]
      exact hnoncol T hT hTc
  have hsum :
      (∑ T ∈ All, weight T) ≤ d * All.card + c * C.card := by
    have hconst : (∑ _T ∈ All, d) = d * All.card := by
      simp [mul_comm]
    have hcolsum :
        (∑ T ∈ All, if Collinear onLine T then c else 0) = c * C.card := by
      simp only [← Finset.sum_filter]
      have hfilter : All.filter (Collinear onLine) = C := by
        rfl
      rw [hfilter]
      simp [mul_comm]
    calc
      (∑ T ∈ All, weight T)
          ≤ ∑ T ∈ All, (d + if Collinear onLine T then c else 0) :=
        Finset.sum_le_sum hpoint
      _ = d * All.card + c * C.card := by
        rw [Finset.sum_add_distrib, hconst, hcolsum]
  have hcolCount := three_mul_collinearTriples_card_le_two_mul_choose_two
    G onLine determinedLine hpairOn hpairUnique hlineFour
  have hAllCard : All.card = G.card.choose 3 := Finset.card_powersetCard 3 G
  have hscaled :
      6 * (∑ T ∈ All, weight T) ≤ 6 * (d * All.card + c * C.card) :=
    Nat.mul_le_mul_left 6 hsum
  have hexcess : 6 * c * C.card ≤ 4 * c * G.card.choose 2 := by
    nlinarith
  rw [hAllCard] at hscaled
  nlinarith

/-- **Abstract third-moment upper bound, exact falling-factorial form.** -/
theorem weightedTripleSum_upper
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line)
    (weight : Finset Point → ℕ) (d c : ℕ)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineFour : ∀ ell, (linePoints G onLine ell).card ≤ 4)
    (hnoncol : ∀ T ∈ G.powersetCard 3, ¬ Collinear onLine T → weight T ≤ d)
    (hcol : ∀ T ∈ collinearTriples G onLine, weight T ≤ d + c) :
    6 * (∑ T ∈ G.powersetCard 3, weight T) ≤
      d * G.card * (G.card - 1) * (G.card - 2) +
        2 * c * G.card * (G.card - 1) := by
  have hupper := weightedTripleSum_upper_choose G onLine determinedLine
    weight d c hpairOn hpairUnique hlineFour hnoncol hcol
  have hchoose2 := Nat.choose_succ_right_eq G.card 1
  have hchoose3 := Nat.choose_succ_right_eq G.card 2
  norm_num [Nat.choose_one_right] at hchoose2 hchoose3
  have hfallTwo : 2 * G.card.choose 2 = G.card * (G.card - 1) := by
    nlinarith
  have hfallThree :
      6 * G.card.choose 3 = G.card * (G.card - 1) * (G.card - 2) := by
    calc
      6 * G.card.choose 3 = 2 * (G.card.choose 3 * 3) := by ring
      _ = 2 * (G.card.choose 2 * (G.card - 2)) := by rw [hchoose3]
      _ = (2 * G.card.choose 2) * (G.card - 2) := by ring
      _ = G.card * (G.card - 1) * (G.card - 2) := by rw [hfallTwo]
  have hrhs :
      6 * d * G.card.choose 3 + 4 * c * G.card.choose 2 =
        d * G.card * (G.card - 1) * (G.card - 2) +
          2 * c * G.card * (G.card - 1) := by
    calc
      6 * d * G.card.choose 3 + 4 * c * G.card.choose 2 =
          d * (6 * G.card.choose 3) + 2 * c * (2 * G.card.choose 2) := by ring
      _ = d * G.card * (G.card - 1) * (G.card - 2) +
          2 * c * G.card * (G.card - 1) := by
        rw [hfallThree, hfallTwo]
        ring
  exact hupper.trans_eq hrhs

/-! ## Incidence moment identity -/

/-- Coordinates on which every point in a finite parameter set agrees. -/
noncomputable def commonCoordinates [Fintype U]
    (A : Point → Finset U) (T : Finset Point) : Finset U :=
  Finset.univ.filter fun i => ∀ gamma ∈ T, i ∈ A gamma

/-- The three-subsets of selected points incident to one coordinate can be
viewed either as a powerset of the coordinate fiber or as a filter of all
three-subsets. -/
theorem incidentTripleFiber_eq
    (G : Finset Point) (A : Point → Finset U) (i : U) :
    ((G.filter fun gamma => i ∈ A gamma).powersetCard 3) =
      (G.powersetCard 3).filter (fun T => ∀ gamma ∈ T, i ∈ A gamma) := by
  ext T
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hTfiber, hTcard⟩
    refine ⟨⟨fun gamma hgamma => (Finset.mem_filter.mp (hTfiber hgamma)).1,
      hTcard⟩, ?_⟩
    intro gamma hgamma
    exact (Finset.mem_filter.mp (hTfiber hgamma)).2
  · rintro ⟨⟨hTG, hTcard⟩, hTall⟩
    refine ⟨?_, hTcard⟩
    intro gamma hgamma
    exact Finset.mem_filter.mpr ⟨hTG hgamma, hTall gamma hgamma⟩

/-- **Exact third-incidence identity.**  The sum over coordinates of the number
of incident point triples equals the sum over point triples of their common
coordinate count. -/
theorem sum_choose_incidence_eq_sum_commonCoordinates_card
    [Fintype U] (G : Finset Point) (A : Point → Finset U) :
    (∑ i : U, ((G.filter fun gamma => i ∈ A gamma).card.choose 3)) =
      ∑ T ∈ G.powersetCard 3, (commonCoordinates A T).card := by
  let All := G.powersetCard 3
  calc
    (∑ i : U, ((G.filter fun gamma => i ∈ A gamma).card.choose 3)) =
        ∑ i : U, ((G.filter fun gamma => i ∈ A gamma).powersetCard 3).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_powersetCard]
    _ = ∑ i : U, ((All.filter fun T => ∀ gamma ∈ T, i ∈ A gamma).card) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [incidentTripleFiber_eq G A i]
    _ = ∑ i : U, ∑ T ∈ All,
          if (∀ gamma ∈ T, i ∈ A gamma) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ T ∈ All, ∑ i : U,
          if (∀ gamma ∈ T, i ∈ A gamma) then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ T ∈ All, (commonCoordinates A T).card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [commonCoordinates, Finset.card_eq_sum_ones, Finset.sum_filter]

end ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper

#print axioms ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper.collinearExtensions_card_le_two
#print axioms ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper.three_mul_collinearTriples_card_le_two_mul_choose_two
#print axioms ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper.weightedTripleSum_upper
#print axioms ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper.sum_choose_incidence_eq_sum_commonCoordinates_card

