/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorThirdMomentUpper

/-!
# Weighted third-moment upper bound with an arbitrary line cap

This parameterizes the four-point-line theorem used at the half predecessor.
If every determined line has at most `B` selected points, each selected pair
has at most `B-2` collinear extensions.  The resulting correction to six
times the third moment is exactly

`(B-2) * c * N * (N-1)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper

namespace ArkLib.ProximityGap.Frontier.ThirdMomentUpperLineCap

attribute [local instance] Classical.propDecidable

variable {Point Line U : Type*}
variable [DecidableEq Point] [DecidableEq Line] [DecidableEq U]

/-- Under a `B`-point line cap, a fixed pair has at most `B-2`
collinear triple extensions. -/
theorem collinearExtensions_card_le_lineCap_sub_two
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line) (B : ℕ)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineCap : ∀ ell, (linePoints G onLine ell).card ≤ B)
    (P : Finset Point) (hP : P ∈ G.powersetCard 2) :
    (collinearExtensions G onLine P).card ≤ B - 2 := by
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
  have hdiffCard : (Lpts \ ({x, y} : Finset Point)).card ≤ B - 2 := by
    rw [Finset.card_sdiff_of_subset hpairSub]
    have hline := hlineCap ell
    change Lpts.card ≤ B at hline
    rw [hPcard]
    omega
  let f : Finset Point → Finset Point := fun T =>
    T \ ({x, y} : Finset Point)
  have hmaps : Set.MapsTo f
      (↑(collinearExtensions G onLine {x, y}))
      (↑((Lpts \ ({x, y} : Finset Point)).powersetCard 1)) := by
    intro T hT
    have hText : T ∈ collinearExtensions G onLine {x, y} := hT
    have hTcol : T ∈ collinearTriples G onLine :=
      (Finset.mem_filter.mp hText).1
    have hpairT : ({x, y} : Finset Point) ⊆ T :=
      (Finset.mem_filter.mp hText).2
    obtain ⟨hTG, hTcard, ell', hTline⟩ :=
      (mem_collinearTriples_iff G onLine T).mp hTcol
    have hxT : x ∈ T := hpairT (by simp)
    have hyT : y ∈ T := hpairT (by simp)
    have hell : ell' = ell := by
      exact hpairUnique ell' x y hxy (hTline x hxT) (hTline y hyT)
    have hTsubL : T ⊆ Lpts := by
      intro z hz
      exact Finset.mem_filter.mpr
        ⟨hTG hz, by simpa only [hell] using hTline z hz⟩
    change f T ∈ (Lpts \ ({x, y} : Finset Point)).powersetCard 1
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff hTsubL (by rfl), ?_⟩
    rw [Finset.card_sdiff_of_subset hpairT, hTcard, hPcard]
  have hinj : Set.InjOn f
      (↑(collinearExtensions G onLine {x, y})) := by
    intro T hT S hS heq
    have hTpair : ({x, y} : Finset Point) ⊆ T :=
      (Finset.mem_filter.mp hT).2
    have hSpair : ({x, y} : Finset Point) ⊆ S :=
      (Finset.mem_filter.mp hS).2
    change T \ ({x, y} : Finset Point) = S \ {x, y} at heq
    calc
      T = {x, y} ∪ (T \ {x, y}) :=
        (Finset.union_sdiff_of_subset hTpair).symm
      _ = {x, y} ∪ (S \ {x, y}) := by rw [heq]
      _ = S := Finset.union_sdiff_of_subset hSpair
  calc
    (collinearExtensions G onLine {x, y}).card
        ≤ ((Lpts \ ({x, y} : Finset Point)).powersetCard 1).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = (Lpts \ ({x, y} : Finset Point)).card := by
      rw [Finset.card_powersetCard, Nat.choose_one_right]
    _ ≤ B - 2 := hdiffCard

/-- Double-counting triples against their three pairs with an arbitrary line
cap. -/
theorem three_mul_collinearTriples_card_le_lineCap
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line) (B : ℕ)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineCap : ∀ ell, (linePoints G onLine ell).card ≤ B) :
    3 * (collinearTriples G onLine).card ≤
      (B - 2) * G.card.choose 2 := by
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
        ∑ _P ∈ Pairs, (B - 2) := by
    exact Finset.sum_le_sum fun P hP =>
      collinearExtensions_card_le_lineCap_sub_two G onLine
        determinedLine B hpairOn hpairUnique hlineCap P hP
  have hpairs : Pairs.card = G.card.choose 2 := by
    exact Finset.card_powersetCard 2 G
  calc
    3 * C.card = ∑ T ∈ C, ((Pairs.filter fun P => P ⊆ T).card) :=
      hleft.symm
    _ = ∑ P ∈ Pairs, (collinearExtensions G onLine P).card := hswap
    _ ≤ ∑ _P ∈ Pairs, (B - 2) := hright
    _ = (B - 2) * G.card.choose 2 := by simp [hpairs, mul_comm]

/-- **Arbitrary-line-cap weighted third-moment upper bound.** -/
theorem weightedTripleSum_upper_lineCap
    (G : Finset Point) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line)
    (weight : Finset Point → ℕ) (d c B : ℕ)
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineCap : ∀ ell, (linePoints G onLine ell).card ≤ B)
    (hnoncol : ∀ T ∈ G.powersetCard 3,
      ¬ Collinear onLine T → weight T ≤ d)
    (hcol : ∀ T ∈ collinearTriples G onLine, weight T ≤ d + c) :
    6 * (∑ T ∈ G.powersetCard 3, weight T) ≤
      d * G.card * (G.card - 1) * (G.card - 2) +
        (B - 2) * c * G.card * (G.card - 1) := by
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
        (∑ T ∈ All, if Collinear onLine T then c else 0) =
          c * C.card := by
      simp only [← Finset.sum_filter]
      have hfilter : All.filter (Collinear onLine) = C := by rfl
      rw [hfilter]
      simp [mul_comm]
    calc
      (∑ T ∈ All, weight T)
          ≤ ∑ T ∈ All, (d + if Collinear onLine T then c else 0) :=
        Finset.sum_le_sum hpoint
      _ = d * All.card + c * C.card := by
        rw [Finset.sum_add_distrib, hconst, hcolsum]
  have hcolCount := three_mul_collinearTriples_card_le_lineCap
    G onLine determinedLine B hpairOn hpairUnique hlineCap
  have hAllCard : All.card = G.card.choose 3 :=
    Finset.card_powersetCard 3 G
  have hscaled :
      6 * (∑ T ∈ All, weight T) ≤ 6 * (d * All.card + c * C.card) :=
    Nat.mul_le_mul_left 6 hsum
  have hexcess :
      6 * c * C.card ≤ 2 * (B - 2) * c * G.card.choose 2 := by
    nlinarith
  have hchoose2 := Nat.choose_succ_right_eq G.card 1
  have hchoose3 := Nat.choose_succ_right_eq G.card 2
  norm_num [Nat.choose_one_right] at hchoose2 hchoose3
  have hfallTwo : 2 * G.card.choose 2 = G.card * (G.card - 1) := by
    nlinarith
  have hfallThree :
      6 * G.card.choose 3 =
        G.card * (G.card - 1) * (G.card - 2) := by
    calc
      6 * G.card.choose 3 = 2 * (G.card.choose 3 * 3) := by ring
      _ = 2 * (G.card.choose 2 * (G.card - 2)) := by rw [hchoose3]
      _ = (2 * G.card.choose 2) * (G.card - 2) := by ring
      _ = G.card * (G.card - 1) * (G.card - 2) := by rw [hfallTwo]
  rw [hAllCard] at hscaled
  calc
    6 * (∑ T ∈ G.powersetCard 3, weight T)
        ≤ 6 * (d * G.card.choose 3 + c * C.card) := hscaled
    _ = 6 * d * G.card.choose 3 + 6 * c * C.card := by ring
    _ ≤ 6 * d * G.card.choose 3 +
        2 * (B - 2) * c * G.card.choose 2 :=
      Nat.add_le_add_left hexcess _
    _ = d * G.card * (G.card - 1) * (G.card - 2) +
        (B - 2) * c * G.card * (G.card - 1) := by
      rw [show 6 * d * G.card.choose 3 =
          d * (6 * G.card.choose 3) by ring,
        hfallThree,
        show 2 * (B - 2) * c * G.card.choose 2 =
          (B - 2) * c * (2 * G.card.choose 2) by ring,
        hfallTwo]
      ring

end ArkLib.ProximityGap.Frontier.ThirdMomentUpperLineCap

#print axioms
  ArkLib.ProximityGap.Frontier.ThirdMomentUpperLineCap.weightedTripleSum_upper_lineCap
