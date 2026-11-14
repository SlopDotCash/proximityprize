/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorThirdMomentUpper

/-!
# Weighted third-moment upper bound with an arbitrary line cap

This parameterizes the four-point-line theorem used at the half predecessor.
If every determined line has at most `B` selected points, each selected pair
has at most `B-2` collinear extensions (the shared lemma
`HalfPredecessorThirdMomentUpper.collinearExtensions_card_le_lineCap_sub_two`,
of which the half-predecessor four-point lemma is the `B = 4` case).  The
resulting correction to six times the third moment is at most (an upper bound,
not an identity)

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
