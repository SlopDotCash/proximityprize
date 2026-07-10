/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAgreementOverlapGraph

/-!
# P1 divided-difference rank: only subsets of at most six can violate Hall

For a set `U` of decoded-polynomial labels, the divided-difference rows at coordinate `x`
have projected rank

```text
min (|support(x) intersect U|) (|support(x)| - 2).
```

Since `|support(x) intersect U| <= |support(x)|`, this truncation loses at most two from the
raw incidence count at each coordinate.  Thus labels of support size at least `T` have total
projected budget at least `|U|*T - 2*N`.  At the literal P1 constants,

```text
7*(T-K) > 2*N.
```

Consequently every subset of at least seven labels automatically has projected budget at least
`K*|U|`.  Any Hall obstruction to full block-Vandermonde rank is localized to at most six
labels.  This is an arithmetic/combinatorial localization, not yet the GM-MDS rank theorem that
turns the budget inequalities into injectivity.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization

open P1RateQuarterAgreementOverlapGraph

/-- Projected local divided-difference row budget for a label subset. -/
def projectedBudget {X J : Type} [Fintype X] [DecidableEq J]
    (support : X -> Finset J) (U : Finset J) : Nat :=
  ∑ x : X, min (support x ∩ U).card ((support x).card - 2)

/-- Truncating a local support to its codimension-two constraint space loses at most two. -/
theorem local_card_le_projected_add_two {J : Type} [DecidableEq J]
    (S U : Finset J) :
    (S ∩ U).card ≤ min (S ∩ U).card (S.card - 2) + 2 := by
  have hsub : (S ∩ U).card ≤ S.card := Finset.card_le_card inter_subset_left
  omega

/-- Summed local truncation loses at most twice the number of coordinates. -/
theorem incidence_le_projectedBudget_add_two_mul
    {X J : Type} [Fintype X] [DecidableEq J]
    (support : X -> Finset J) (U : Finset J) :
    (∑ x : X, (support x ∩ U).card) ≤
      projectedBudget support U + 2 * Fintype.card X := by
  calc
    (∑ x : X, (support x ∩ U).card)
        ≤ ∑ x : X, (min (support x ∩ U).card ((support x).card - 2) + 2) := by
          exact Finset.sum_le_sum fun x _hx => local_card_le_projected_add_two (support x) U
    _ = projectedBudget support U + 2 * Fintype.card X := by
      simp [projectedBudget, Finset.sum_add_distrib, mul_comm]

/-- Double-counting support incidences by coordinates or by labels. -/
theorem sum_inter_card_eq_sum_label_degree
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) (U : Finset J) :
    (∑ x : X, (support x ∩ U).card) =
      ∑ j ∈ U, (Finset.univ.filter fun x : X => j ∈ support x).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [Finset.sum_ite_mem, Finset.sum_const_zero, add_zero]
  rw [Finset.inter_comm]

/-- Uniform label support `T` gives the raw incidence lower bound `|U|*T`. -/
theorem card_mul_le_incidence
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) (U : Finset J) (t : Nat)
    (hsize : ∀ j ∈ U, t ≤ (Finset.univ.filter fun x : X => j ∈ support x).card) :
    U.card * t ≤ ∑ x : X, (support x ∩ U).card := by
  rw [sum_inter_card_eq_sum_label_degree support U]
  calc
    U.card * t = ∑ _j ∈ U, t := by simp
    _ ≤ ∑ j ∈ U, (Finset.univ.filter fun x : X => j ∈ support x).card := by
      exact Finset.sum_le_sum fun j hj => hsize j hj

/-! ## Complement-weighted loss -/

/-- Local weighted loss inequality.  Here `s` is the number of labels of `U` incident at a
coordinate, `z` the number of outside labels incident there, and `w` the total number of outside
labels.  Zero outsiders can cost two local dimensions, one outsider can cost one, and two
outsiders cost none. -/
theorem weighted_local_truncation (s z w : Nat) (hw : 2 ≤ w) (hz : z ≤ w) :
    w * s ≤ w * min s (s + z - 2) + 2 * (w - z) := by
  by_cases hz0 : z = 0
  · subst z
    simp only [add_zero, Nat.sub_zero]
    by_cases hs : 2 ≤ s
    · have hsplit : s = (s - 2) + 2 := by omega
      rw [hsplit, Nat.mul_add]
      simp [Nat.mul_comm, Nat.add_comm]
    · have hsle : s ≤ 1 := by omega
      interval_cases s <;> simp <;> omega
  by_cases hz1 : z = 1
  · subst z
    by_cases hs : s = 0
    · subst s
      simp
    · have hspos : 1 ≤ s := by omega
      have hmin : min s (s + 1 - 2) = s - 1 := by
        rw [min_eq_right] <;> omega
      have hsplit : s = (s - 1) + 1 := by omega
      have hwloss : w ≤ 2 * (w - 1) := by omega
      rw [hmin, hsplit, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_left hwloss _
  have hz2 : 2 ≤ z := by omega
  have hs : s ≤ s + z - 2 := by omega
  rw [min_eq_left hs]
  exact Nat.le_add_right _ _

/-- Finset form of the local weighted loss inequality. -/
theorem weighted_local_support_truncation
    {J : Type} [Fintype J] [DecidableEq J]
    (S U : Finset J) (hw : 2 ≤ (Finset.univ \ U).card) :
    (Finset.univ \ U).card * (S ∩ U).card ≤
      (Finset.univ \ U).card * min (S ∩ U).card (S.card - 2) +
        2 * ((Finset.univ \ U).card - (S \ U).card) := by
  let w := (Finset.univ \ U).card
  let s := (S ∩ U).card
  let z := (S \ U).card
  have hz : z ≤ w := by
    apply Finset.card_le_card
    intro j hj
    simp only [z, w, Finset.mem_sdiff, Finset.mem_univ, true_and] at hj ⊢
    exact hj.2
  have hsplit : s + z = S.card := by
    simpa only [s, z, add_comm] using Finset.card_sdiff_add_card_inter S U
  have hlocal := weighted_local_truncation s z w hw hz
  simpa only [w, s, z, hsplit] using hlocal

/-- Summing the weighted local inequality and charging low-outside coordinates against the
outside labels' own incidences improves the global loss from `2*|X|` to `2*(|X|-t)`. -/
theorem incidence_le_projectedBudget_add_complement_loss
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X -> Finset J) (U : Finset J) (t : Nat)
    (hw : 2 ≤ (Finset.univ \ U).card) (ht : t ≤ Fintype.card X)
    (hout : ∀ j ∈ (Finset.univ \ U),
      t ≤ (Finset.univ.filter fun x : X => j ∈ support x).card) :
    (∑ x : X, (support x ∩ U).card) ≤
      projectedBudget support U + 2 * (Fintype.card X - t) := by
  classical
  let W : Finset J := Finset.univ \ U
  let w := W.card
  let outsideAt : X -> Nat := fun x => (support x \ U).card
  have hwpos : 0 < w := lt_of_lt_of_le (by omega : 0 < 2) hw
  have houtside_le : ∀ x, outsideAt x ≤ w := by
    intro x
    apply Finset.card_le_card
    intro j hj
    simp only [outsideAt, W, Finset.mem_sdiff, Finset.mem_univ, true_and] at hj ⊢
    exact hj.2
  have hlocal : ∀ x,
      w * (support x ∩ U).card ≤
        w * min (support x ∩ U).card ((support x).card - 2) +
          2 * (w - outsideAt x) := by
    intro x
    simpa only [w, W, outsideAt] using weighted_local_support_truncation (support x) U hw
  have hsumLocal :
      ∑ x : X, w * (support x ∩ U).card ≤
        ∑ x : X, (w * min (support x ∩ U).card ((support x).card - 2) +
          2 * (w - outsideAt x)) :=
    Finset.sum_le_sum fun x _hx => hlocal x
  have houtInc : w * t ≤ ∑ x : X, outsideAt x := by
    have h := card_mul_le_incidence support W t (by simpa only [W] using hout)
    convert h using 1 <;> simp [W, outsideAt, Finset.sdiff_eq_inter_compl]
  have hmissingPartition :
      (∑ x : X, (w - outsideAt x)) + (∑ x : X, outsideAt x) =
        w * Fintype.card X := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x : X, (w - outsideAt x + outsideAt x)) = ∑ _x : X, w := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact Nat.sub_add_cancel (houtside_le x)
      _ = w * Fintype.card X := by simp [Nat.mul_comm]
  have hmissing : ∑ x : X, (w - outsideAt x) ≤ w * (Fintype.card X - t) := by
    have hsplit : w * t + w * (Fintype.card X - t) = w * Fintype.card X := by
      rw [← Nat.mul_add, Nat.add_sub_of_le ht]
    have hadd : (∑ x : X, (w - outsideAt x)) + w * t ≤
        w * (Fintype.card X - t) + w * t := by
      calc
        (∑ x : X, (w - outsideAt x)) + w * t
            ≤ (∑ x : X, (w - outsideAt x)) + (∑ x : X, outsideAt x) :=
              Nat.add_le_add_left houtInc _
        _ = w * Fintype.card X := hmissingPartition
        _ = w * t + w * (Fintype.card X - t) := hsplit.symm
        _ = w * (Fintype.card X - t) + w * t := Nat.add_comm _ _
    exact Nat.le_of_add_le_add_right hadd
  have hscaled : w * (∑ x : X, (support x ∩ U).card) ≤
      w * (projectedBudget support U + 2 * (Fintype.card X - t)) := by
    rw [Finset.mul_sum]
    calc
      ∑ x : X, w * (support x ∩ U).card
          ≤ ∑ x : X, (w * min (support x ∩ U).card ((support x).card - 2) +
            2 * (w - outsideAt x)) := hsumLocal
      _ = w * projectedBudget support U + 2 * (∑ x : X, (w - outsideAt x)) := by
        simp [projectedBudget, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ w * projectedBudget support U + 2 * (w * (Fintype.card X - t)) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 2 hmissing) _
      _ = w * (projectedBudget support U + 2 * (Fintype.card X - t)) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hwpos

theorem seven_gap_gt_two_length : 2 * N < 7 * (T - K) := by
  norm_num [N, T, K]

theorem three_gap_gt_complement_loss : 2 * (N - T) < 3 * (T - K) := by
  norm_num [N, T, K]

/-- **Complement-weighted P1 localization.**  If at least two selected labels lie outside `U`,
their own large supports pay for every local codimension-two loss.  Hence every `|U| >= 3` has
projected budget at least `K*|U|`.  Only singleton and pair subsets can remain Hall-obstructive. -/
theorem p1_card_mul_K_le_projectedBudget_of_three_le
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) (U : Finset J)
    (hthree : 3 ≤ U.card) (houtside : 2 ≤ (Finset.univ \ U).card)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    U.card * K ≤ projectedBudget support U := by
  have hinc := card_mul_le_incidence support U T (fun j _hj => hsize j)
  have hloss := incidence_le_projectedBudget_add_complement_loss
    support U T houtside (by norm_num [N, T])
    (fun j _hj => hsize j)
  simp only [Fintype.card_fin] at hloss
  have hgap : 2 * (N - T) ≤ U.card * (T - K) := by
    have hmono : 3 * (T - K) ≤ U.card * (T - K) :=
      Nat.mul_le_mul_right (T - K) hthree
    exact three_gap_gt_complement_loss.le.trans hmono
  have hkT : K ≤ T := by norm_num [K, T]
  have hsplit : U.card * K + U.card * (T - K) = U.card * T := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkT]
  have hwithLoss : U.card * K + 2 * (N - T) ≤
      projectedBudget support U + 2 * (N - T) := by
    calc
      U.card * K + 2 * (N - T) ≤ U.card * K + U.card * (T - K) :=
        Nat.add_le_add_left hgap _
      _ = U.card * T := hsplit
      _ ≤ ∑ x : Fin N, (support x ∩ U).card := hinc
      _ ≤ projectedBudget support U + 2 * (N - T) := hloss
  exact Nat.le_of_add_le_add_right hwithLoss

/-! ## Singleton exceptional-label census -/

/-- Coordinates of a label on which the whole selected family has multiplicity at most two. -/
def lowMultiplicityCoords {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) (j : J) : Finset X :=
  Finset.univ.filter fun x => j ∈ support x ∧ (support x).card ≤ 2

/-- Double-counting identifies total low-multiplicity label incidence with the coordinate-side
sum of multiplicities truncated above two. -/
theorem sum_lowMultiplicityCoords_card_eq
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X -> Finset J) :
    (∑ j : J, (lowMultiplicityCoords support j).card) =
      ∑ x : X, if (support x).card ≤ 2 then (support x).card else 0 := by
  classical
  simp only [lowMultiplicityCoords, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hd : (support x).card ≤ 2
  · simp [hd]
  · simp [hd]

/-- Total low-multiplicity incidence mass is at most twice the universe size. -/
theorem sum_lowMultiplicityCoords_card_le_two_mul
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X -> Finset J) :
    (∑ j : J, (lowMultiplicityCoords support j).card) ≤ 2 * Fintype.card X := by
  classical
  calc
    (∑ j : J, (lowMultiplicityCoords support j).card)
        = ∑ x : X, if (support x).card ≤ 2 then (support x).card else 0 :=
          sum_lowMultiplicityCoords_card_eq support
    _ ≤ ∑ _x : X, 2 := by
      apply Finset.sum_le_sum
      intro x _hx
      split <;> omega
    _ = 2 * Fintype.card X := by simp [Nat.mul_comm]

/-- Pointwise incidence/low-mass tradeoff for a family of `m` labels. -/
theorem two_mul_degree_add_low_weight_le
    (d m : Nat) (hdm : d ≤ m) :
    2 * d + (m - 2) * (if d ≤ 2 then d else 0) ≤ 2 * m := by
  by_cases hd : d ≤ 2
  · simp only [hd, if_true]
    interval_cases d <;> simp <;> omega
  · simp only [hd, if_false, mul_zero, add_zero]
    exact Nat.mul_le_mul_left 2 hdm

/-- Summed pointwise tradeoff. -/
theorem two_mul_totalIncidence_add_low_weight_le
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X -> Finset J) :
    2 * (∑ x : X, (support x).card) +
        (Fintype.card J - 2) * (∑ j : J, (lowMultiplicityCoords support j).card) ≤
      2 * Fintype.card J * Fintype.card X := by
  rw [sum_lowMultiplicityCoords_card_eq support, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc
    (∑ x : X, (2 * (support x).card +
      (Fintype.card J - 2) * (if (support x).card ≤ 2 then (support x).card else 0)))
        ≤ ∑ _x : X, 2 * Fintype.card J := by
          apply Finset.sum_le_sum
          intro x _hx
          apply two_mul_degree_add_low_weight_le
          simpa using Finset.card_le_univ (support x)
    _ = 2 * Fintype.card J * Fintype.card X := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- P1 weighted low-incidence mass bound for exactly `N+1` selected labels. -/
theorem p1_weighted_lowMultiplicity_mass
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    (N + 1 - 2) * (∑ j : J, (lowMultiplicityCoords support j).card) ≤
      2 * (N + 1) * (N - T) := by
  have hinc := card_mul_le_incidence support (Finset.univ : Finset J) T
    (fun j _hj => hsize j)
  simp only [Finset.inter_univ, Finset.card_univ, hcard] at hinc
  have htrade := two_mul_totalIncidence_add_low_weight_le support
  simp only [Fintype.card_fin, hcard] at htrade
  have htrade' : 2 * ((N + 1) * T) +
      (N + 1 - 2) * (∑ j : J, (lowMultiplicityCoords support j).card) ≤
        2 * (N + 1) * N := by
    calc
      2 * ((N + 1) * T) +
          (N + 1 - 2) * (∑ j : J, (lowMultiplicityCoords support j).card)
          ≤ 2 * (∑ x : Fin N, (support x).card) +
            (N + 1 - 2) * (∑ j : J, (lowMultiplicityCoords support j).card) :=
              Nat.add_le_add_right (Nat.mul_le_mul_left 2 hinc) _
      _ ≤ 2 * (N + 1) * N := htrade
  have hsplit : 2 * ((N + 1) * T) + 2 * (N + 1) * (N - T) =
      2 * (N + 1) * N := by
    have hTN : T ≤ N := by norm_num [T, N]
    calc
      2 * ((N + 1) * T) + 2 * (N + 1) * (N - T)
          = 2 * (N + 1) * (T + (N - T)) := by ring
      _ = 2 * (N + 1) * N := by rw [Nat.add_sub_of_le hTN]
  apply Nat.le_of_add_le_add_left
    (a := 2 * ((N + 1) * T))
  calc
    2 * ((N + 1) * T) +
        (N + 1 - 2) * (∑ j : J, (lowMultiplicityCoords support j).card)
        ≤ 2 * (N + 1) * N := htrade'
    _ = 2 * ((N + 1) * T) + 2 * (N + 1) * (N - T) := hsplit.symm

/-- Labels carrying more than `T-K` low-multiplicity coordinates. -/
def singletonExceptional {X J : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J]
    (support : X -> Finset J) (threshold : Nat) : Finset J :=
  Finset.univ.filter fun j => threshold ≤ (lowMultiplicityCoords support j).card

/-- For a singleton label, projected rank plus low-multiplicity loss is exactly its support
degree. -/
theorem singleton_projectedBudget_add_lowMultiplicity
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) (j : J) :
    projectedBudget support {j} + (lowMultiplicityCoords support j).card =
      (Finset.univ.filter fun x : X => j ∈ support x).card := by
  classical
  rw [projectedBudget, lowMultiplicityCoords, Finset.card_eq_sum_ones,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hj : j ∈ support x
  · have hinter : (support x ∩ {j}).card = 1 := by simp [hj]
    rw [hinter]
    by_cases hd : (support x).card ≤ 2
    · have hsub : (support x).card - 2 = 0 := by omega
      simp [hj, hd, hsub]
    · have hd3 : 3 ≤ (support x).card := by omega
      have hsub : 1 ≤ (support x).card - 2 := by omega
      simp [hj, hd, min_eq_left hsub]
  · have hinter : (support x ∩ {j}).card = 0 := by simp [hj]
    simp [hj, hinter]

/-- Singleton Hall failure forces the exact low-multiplicity exceptional threshold. -/
theorem mem_singletonExceptional_of_singleton_projectedBudget_lt
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X -> Finset J) {j : J} {t k : Nat}
    (hkt : k ≤ t)
    (hsize : t ≤ (Finset.univ.filter fun x : X => j ∈ support x).card)
    (hbad : projectedBudget support {j} < k) :
    j ∈ singletonExceptional support (t - k + 1) := by
  simp only [singletonExceptional, Finset.mem_filter, Finset.mem_univ, true_and]
  have hpartition := singleton_projectedBudget_add_lowMultiplicity support j
  omega

/-- Labels whose singleton projected budget is below `K`. -/
def singletonHallBad {X J : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J]
    (support : X -> Finset J) (k : Nat) : Finset J :=
  Finset.univ.filter fun j => projectedBudget support {j} < k

/-! ## Exact pair deficiency -/

/-- Coordinates containing both labels where the whole family has multiplicity exactly three. -/
def exactMultiplicityThreePairCoords
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) (j k : J) : Finset X :=
  Finset.univ.filter fun x => j ∈ support x ∧ k ∈ support x ∧ (support x).card = 3

/-- **Exact pair partition.**  Pair projected rank differs from the sum of the two singleton
partitions only at exact-multiplicity-three coordinates containing both labels. -/
theorem pair_projectedBudget_add_losses
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) {j k : J} (hjk : j ≠ k) :
    projectedBudget support {j, k} +
        (lowMultiplicityCoords support j).card +
        (lowMultiplicityCoords support k).card +
        (exactMultiplicityThreePairCoords support j k).card =
      (Finset.univ.filter fun x : X => j ∈ support x).card +
        (Finset.univ.filter fun x : X => k ∈ support x).card := by
  classical
  rw [projectedBudget, lowMultiplicityCoords, lowMultiplicityCoords,
    exactMultiplicityThreePairCoords,
    Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  have hinter : (support x ∩ {j, k}).card =
      (if j ∈ support x then 1 else 0) + (if k ∈ support x then 1 else 0) := by
    by_cases hj : j ∈ support x <;> by_cases hk : k ∈ support x <;>
      simp [hj, hk, hjk]
  rw [hinter]
  by_cases hj : j ∈ support x <;>
    by_cases hk : k ∈ support x <;>
      by_cases hd2 : (support x).card ≤ 2 <;>
        by_cases hd3 : (support x).card = 3 <;>
          simp [hj, hk, hd2, hd3] <;> omega

/-- Pair budget is the sum of singleton budgets minus the exact-three overlap correction. -/
theorem pair_projectedBudget_add_exactThree_eq_singletons
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) {j k : J} (hjk : j ≠ k) :
    projectedBudget support {j, k} +
        (exactMultiplicityThreePairCoords support j k).card =
      projectedBudget support {j} + projectedBudget support {k} := by
  have hpair := pair_projectedBudget_add_losses support hjk
  have hj := singleton_projectedBudget_add_lowMultiplicity support j
  have hk := singleton_projectedBudget_add_lowMultiplicity support k
  omega

/-- A pair Hall failure between singleton-safe labels requires the exact-three correction to
strictly exceed the sum of both singleton surpluses above `K`. -/
theorem exactThree_gt_singleton_surplus_of_pair_bad
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) {j k : J} (hjk : j ≠ k) {degree : Nat}
    (hjSafe : degree ≤ projectedBudget support {j})
    (hkSafe : degree ≤ projectedBudget support {k})
    (hpairBad : projectedBudget support {j, k} < 2 * degree) :
    (projectedBudget support {j} - degree) +
        (projectedBudget support {k} - degree) <
      (exactMultiplicityThreePairCoords support j k).card := by
  have hidentity := pair_projectedBudget_add_exactThree_eq_singletons support hjk
  omega

/-- **Four-pair arithmetic capstone.**  The sharp P1 low-mass ledger is incompatible with four
disjoint pair obstructions.  `surplus` is the sum of the eight singleton surpluses, `exactThree`
the sum of the four (disjoint) exact-three coordinate counts, and `lowMass` bounds the low
multiplicity contribution of those endpoints. -/
theorem p1_no_four_pair_obstruction_ledger
    (lowMass surplus exactThree : Nat)
    (hlow : (N + 1 - 2) * lowMass ≤ 2 * (N + 1) * (N - T))
    (hsurplus : 8 * (T - K) ≤ surplus + lowMass)
    (hpair : surplus + 4 ≤ exactThree)
    (hexact : exactThree ≤ N) : False := by
  have hcombined : 8 * (T - K) + 4 ≤ N + lowMass := by omega
  have hweighted : (N + 1 - 2) * (8 * (T - K) + 4 - N) ≤
      (N + 1 - 2) * lowMass := by
    apply Nat.mul_le_mul_left
    omega
  have hnumeric : 2 * (N + 1) * (N - T) <
      (N + 1 - 2) * (8 * (T - K) + 4 - N) := by
    norm_num [N, T, K]
  exact (Nat.not_lt_of_ge (hweighted.trans hlow)) hnumeric

/-! ## Four disjoint bad pairs -/

/-- Endpoint map for four labelled pairs. -/
def pairEndpoint {J : Type} (a b : Fin 4 -> J) : Fin 4 × Fin 2 -> J :=
  fun p => ![a p.1, b p.1] p.2

@[simp]
theorem pairEndpoint_zero {J : Type} (a b : Fin 4 -> J) (i : Fin 4) :
    pairEndpoint a b (i, 0) = a i := rfl

@[simp]
theorem pairEndpoint_one {J : Type} (a b : Fin 4 -> J) (i : Fin 4) :
    pairEndpoint a b (i, 1) = b i := rfl

/-- Exact-three coordinate sets belonging to vertex-disjoint pairs are disjoint. -/
theorem exactThreePairCoords_disjoint_of_endpoint_injective
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) (a b : Fin 4 -> J)
    (hinj : Function.Injective (pairEndpoint a b))
    {i l : Fin 4} (hil : i ≠ l) :
    Disjoint (exactMultiplicityThreePairCoords support (a i) (b i))
      (exactMultiplicityThreePairCoords support (a l) (b l)) := by
  rw [Finset.disjoint_left]
  intro x hxi hxl
  have hi := (Finset.mem_filter.mp hxi).2
  have hl := (Finset.mem_filter.mp hxl).2
  let Q : Finset (Fin 4 × Fin 2) := ({i, l} : Finset (Fin 4)) ×ˢ Finset.univ
  let e : (Fin 4 × Fin 2) ↪ J := ⟨pairEndpoint a b, hinj⟩
  have hQcard : Q.card = 4 := by
    simp [Q, hil]
  have hsub : Q.map e ⊆ support x := by
    intro y hy
    simp only [Finset.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rcases p with ⟨pi, ps⟩
    have hp' : (pi = i ∨ pi = l) := by
      have := (Finset.mem_product.mp hp).1
      simpa [Q] using this
    rcases hp' with rfl | rfl
    · fin_cases ps
      · exact hi.1
      · exact hi.2.1
    · fin_cases ps
      · exact hl.1
      · exact hl.2.1
  have hfour : 4 ≤ (support x).card := by
    calc
      4 = Q.card := hQcard.symm
      _ = (Q.map e).card := by simp
      _ ≤ (support x).card := Finset.card_le_card hsub
  omega

/-- Four vertex-disjoint pairs use at most the whole coordinate universe in exact-three sets. -/
theorem sum_four_exactThreePairCoords_le
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X -> Finset J) (a b : Fin 4 -> J)
    (hinj : Function.Injective (pairEndpoint a b)) :
    (∑ i : Fin 4,
      (exactMultiplicityThreePairCoords support (a i) (b i)).card) ≤
      Fintype.card X := by
  let E : Fin 4 -> Finset X := fun i =>
    exactMultiplicityThreePairCoords support (a i) (b i)
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      ∀ l ∈ (Finset.univ : Finset (Fin 4)), i ≠ l -> Disjoint (E i) (E l) := by
    intro i _hi l _hl hil
    exact exactThreePairCoords_disjoint_of_endpoint_injective support a b hinj hil
  have hcard := Finset.card_biUnion hdisj
  calc
    (∑ i : Fin 4, (exactMultiplicityThreePairCoords support (a i) (b i)).card)
        = ((Finset.univ : Finset (Fin 4)).biUnion E).card := by
          simpa only [E] using hcard.symm
    _ ≤ (Finset.univ : Finset X).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card X := Finset.card_univ

/-- Low-multiplicity mass on eight distinct endpoints is bounded by the global low mass. -/
theorem sum_pairEndpoint_lowMultiplicity_le
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X -> Finset J) (a b : Fin 4 -> J)
    (hinj : Function.Injective (pairEndpoint a b)) :
    (∑ p : Fin 4 × Fin 2,
      (lowMultiplicityCoords support (pairEndpoint a b p)).card) ≤
      ∑ j : J, (lowMultiplicityCoords support j).card := by
  let e : (Fin 4 × Fin 2) ↪ J := ⟨pairEndpoint a b, hinj⟩
  calc
    (∑ p : Fin 4 × Fin 2,
      (lowMultiplicityCoords support (pairEndpoint a b p)).card) =
        ∑ j ∈ (Finset.univ : Finset (Fin 4 × Fin 2)).map e,
          (lowMultiplicityCoords support j).card := by
            rw [Finset.sum_map]
            rfl
    _ ≤ ∑ j : J, (lowMultiplicityCoords support j).card :=
      sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

/-- **No four-edge matching in the pair-obstruction graph.**  Four vertex-disjoint pairs of
singleton-safe labels cannot all violate their pair Hall budgets at the literal P1 parameters. -/
theorem not_four_disjoint_pairHallBad
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card)
    (a b : Fin 4 -> J) (hinj : Function.Injective (pairEndpoint a b))
    (hsafe : ∀ p : Fin 4 × Fin 2,
      K ≤ projectedBudget support {pairEndpoint a b p})
    (hbad : ∀ i : Fin 4, projectedBudget support {a i, b i} < 2 * K) : False := by
  let lowMass := ∑ j : J, (lowMultiplicityCoords support j).card
  let surplus := ∑ p : Fin 4 × Fin 2,
    (projectedBudget support {pairEndpoint a b p} - K)
  let exactThree := ∑ i : Fin 4,
    (exactMultiplicityThreePairCoords support (a i) (b i)).card
  have hlow : (N + 1 - 2) * lowMass ≤ 2 * (N + 1) * (N - T) :=
    p1_weighted_lowMultiplicity_mass support hcard hsize
  have hendpointLow :
      (∑ p : Fin 4 × Fin 2,
        (lowMultiplicityCoords support (pairEndpoint a b p)).card) ≤ lowMass :=
    sum_pairEndpoint_lowMultiplicity_le support a b hinj
  have hperEndpoint : ∀ p : Fin 4 × Fin 2,
      T - K ≤ (projectedBudget support {pairEndpoint a b p} - K) +
        (lowMultiplicityCoords support (pairEndpoint a b p)).card := by
    intro p
    have hpartition := singleton_projectedBudget_add_lowMultiplicity
      support (pairEndpoint a b p)
    have hsupport := hsize (pairEndpoint a b p)
    have hsafe' := hsafe p
    omega
  have hsumEndpoint := Finset.sum_le_sum fun p (_hp : p ∈
      (Finset.univ : Finset (Fin 4 × Fin 2))) => hperEndpoint p
  have hsurplus : 8 * (T - K) ≤ surplus + lowMass := by
    have hdecomp :
        (∑ p : Fin 4 × Fin 2,
          ((projectedBudget support {pairEndpoint a b p} - K) +
            (lowMultiplicityCoords support (pairEndpoint a b p)).card)) =
          surplus + ∑ p : Fin 4 × Fin 2,
            (lowMultiplicityCoords support (pairEndpoint a b p)).card := by
      simp only [surplus, Finset.sum_add_distrib]
    have hconst : (∑ _p : Fin 4 × Fin 2, (T - K)) = 8 * (T - K) := by
      simp
    rw [hconst, hdecomp] at hsumEndpoint
    exact hsumEndpoint.trans (Nat.add_le_add_left hendpointLow surplus)
  have hperPair : ∀ i : Fin 4,
      (projectedBudget support {a i} - K) +
          (projectedBudget support {b i} - K) + 1 ≤
        (exactMultiplicityThreePairCoords support (a i) (b i)).card := by
    intro i
    have hi0 : a i ≠ b i := by
      have hp : (i, (0 : Fin 2)) ≠ (i, (1 : Fin 2)) := by
        intro h
        exact Fin.zero_ne_one (congrArg Prod.snd h)
      simpa using hinj.ne hp
    have hgt := exactThree_gt_singleton_surplus_of_pair_bad support hi0
      (hsafe (i, 0)) (hsafe (i, 1)) (hbad i)
    omega
  have hsumPair := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset (Fin 4))) =>
    hperPair i
  have hsurplusExpand : surplus = ∑ i : Fin 4,
      ((projectedBudget support {a i} - K) +
        (projectedBudget support {b i} - K)) := by
    dsimp only [surplus]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [pairEndpoint]
  have hpair : surplus + 4 ≤ exactThree := by
    calc
      surplus + 4 = ∑ i : Fin 4,
          ((projectedBudget support {a i} - K) +
            (projectedBudget support {b i} - K) + 1) := by
              rw [hsurplusExpand]
              simp [Finset.sum_add_distrib]
      _ ≤ exactThree := by simpa only [exactThree] using hsumPair
  have hexact : exactThree ≤ N := by
    simpa only [exactThree, Fintype.card_fin] using
      (sum_four_exactThreePairCoords_le support a b hinj)
  exact p1_no_four_pair_obstruction_ledger lowMass surplus exactThree
    hlow hsurplus hpair hexact

set_option maxHeartbeats 1000000 in
/-- A relation with no four vertex-disjoint pairs has a vertex cover of cardinality at most six.
This is the elementary greedy maximal-matching bound specialized to the constant needed at P1. -/
theorem exists_six_cover_of_not_four_disjoint
    {J : Type} [Fintype J] [DecidableEq J] (R : J -> J -> Prop)
    (hne : ∀ u v, R u v -> u ≠ v)
    (hfour : forall (a b : Fin 4 -> J),
      Function.Injective (fun p : Fin 4 × Fin 2 => pairEndpoint a b p) ->
      ¬ (∀ i, R (a i) (b i))) :
    ∃ C : Finset J, C.card ≤ 6 ∧
      ∀ u v, R u v -> u ∈ C ∨ v ∈ C := by
  classical
  have card_insert_two_le (u v : J) (S : Finset J) :
      (insert u (insert v S)).card ≤ S.card + 2 := by
    have hu := Finset.card_insert_le u (insert v S)
    have hv := Finset.card_insert_le v S
    omega
  by_cases h0 : ∀ u v, R u v -> u ∈ (∅ : Finset J) ∨ v ∈ (∅ : Finset J)
  · exact ⟨∅, by simp, h0⟩
  push_neg at h0
  obtain ⟨a0, b0, hab0, ha0, hb0⟩ := h0
  let C1 : Finset J := {a0, b0}
  by_cases h1 : ∀ u v, R u v -> u ∈ C1 ∨ v ∈ C1
  · refine ⟨C1, ?_, h1⟩
    dsimp only [C1]
    have := card_insert_two_le a0 b0 ∅
    simpa using this.trans (by norm_num)
  push_neg at h1
  obtain ⟨a1, b1, hab1, ha1, hb1⟩ := h1
  let C2 : Finset J := insert a1 (insert b1 C1)
  by_cases h2 : ∀ u v, R u v -> u ∈ C2 ∨ v ∈ C2
  · refine ⟨C2, ?_, h2⟩
    dsimp only [C2, C1]
    have houter := card_insert_two_le a1 b1 {a0, b0}
    have hinner : ({a0, b0} : Finset J).card ≤ 2 := by
      simpa only [Finset.card_empty, Nat.zero_add] using card_insert_two_le a0 b0 ∅
    omega
  push_neg at h2
  obtain ⟨a2, b2, hab2, ha2, hb2⟩ := h2
  let C3 : Finset J := insert a2 (insert b2 C2)
  by_cases h3 : ∀ u v, R u v -> u ∈ C3 ∨ v ∈ C3
  · refine ⟨C3, ?_, h3⟩
    dsimp only [C3, C2, C1]
    have h2c := card_insert_two_le a2 b2 (insert a1 (insert b1 {a0, b0}))
    have h1c := card_insert_two_le a1 b1 {a0, b0}
    have h0c : ({a0, b0} : Finset J).card ≤ 2 := by
      simpa only [Finset.card_empty, Nat.zero_add] using card_insert_two_le a0 b0 ∅
    omega
  push_neg at h3
  obtain ⟨a3, b3, hab3, ha3, hb3⟩ := h3
  let a : Fin 4 -> J := ![a0, a1, a2, a3]
  let b : Fin 4 -> J := ![b0, b1, b2, b3]
  have hne0 : a0 ≠ b0 := hne _ _ hab0
  have hne1 : a1 ≠ b1 := hne _ _ hab1
  have hne2 : a2 ≠ b2 := hne _ _ hab2
  have hne3 : a3 ≠ b3 := hne _ _ hab3
  simp only [C1, Finset.mem_insert, Finset.mem_singleton] at ha1 hb1
  simp only [C2, C1, Finset.mem_insert, Finset.mem_singleton] at ha2 hb2
  simp only [C3, C2, C1, Finset.mem_insert, Finset.mem_singleton] at ha3 hb3
  have hinj : Function.Injective (fun p : Fin 4 × Fin 2 => pairEndpoint a b p) := by
    rintro ⟨i, e⟩ ⟨j, f⟩ hpq
    fin_cases i <;> fin_cases j <;> fin_cases e <;> fin_cases f <;>
      simp [a, b, pairEndpoint] at hpq ⊢ <;> aesop
  have hall : ∀ i, R (a i) (b i) := by
    intro i
    fin_cases i <;> simp [a, b, hab0, hab1, hab2, hab3]
  exact ((hfour a b hinj) hall).elim

/-- **Concrete P1 pair-obstruction cover.**  After removing at most six labels, every pair of
distinct singleton-safe labels has the full `2 * K` projected Hall budget. -/
theorem exists_six_label_pairHall_cover
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    ∃ C : Finset J, C.card ≤ 6 ∧ ∀ u v : J,
      u ≠ v -> K ≤ projectedBudget support {u} -> K ≤ projectedBudget support {v} ->
      u ∉ C -> v ∉ C -> 2 * K ≤ projectedBudget support {u, v} := by
  let R : J -> J -> Prop := fun u v =>
    u ≠ v ∧ K ≤ projectedBudget support {u} ∧ K ≤ projectedBudget support {v} ∧
      projectedBudget support {u, v} < 2 * K
  have hne : ∀ u v, R u v -> u ≠ v := fun _ _ h => h.1
  have hfour : ∀ (a b : Fin 4 -> J),
      Function.Injective (fun p : Fin 4 × Fin 2 => pairEndpoint a b p) ->
      ¬ (∀ i, R (a i) (b i)) := by
    intro a b hinj hall
    apply not_four_disjoint_pairHallBad support hcard hsize a b hinj
    · intro p
      rcases p with ⟨i, e⟩
      fin_cases e
      · exact (hall i).2.1
      · exact (hall i).2.2.1
    · exact fun i => (hall i).2.2.2
  obtain ⟨C, hCcard, hC⟩ := exists_six_cover_of_not_four_disjoint R hne hfour
  refine ⟨C, hCcard, ?_⟩
  intro u v huv hu hv huC hvC
  by_contra hbad
  have hR : R u v := ⟨huv, hu, hv, by omega⟩
  exact (hC u v hR).elim huC hvC

/-- Any uniform threshold on the exceptional labels charges against the global low-multiplicity
mass. -/
theorem singletonExceptional_card_mul_threshold_le
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X -> Finset J) (threshold : Nat) :
    (singletonExceptional support threshold).card * threshold ≤ 2 * Fintype.card X := by
  calc
    (singletonExceptional support threshold).card * threshold =
        ∑ _j ∈ singletonExceptional support threshold, threshold := by simp
    _ ≤ ∑ j ∈ singletonExceptional support threshold,
        (lowMultiplicityCoords support j).card := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [singletonExceptional] using hj
    _ ≤ ∑ j : J, (lowMultiplicityCoords support j).card := by
      exact sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ 2 * Fintype.card X := sum_lowMultiplicityCoords_card_le_two_mul support

theorem seven_singleton_threshold_gt_two_length :
    2 * N < 7 * (T - K + 1) := by
  norm_num [N, T, K]

theorem three_singleton_threshold_weighted_gt :
    2 * (N + 1) * (N - T) < (N + 1 - 2) * (3 * (T - K + 1)) := by
  norm_num [N, T, K]

/-- At P1, at most six labels can carry enough low-multiplicity coordinates to obstruct a
singleton `K`-column Hall budget. -/
theorem p1_singletonExceptional_card_le_six
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) :
    (singletonExceptional support (T - K + 1)).card ≤ 6 := by
  have hmass := singletonExceptional_card_mul_threshold_le
    support (T - K + 1)
  simp only [Fintype.card_fin] at hmass
  by_contra hnot
  have hseven : 7 ≤ (singletonExceptional support (T - K + 1)).card := by omega
  have hlarge : 7 * (T - K + 1) ≤
      (singletonExceptional support (T - K + 1)).card * (T - K + 1) :=
    Nat.mul_le_mul_right (T - K + 1) hseven
  exact (Nat.not_lt_of_ge (hlarge.trans hmass)) seven_singleton_threshold_gt_two_length

/-- With exactly `N+1` selected labels, the sharper weighted census leaves at most two
singleton-Hall exceptions, matching the two available gauge anchors. -/
theorem p1_singletonExceptional_card_le_two
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    (singletonExceptional support (T - K + 1)).card ≤ 2 := by
  have hexMass := singletonExceptional_card_mul_threshold_le
    support (T - K + 1)
  have hlowMass := p1_weighted_lowMultiplicity_mass support hcard hsize
  have hexToLow :
      (singletonExceptional support (T - K + 1)).card * (T - K + 1) ≤
        ∑ j : J, (lowMultiplicityCoords support j).card := by
    calc
      (singletonExceptional support (T - K + 1)).card * (T - K + 1) =
          ∑ _j ∈ singletonExceptional support (T - K + 1), (T - K + 1) := by simp
      _ ≤ ∑ j ∈ singletonExceptional support (T - K + 1),
          (lowMultiplicityCoords support j).card := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [singletonExceptional] using hj
      _ ≤ ∑ j : J, (lowMultiplicityCoords support j).card :=
        sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hweighted := Nat.mul_le_mul_left (N + 1 - 2) hexToLow |>.trans hlowMass
  by_contra hnot
  have hthree : 3 ≤ (singletonExceptional support (T - K + 1)).card := by omega
  have hlarge : (N + 1 - 2) * (3 * (T - K + 1)) ≤
      (N + 1 - 2) *
        ((singletonExceptional support (T - K + 1)).card * (T - K + 1)) := by
    apply Nat.mul_le_mul_left
    exact Nat.mul_le_mul_right (T - K + 1) hthree
  exact (Nat.not_lt_of_ge (hlarge.trans hweighted)) three_singleton_threshold_weighted_gt

/-- **Exact P1 singleton-Hall census.**  At most six labels can have fewer than `K` projected
singleton constraints. -/
theorem p1_singletonHallBad_card_le_six
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    (singletonHallBad support K).card ≤ 6 := by
  apply (Finset.card_le_card ?_).trans (p1_singletonExceptional_card_le_six support)
  intro j hj
  simp only [singletonHallBad, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact mem_singletonExceptional_of_singleton_projectedBudget_lt
    support (by norm_num [K, T]) (hsize j) hj

/-- **Sharp anchor census.**  For exactly `N+1` labels, at most two singleton Hall failures
remain, so the two gauge anchors can cover all of them. -/
theorem p1_singletonHallBad_card_le_two
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    (singletonHallBad support K).card ≤ 2 := by
  apply (Finset.card_le_card ?_).trans
    (p1_singletonExceptional_card_le_two support hcard hsize)
  intro j hj
  simp only [singletonHallBad, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact mem_singletonExceptional_of_singleton_projectedBudget_lt
    support (by norm_num [K, T]) (hsize j) hj

/-- The two gauge anchors can be chosen to contain every singleton Hall exception. -/
theorem exists_anchor_pair_covering_singletonHallBad
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N -> Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    ∃ a b : J, a ≠ b ∧ ∀ j : J, j ≠ a -> j ≠ b ->
      K ≤ projectedBudget support {j} := by
  let E := singletonHallBad support K
  have hE : E.card ≤ 2 := p1_singletonHallBad_card_le_two support hcard hsize
  have hJ : 2 ≤ (Finset.univ : Finset J).card := by
    simp only [Finset.card_univ, hcard]
    norm_num [N]
  obtain ⟨A, hEA, _hAuniv, hAcard⟩ :=
    Finset.exists_subsuperset_card_eq (s := E) (t := (Finset.univ : Finset J))
      (Finset.subset_univ E) hE hJ
  rw [Finset.card_eq_two] at hAcard
  obtain ⟨a, b, hab, rfl⟩ := hAcard
  refine ⟨a, b, hab, ?_⟩
  intro j hja hjb
  by_contra hnot
  have hjE : j ∈ E := by
    simp only [E, singletonHallBad, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hjA := hEA hjE
  simp only [Finset.mem_insert, Finset.mem_singleton] at hjA
  exact hjA.elim hja hjb

/-- **P1 small-subset localization.**  Every label subset of cardinality at least seven has
enough projected divided-difference rows to cover `K` coefficient columns per label. -/
theorem p1_card_mul_K_le_projectedBudget_of_seven_le
    {J : Type} [DecidableEq J]
    (support : Fin N -> Finset J) (U : Finset J)
    (hseven : 7 ≤ U.card)
    (hsize : ∀ j ∈ U, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    U.card * K ≤ projectedBudget support U := by
  have hinc := card_mul_le_incidence support U T hsize
  have hloss := incidence_le_projectedBudget_add_two_mul support U
  simp only [Fintype.card_fin] at hloss
  have hgap : 2 * N ≤ U.card * (T - K) := by
    have hmono : 7 * (T - K) ≤ U.card * (T - K) :=
      Nat.mul_le_mul_right (T - K) hseven
    exact seven_gap_gt_two_length.le.trans hmono
  have hkT : K ≤ T := by norm_num [K, T]
  have hsplit : U.card * K + U.card * (T - K) = U.card * T := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkT]
  have hwithLoss : U.card * K + 2 * N ≤
      projectedBudget support U + 2 * N := by
    calc
      U.card * K + 2 * N ≤ U.card * K + U.card * (T - K) :=
        Nat.add_le_add_left hgap _
      _ = U.card * T := hsplit
      _ ≤ ∑ x : Fin N, (support x ∩ U).card := hinc
      _ ≤ projectedBudget support U + 2 * N := hloss
  exact Nat.le_of_add_le_add_right hwithLoss

end ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization

open ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization
#print axioms incidence_le_projectedBudget_add_two_mul
#print axioms incidence_le_projectedBudget_add_complement_loss
#print axioms sum_inter_card_eq_sum_label_degree
#print axioms p1_card_mul_K_le_projectedBudget_of_three_le
#print axioms p1_singletonExceptional_card_le_six
#print axioms p1_singletonExceptional_card_le_two
#print axioms p1_singletonHallBad_card_le_six
#print axioms p1_singletonHallBad_card_le_two
#print axioms exists_anchor_pair_covering_singletonHallBad
#print axioms pair_projectedBudget_add_losses
#print axioms pair_projectedBudget_add_exactThree_eq_singletons
#print axioms exactThree_gt_singleton_surplus_of_pair_bad
#print axioms p1_no_four_pair_obstruction_ledger
#print axioms exactThreePairCoords_disjoint_of_endpoint_injective
#print axioms sum_four_exactThreePairCoords_le
#print axioms not_four_disjoint_pairHallBad
#print axioms exists_six_cover_of_not_four_disjoint
#print axioms exists_six_label_pairHall_cover
#print axioms p1_card_mul_K_le_projectedBudget_of_seven_le
