/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Connections.GCXK25SecondMoment
import Mathlib.Analysis.SpecialFunctions.Pochhammer
import Mathlib.Tactic

/-!
# R387: Johnson pruning at the half-radius predecessor, rate at most `1/8`

This file contains the abstract combinatorial and numerical engine of the following
argument.  Write the block length as `2h`, with `h = 16m`, and suppose the
Reed--Solomon degree parameter is at most `h/4`; thus the common-codegree cap is
`d = 4m-1`.

For every secant line containing at least five selected rich points, its common
agreement core has size at least `12m+2`.  Distinct line cores intersect in at most
`4m-1` coordinates.  The constant-weight Johnson inequality therefore allows at
most fifteen such lines.  The lines whose core has size at least `15m+1` number at
most three.  The exact fresh-fibre packing law bounds those three lines by
`(16m+4)/5` points each and all other large lines by sixteen points.  Consequently
their union has size at most `5h/7` for `h >= 2048`.

After deleting that union, every original secant line contains at most four
remaining points.  A third-moment count on the remaining `M > 9h/7` points then
contradicts the rate-`1/8` noncollinear-codegree ceiling.

The statements here are deliberately abstract.  The concrete polynomial secant
geometry only has to supply finite core and point families satisfying the displayed
cardinality and intersection hypotheses.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R387RateEighthPruning

/-! ## A Johnson inequality for a family of nonuniform cores -/

/-- **Johnson core-packing inequality.**  A family of subsets of an `n`-point
universe, each of size at least `Z` and with pairwise intersections at most `d`,
satisfies

`L * (Z^2 - n*d) <= n * (Z-d)`.

No equal-size assumption is made.  Equivalently, one could truncate every member
to a `Z`-subset; the second-moment proof below handles the nonuniform family
directly. -/
theorem johnson_core_packing
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (G : Finset Line) (core : Line → Finset U) (Z d : ℕ)
    (hdZ : d ≤ Z)
    (hsize : ∀ line ∈ G, Z ≤ (core line).card)
    (hinter : ∀ line ∈ G, ∀ line' ∈ G, line ≠ line' →
      (core line ∩ core line').card ≤ d) :
    (G.card : ℝ) * ((Z : ℝ) ^ 2 - (Fintype.card U : ℝ) * d) ≤
      (Fintype.card U : ℝ) * ((Z : ℝ) - d) := by
  classical
  by_cases hG : G.Nonempty
  · have hbase := GCXK25SecondMoment.card_le_of_second_moment
      G core hG (Z : ℝ) (d : ℝ) (by positivity) (by positivity)
      (fun line hline ↦ by exact_mod_cast hsize line hline)
      (fun line hline line' hline' hne ↦ by
        exact_mod_cast hinter line hline line' hline' hne)
    nlinarith
  · have hcard : G.card = 0 := Finset.not_nonempty_iff_eq_empty.mp hG |>.symm ▸ rfl
    simp only [hcard, Nat.cast_zero, zero_mul]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hdZ))

/-- At `h=16m`, cores of size at least `15m+1` with intersections at most
`4m-1` form a family of size at most three. -/
theorem ultra_core_family_card_le_three
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (m : ℕ) (hm : 1 ≤ m) (hU : Fintype.card U = 32 * m)
    (G : Finset Line) (core : Line → Finset U)
    (hsize : ∀ line ∈ G, 15 * m + 1 ≤ (core line).card)
    (hinter : ∀ line ∈ G, ∀ line' ∈ G, line ≠ line' →
      (core line ∩ core line').card ≤ 4 * m - 1) :
    G.card ≤ 3 := by
  have hpred_le : 4 * m - 1 ≤ 15 * m + 1 := by omega
  have hJ := johnson_core_packing G core (15 * m + 1) (4 * m - 1)
    hpred_le hsize hinter
  rw [hU] at hJ
  by_contra hnot
  have hfour : 4 ≤ G.card := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfourR : (4 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hfour
  have h4m : 1 ≤ 4 * m := by omega
  rw [Nat.cast_sub h4m] at hJ
  push_cast at hJ
  have hden : (0 : ℝ) <
      (15 * (m : ℝ) + 1) ^ 2 - 32 * (m : ℝ) * (4 * (m : ℝ) - 1) := by
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hlow : 4 *
      ((15 * (m : ℝ) + 1) ^ 2 - 32 * (m : ℝ) * (4 * (m : ℝ) - 1)) ≤
      (G.card : ℝ) *
        ((15 * (m : ℝ) + 1) ^ 2 - 32 * (m : ℝ) * (4 * (m : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_right hfourR hden.le
  nlinarith

/-- At `h=16m`, cores of size at least `12m+2` with intersections at most
`4m-1` form a family of size at most fifteen. -/
theorem exceptional_core_family_card_le_fifteen
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (m : ℕ) (hm : 1 ≤ m) (hU : Fintype.card U = 32 * m)
    (G : Finset Line) (core : Line → Finset U)
    (hsize : ∀ line ∈ G, 12 * m + 2 ≤ (core line).card)
    (hinter : ∀ line ∈ G, ∀ line' ∈ G, line ≠ line' →
      (core line ∩ core line').card ≤ 4 * m - 1) :
    G.card ≤ 15 := by
  have hpred_le : 4 * m - 1 ≤ 12 * m + 2 := by omega
  have hJ := johnson_core_packing G core (12 * m + 2) (4 * m - 1)
    hpred_le hsize hinter
  rw [hU] at hJ
  by_contra hnot
  have hsixteen : 16 ≤ G.card := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsixteenR : (16 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hsixteen
  have h4m : 1 ≤ 4 * m := by omega
  rw [Nat.cast_sub h4m] at hJ
  push_cast at hJ
  have hden : (0 : ℝ) <
      (12 * (m : ℝ) + 2) ^ 2 - 32 * (m : ℝ) * (4 * (m : ℝ) - 1) := by
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hlow : 16 *
      ((12 * (m : ℝ) + 2) ^ 2 - 32 * (m : ℝ) * (4 * (m : ℝ) - 1)) ≤
      (G.card : ℝ) *
        ((12 * (m : ℝ) + 2) ^ 2 - 32 * (m : ℝ) * (4 * (m : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_right hsixteenR hden.le
  nlinarith

/-! ## Weighted union bound for the exceptional lines -/

/-- A finite family is the disjoint union of a subfamily and its complement,
also at the level of a sum of cardinalities. -/
private theorem sum_eq_sum_subset_add_sdiff
    {Line Point : Type*} [DecidableEq Line]
    (E Q : Finset Line) (points : Line → Finset Point) (hQE : Q ⊆ E) :
    ∑ line ∈ E, (points line).card =
      (∑ line ∈ Q, (points line).card) +
        ∑ line ∈ E \ Q, (points line).card := by
  simpa [add_comm] using (Finset.sum_sdiff (f := fun line ↦ (points line).card) hQE).symm

/-- **Weighted exceptional-line union bound.**  Suppose `E` has at most fifteen
lines, `Q ⊆ E` has at most three ultra-core lines, every ultra line obeys
`5|P_l| ≤ h+4`, and every other exceptional line has at most sixteen points.
For `h ≥ 1701`, the union of all their point sets has size at most `5h/7`.

The point sets need not be disjoint: the ordinary union bound is in the favorable
direction. -/
theorem exceptional_biUnion_seven_mul_card_le_five_mul
    {Line Point : Type*} [DecidableEq Line] [DecidableEq Point]
    (h : ℕ) (hh : 1701 ≤ h)
    (E Q : Finset Line) (points : Line → Finset Point)
    (hQE : Q ⊆ E) (hE : E.card ≤ 15) (hQ : Q.card ≤ 3)
    (hultra : ∀ line ∈ Q, 5 * (points line).card ≤ h + 4)
    (hordinary : ∀ line ∈ E \ Q, (points line).card ≤ 16) :
    7 * (E.biUnion points).card ≤ 5 * h := by
  have hunion : (E.biUnion points).card ≤
      ∑ line ∈ E, (points line).card := Finset.card_biUnion_le
  have hsplit := sum_eq_sum_subset_add_sdiff E Q points hQE
  have hQsum : 5 * (∑ line ∈ Q, (points line).card) ≤ Q.card * (h + 4) := by
    calc
      5 * (∑ line ∈ Q, (points line).card) =
          ∑ line ∈ Q, 5 * (points line).card := by
            rw [Finset.mul_sum]
      _ ≤ ∑ _line ∈ Q, (h + 4) := Finset.sum_le_sum hultra
      _ = Q.card * (h + 4) := by simp
  have hOsum : ∑ line ∈ E \ Q, (points line).card ≤
      (E \ Q).card * 16 := by
    calc
      ∑ line ∈ E \ Q, (points line).card ≤
          ∑ _line ∈ E \ Q, 16 := Finset.sum_le_sum hordinary
      _ = (E \ Q).card * 16 := by simp
  have hQcardE : Q.card ≤ E.card := Finset.card_le_card hQE
  have hsdiff : (E \ Q).card = E.card - Q.card :=
    Finset.card_sdiff_of_subset hQE
  have hh76 : 76 ≤ h := by omega
  have hweighted :
      5 * (∑ line ∈ E, (points line).card) ≤ 3 * h + 972 := by
    have hsplit5 : 5 * (∑ line ∈ E, (points line).card) =
        5 * (∑ line ∈ Q, (points line).card) +
          5 * (∑ line ∈ E \ Q, (points line).card) := by
      rw [hsplit, Nat.mul_add]
    have hO5 : 5 * (∑ line ∈ E \ Q, (points line).card) ≤
        80 * (E.card - Q.card) := by
      rw [← hsdiff]
      nlinarith
    have hraw : 5 * (∑ line ∈ E, (points line).card) ≤
        Q.card * (h + 4) + 80 * (E.card - Q.card) := by
      rw [hsplit5]
      omega
    have hmonoE : 80 * E.card ≤ 80 * 15 := Nat.mul_le_mul_left 80 hE
    have hmonoQ : Q.card * (h - 76) ≤ 3 * (h - 76) :=
      Nat.mul_le_mul_right (h - 76) hQ
    have hrawZ :
        (5 * (∑ line ∈ E, (points line).card) : ℤ) ≤
          (Q.card : ℤ) * ((h : ℤ) + 4) +
            80 * ((E.card : ℤ) - (Q.card : ℤ)) := by
      exact_mod_cast hraw
    have hmonoEZ : (80 : ℤ) * E.card ≤ 80 * 15 := by
      exact_mod_cast hmonoE
    have hmonoQZ : (Q.card : ℤ) * ((h : ℤ) - 76) ≤
        3 * ((h : ℤ) - 76) := by
      exact_mod_cast hmonoQ
    have htargetZ :
        (5 * (∑ line ∈ E, (points line).card) : ℤ) ≤
          3 * (h : ℤ) + 972 := by
      nlinarith
    exact_mod_cast htargetZ
  have hfiveUnion : 5 * (E.biUnion points).card ≤ 3 * h + 972 := by
    nlinarith
  nlinarith

/-- **Complete Johnson-pruning bound at rate `1/8`.**  This packages the two
Johnson estimates and the weighted union calculation. -/
theorem rateEighth_exceptional_union_bound
    {U Line Point : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq Line] [DecidableEq Point]
    (m : ℕ) (hm : 128 ≤ m) (hU : Fintype.card U = 32 * m)
    (E Q : Finset Line) (core : Line → Finset U)
    (points : Line → Finset Point) (hQE : Q ⊆ E)
    (hEcore : ∀ line ∈ E, 12 * m + 2 ≤ (core line).card)
    (hQcore : ∀ line ∈ Q, 15 * m + 1 ≤ (core line).card)
    (hinter : ∀ line ∈ E, ∀ line' ∈ E, line ≠ line' →
      (core line ∩ core line').card ≤ 4 * m - 1)
    (hultra : ∀ line ∈ Q, 5 * (points line).card ≤ 16 * m + 4)
    (hordinary : ∀ line ∈ E \ Q, (points line).card ≤ 16) :
    7 * (E.biUnion points).card ≤ 80 * m := by
  have hm1 : 1 ≤ m := by omega
  have hE := exceptional_core_family_card_le_fifteen
    m hm1 hU E core hEcore hinter
  have hQinter : ∀ line ∈ Q, ∀ line' ∈ Q, line ≠ line' →
      (core line ∩ core line').card ≤ 4 * m - 1 := by
    intro line hline line' hline' hne
    exact hinter line (hQE hline) line' (hQE hline') hne
  have hQ := ultra_core_family_card_le_three
    m hm1 hU Q core hQcore hQinter
  have hh : 1701 ≤ 16 * m := by omega
  have hbound := exceptional_biUnion_seven_mul_card_le_five_mul
    (16 * m) hh E Q points hQE hE hQ hultra hordinary
  nlinarith

/-! ## Elementary arithmetic producing the two line strata -/

/-- A line with at least five points and fresh-fibre parameter `c` must have
`4c+1 <= h`. -/
theorem five_points_force_four_mul_c_add_one_le
    {h c L : ℕ} (hL : 5 ≤ L)
    (hpacking : L * c + (h + 1 - c) ≤ 2 * h)
    (hc : c ≤ h + 1) :
    4 * c + 1 ≤ h := by
  have hcancel : h + 1 - c + c = h + 1 := Nat.sub_add_cancel hc
  have hmul : 5 * c ≤ L * c := Nat.mul_le_mul_right c hL
  omega

/-- If `h=16m`, a five-point line has core size at least `12m+2`. -/
theorem exceptional_core_lower
    {m c z L : ℕ} (hz : z + c = 16 * m + 1) (hL : 5 ≤ L)
    (hpacking : L * c + z ≤ 32 * m) :
    12 * m + 2 ≤ z := by
  nlinarith

/-- If `c <= m`, then the core has size at least `15m+1`. -/
theorem ultra_core_lower
    {m c z : ℕ} (hz : z + c = 16 * m + 1) (hc : c ≤ m) :
    15 * m + 1 ≤ z := by
  omega

/-- Every ultra line obeys the weighted size bound used in the union estimate. -/
theorem ultra_line_weighted_card_bound
    {m c z L : ℕ} (hc : 5 ≤ c) (hz : z + c = 16 * m + 1)
    (hpacking : L * c + z ≤ 32 * m) :
    5 * L ≤ 16 * m + 4 := by
  nlinarith

/-- A non-ultra exceptional line (`m < c`) has at most sixteen points. -/
theorem non_ultra_line_card_le_sixteen
    {m c z L : ℕ} (hc : m < c) (hz : z + c = 16 * m + 1)
    (hpacking : L * c + z ≤ 32 * m) :
    L ≤ 16 := by
  by_contra hnot
  have hL : 17 ≤ L := by omega
  nlinarith

end ArkLib.ProximityGap.Frontier.R387RateEighthPruning

#print axioms ArkLib.ProximityGap.Frontier.R387RateEighthPruning.johnson_core_packing
#print axioms ArkLib.ProximityGap.Frontier.R387RateEighthPruning.ultra_core_family_card_le_three
#print axioms ArkLib.ProximityGap.Frontier.R387RateEighthPruning.exceptional_core_family_card_le_fifteen
#print axioms ArkLib.ProximityGap.Frontier.R387RateEighthPruning.exceptional_biUnion_seven_mul_card_le_five_mul
#print axioms ArkLib.ProximityGap.Frontier.R387RateEighthPruning.rateEighth_exceptional_union_bound
