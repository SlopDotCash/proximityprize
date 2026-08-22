/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import Mathlib.Tactic

/-!
# Set-system bricks for the rate-`1/8` half-predecessor stratification

This file contains the reusable combinatorial pieces of
`docs/kb/deltastar-466-half-predecessor-rate-eighth-2026-07-09.md`.
There is no Reed--Solomon structure here.

* `sharp_johnson_of_lower_upper_pair` keeps the true diagonal upper bound
  `b`, unlike the standard Johnson inequality which replaces it by the size
  of the whole universe.
* `exceptional_family_card_le_fifteen` is the exact `L >= 5` core count.
* `ultra_family_card_le_three` is the `z >= 15h/16` core count.
* `truncation_preserves_pair_cap` explicitly certifies that passing to
  common-size subsets cannot increase pair intersections.
* `pair_inter_le_of_union_floor` is the complement-block calculation behind
  the independent ultra-core exclusion: the number `2c-7` is not heuristic.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics

/-- A three-fold union, plus one selected pair intersection, is bounded by
the sum of the three cardinalities. -/
theorem card_union_union_add_pairInter_le
    {U : Type*} [DecidableEq U] (X Y Z : Finset U) :
    (X ∪ Y ∪ Z).card + (X ∩ Y).card ≤ X.card + Y.card + Z.card := by
  have hunion := Finset.card_union_le (X ∪ Y) Z
  have hpair := Finset.card_union_add_card_inter X Y
  omega

/-- **The exact complement pair cap.**  Suppose three blocks have size at
most `b`, while every allowed extension `Z` of the pair `(X,Y)` has union
size at least `v-d`.  At the balance identity

`3b = (v-d)+s`,

their pair intersection is at most `s`.  In the rate-`1/8` application,
`b=h/4+c-2` and `s=2c-7`. -/
theorem pair_inter_le_of_union_floor
    {U : Type*} [DecidableEq U] (X Y Z : Finset U)
    (v d b s : ℕ)
    (hX : X.card ≤ b) (hY : Y.card ≤ b) (hZ : Z.card ≤ b)
    (hfloor : v - d ≤ (X ∪ Y ∪ Z).card)
    (hbalance : 3 * b = (v - d) + s) :
    (X ∩ Y).card ≤ s := by
  have hcard := card_union_union_add_pairInter_le X Y Z
  omega

/-- If one block is smaller than `b-s`, no triple containing it can reach
the same union floor.  This is the pointwise half of the two-line
alternative in the complement-code argument. -/
theorem block_card_ge_of_union_floor
    {U : Type*} [DecidableEq U] (X Y Z : Finset U)
    (v d b s : ℕ)
    (hY : Y.card ≤ b) (hZ : Z.card ≤ b)
    (hfloor : v - d ≤ (X ∪ Y ∪ Z).card)
    (hbalance : 3 * b = (v - d) + s) :
    b - s ≤ X.card := by
  have hunion := Finset.card_union_le (X ∪ Y) Z
  have hXY := Finset.card_union_le X Y
  omega

/-- **Sharp bounded-block Johnson inequality.**  Every block has size in
`[a,b]` and distinct blocks intersect in at most `s`.  Cauchy--Schwarz with
the exact diagonal `|S_i| <= b` gives

`M a^2 <= v (b+(M-1)s)`.

This is stronger than replacing the diagonal by the whole universe size. -/
theorem sharp_johnson_of_lower_upper_pair
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    [Nonempty κ] (S : κ → Finset ι) (a b s : ℕ)
    (hlo : ∀ i, a ≤ (S i).card)
    (hhi : ∀ i, (S i).card ≤ b)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ s) :
    Fintype.card κ * a ^ 2 ≤
      Fintype.card ι * (b + (Fintype.card κ - 1) * s) := by
  classical
  let M := Fintype.card κ
  let v := Fintype.card ι
  have hlower : M * a ≤ ∑ i, (S i).card := by
    rw [show M * a = ∑ _i : κ, a by
      simp only [M, Finset.sum_const, Finset.card_univ, smul_eq_mul]]
    exact Finset.sum_le_sum (fun i _ => hlo i)
  have hinner : ∀ i : κ,
      (∑ j : κ, (S i ∩ S j).card) ≤ b + (M - 1) * s := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => (S i ∩ S j).card) (Finset.mem_univ i)]
    apply Nat.add_le_add
    · simpa only [Finset.inter_self] using hhi i
    · calc
        ∑ j ∈ (Finset.univ.erase i), (S i ∩ S j).card
            ≤ ∑ _j ∈ (Finset.univ.erase i), s := by
              apply Finset.sum_le_sum
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              exact hpair i j hji.symm
        _ = (M - 1) * s := by
          simp [M, Finset.card_erase_of_mem]
  have hupper :
      (∑ i, ∑ j, (S i ∩ S j).card) ≤ M * (b + (M - 1) * s) := by
    calc
      (∑ i, ∑ j, (S i ∩ S j).card)
          ≤ ∑ _i : κ, (b + (M - 1) * s) :=
            Finset.sum_le_sum (fun i _ => hinner i)
      _ = M * (b + (M - 1) * s) := by
        simp [M]
  have hmass := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter S
  have hkey : (M * a) ^ 2 ≤ v * (M * (b + (M - 1) * s)) :=
    le_trans (Nat.pow_le_pow_left hlower 2)
      (le_trans hmass (Nat.mul_le_mul le_rfl hupper))
  have heqLeft : (M * a) ^ 2 = M * (M * a ^ 2) := by ring
  have heqRight : v * (M * (b + (M - 1) * s)) =
      M * (v * (b + (M - 1) * s)) := by ring
  rw [heqLeft, heqRight] at hkey
  have hMpos : 0 < M := Fintype.card_pos_iff.mpr inferInstance
  exact Nat.le_of_mul_le_mul_left hkey hMpos

/-- Passing from varying cores to arbitrary common-size subcores preserves
the pair-intersection cap.  This is the exact justification for the
fixed-`Z` Johnson step. -/
theorem truncation_preserves_pair_cap
    {I U : Type*} [DecidableEq U]
    (D E : I → Finset U) (d : ℕ)
    (hsub : ∀ i, E i ⊆ D i)
    (hpair : ∀ i j, i ≠ j → (D i ∩ D j).card ≤ d)
    {i j : I} (hne : i ≠ j) :
    (E i ∩ E j).card ≤ d := by
  apply le_trans (Finset.card_le_card ?_) (hpair i j hne)
  exact Finset.inter_subset_inter (hsub i) (hsub j)

/-- The sharp Johnson inequality permits at most fifteen exceptional line
cores.  Parameters are `h=4q`, universe size `2h=8q`,
`Z=3h/4+2=3q+2`, and `d=h/4-1=q-1`. -/
theorem exceptional_family_card_le_fifteen
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    [Nonempty κ] (S : κ → Finset ι) (q : ℕ) (hq : 1 ≤ q)
    (hcard : Fintype.card ι = 8 * q)
    (hsize : ∀ i, (S i).card = 3 * q + 2)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ q - 1) :
    Fintype.card κ ≤ 15 := by
  have hsharp := sharp_johnson_of_lower_upper_pair S (3 * q + 2) (3 * q + 2)
    (q - 1) (fun i => (hsize i).ge) (fun i => (hsize i).le) hpair
  rw [hcard] at hsharp
  by_contra hnot
  have hM : 16 ≤ Fintype.card κ := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  simp only [Nat.succ_sub_one] at hsharp
  have hM0 : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  rw [hm] at hsharp hM
  simp only [Nat.succ_sub_one] at hsharp
  have hbound :
      (m + 1) * (((r + 1) ^ 2) + 20 * (r + 1) + 4) ≤
        16 * (r + 1) ^ 2 + 24 * (r + 1) := by
    nlinarith [hsharp]
  have hmul :
      16 * (((r + 1) ^ 2) + 20 * (r + 1) + 4) ≤
        (m + 1) * (((r + 1) ^ 2) + 20 * (r + 1) + 4) :=
    Nat.mul_le_mul_right _ hM
  have hcontra :
      16 * (r + 1) ^ 2 + 24 * (r + 1) <
        16 * (((r + 1) ^ 2) + 20 * (r + 1) + 4) := by
    nlinarith
  omega

/-- The same inequality permits at most three ultra-large cores.  Parameters
are `h=16q`, universe size `2h=32q`, `Z=15h/16=15q`, and
`d=h/4-1=4q-1`. -/
theorem ultra_family_card_le_three
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    [Nonempty κ] (S : κ → Finset ι) (q : ℕ) (hq : 1 ≤ q)
    (hcard : Fintype.card ι = 32 * q)
    (hsize : ∀ i, (S i).card = 15 * q)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 4 * q - 1) :
    Fintype.card κ ≤ 3 := by
  have hsharp := sharp_johnson_of_lower_upper_pair S (15 * q) (15 * q)
    (4 * q - 1) (fun i => (hsize i).ge) (fun i => (hsize i).le) hpair
  rw [hcard] at hsharp
  by_contra hnot
  have hM : 4 ≤ Fintype.card κ := by omega
  have hq0 : q ≠ 0 := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
  have hfour : 4 * (r + 1) - 1 = 4 * r + 3 := by omega
  rw [hfour] at hsharp
  have hM0 : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  rw [hm] at hsharp hM
  simp only [Nat.succ_sub_one] at hsharp
  have hbound :
      (m + 1) * (97 * (r + 1) ^ 2 + 32 * (r + 1)) ≤
        352 * (r + 1) ^ 2 + 32 * (r + 1) := by
    nlinarith [hsharp]
  have hmul :
      4 * (97 * (r + 1) ^ 2 + 32 * (r + 1)) ≤
        (m + 1) * (97 * (r + 1) ^ 2 + 32 * (r + 1)) :=
    Nat.mul_le_mul_right _ hM
  have hcontra :
      352 * (r + 1) ^ 2 + 32 * (r + 1) <
        4 * (97 * (r + 1) ^ 2 + 32 * (r + 1)) := by
    nlinarith
  omega

/-- A five-point line at half-predecessor agreement has core at least
`3h/4+2`.  Here `h=4q`. -/
theorem five_points_force_large_core
    {q z L : ℕ} (hz : z ≤ 4 * q)
    (hL : 5 ≤ L)
    (hpacking : L * (4 * q + 1 - z) + z ≤ 8 * q) :
    3 * q + 2 ≤ z := by
  have hsub : 4 * q + 1 - z + z = 4 * q + 1 :=
    Nat.sub_add_cancel (by omega)
  have hmul : 5 * (4 * q + 1 - z) ≤ L * (4 * q + 1 - z) :=
    Nat.mul_le_mul_right _ hL
  nlinarith

/-- If a line core is below `15h/16`, its packing line has at most sixteen
points.  Here `h=16q`. -/
theorem nonultra_line_card_le_sixteen
    {q z L : ℕ} (hz : z < 15 * q)
    (hpacking : L * (16 * q + 1 - z) + z ≤ 32 * q) :
    L ≤ 16 := by
  have hz' : z ≤ 16 * q + 1 := by omega
  have hsub : 16 * q + 1 - z + z = 16 * q + 1 :=
    Nat.sub_add_cancel hz'
  by_contra hnot
  have hL : 17 ≤ L := by omega
  have hmul : 17 * (16 * q + 1 - z) ≤ L * (16 * q + 1 - z) :=
    Nat.mul_le_mul_right _ hL
  nlinarith

/-- Under the global core ceiling `z<=h-4`, every line satisfies the
ultra-line size budget `5L<=h+4`. -/
theorem global_core_ceiling_line_budget
    {h z L : ℕ} (hz : z + 4 ≤ h)
    (hpacking : L * (h + 1 - z) + z ≤ 2 * h) :
    5 * L ≤ h + 4 := by
  by_cases hL0 : L = 0
  · simp [hL0]
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL0
  have hz' : z ≤ h + 1 := by omega
  have hsub : h + 1 - z + z = h + 1 := Nat.sub_add_cancel hz'
  have hfresh : 5 ≤ h + 1 - z := by omega
  have hLsplit : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hprod :
      L * (h + 1 - z) = (L - 1) * (h + 1 - z) + (h + 1 - z) := by
    calc
      L * (h + 1 - z) = ((L - 1) + 1) * (h + 1 - z) := by rw [hLsplit]
      _ = (L - 1) * (h + 1 - z) + (h + 1 - z) := by ring
  have hbase : (L - 1) * (h + 1 - z) ≤ h - 1 := by
    omega
  have hmul : 5 * (L - 1) ≤ (L - 1) * (h + 1 - z) := by
    nlinarith
  omega

/-- Numeric union budget for the pruning proof.  If there are at most
fifteen exceptional lines, at most three of them are ultra, ultra lines have
`5L<=h+4`, and ordinary exceptional lines have `L<=16`, then any union whose
fivefold size is bounded by the corresponding sum occupies at most `5h/7`
coordinates once `h>=1699`. -/
theorem exceptional_union_seven_mul_le_five_mul
    {h R u m : ℕ} (hh : 1699 ≤ h) (hu : u ≤ 3) (hum : u ≤ m)
    (hm : m ≤ 15)
    (hbudget : 5 * R ≤ u * (h + 4) + 5 * (m - u) * 16) :
    7 * R ≤ 5 * h := by
  have hh76 : 76 ≤ h := by omega
  have hhsplit : h - 76 + 76 = h := Nat.sub_add_cancel hh76
  have hmsplit : m - u + u = m := Nat.sub_add_cancel hum
  have hrearrange :
      u * (h + 4) + 5 * (m - u) * 16 = u * (h - 76) + 80 * m := by
    nlinarith
  have hultra : u * (h - 76) ≤ 3 * (h - 76) :=
    Nat.mul_le_mul_right _ hu
  have hord : 80 * m ≤ 80 * 15 := Nat.mul_le_mul_left 80 hm
  have hbound : 5 * R ≤ 3 * h + 972 := by
    rw [hrearrange] at hbudget
    nlinarith
  by_contra hnot
  have hstrict : 5 * h < 7 * R := by omega
  have hupper : h ≤ 1699 := by nlinarith
  have heq : h = 1699 := by omega
  subst h
  omega

/-- Removing a set of size at most `5h/7` from a counterexample of size at
least `2h+1` leaves strictly more than `9h/7` points. -/
theorem nine_mul_lt_seven_mul_pruned
    {h N R M : ℕ} (hN : 2 * h + 1 ≤ N) (hRN : R ≤ N)
    (hR : 7 * R ≤ 5 * h) (hM : M = N - R) :
    9 * h < 7 * M := by
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.pair_inter_le_of_union_floor
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.sharp_johnson_of_lower_upper_pair
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.truncation_preserves_pair_cap
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.exceptional_family_card_le_fifteen
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.ultra_family_card_le_three
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.five_points_force_large_core
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.nonultra_line_card_le_sixteen
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.exceptional_union_seven_mul_le_five_mul
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics.nine_mul_lt_seven_mul_pruned
