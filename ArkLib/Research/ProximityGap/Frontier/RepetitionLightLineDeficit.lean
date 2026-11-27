/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.WeightedRichLinePacking
import ArkLib.Research.ProximityGap.Frontier.AgreementSlicePacking

/-! # Light-point excess in a weighted rich-line arrangement -/
set_option autoImplicit false
open Finset
namespace ArkLib.ProximityGap.Frontier.WeightedRichLinePacking.Arrangement

variable {P J : Type} [DecidableEq P] [DecidableEq J] {t : ℕ} (A : Arrangement P J t)

/-- Each unweighted incidence beyond the union can be charged to a pair of lines. -/
theorem incidence_le_union_add_pairs (G : Finset J) (sub : G ⊆ A.lines) :
    (∑ j ∈ G, (A.block j).card) ≤ (G.biUnion A.block).card + G.card.choose 2 := by
  induction G using Finset.induction_on with
  | empty => simp
  | @insert j G hj ih =>
    have old : G ⊆ A.lines := (subset_insert j G).trans sub
    have row (i) (hi : i ∈ G) : (A.block j ∩ A.block i).card ≤ 1 :=
      A.linear j (sub (mem_insert_self ..)) i (old hi) (fun eq => hj (eq ▸ hi))
    have union : A.block j ∩ G.biUnion A.block = G.biUnion (fun i => A.block j ∩ A.block i) := by
      ext x
      simp only [mem_inter, mem_biUnion]
      grind
    have overlap : (A.block j ∩ G.biUnion A.block).card ≤ G.card := by
      rw [union]
      exact card_biUnion_le.trans (by simpa using sum_le_sum (s := G) (fun i hi => row i hi))
    have split := card_union_add_card_inter (A.block j) (G.biUnion A.block)
    rw [sum_insert hj, biUnion_insert, card_insert_of_notMem hj, Nat.choose_succ_succ,
      Nat.choose_one_right]
    change (A.block j).card + _ ≤ _ + (G.card + G.card.choose 2)
    have smaller := ih old
    omega

omit [DecidableEq J] in
private theorem mass_eq_card_add_excess (T : Finset P) (sub : T ⊆ A.points) :
    mass A.w T = T.card + ∑ x ∈ T, (A.w x-1) := by
  have each (x) (hx : x ∈ T) : A.w x = 1 + (A.w x-1) := by have := A.positive x (sub hx); omega
  change (∑ x ∈ T, A.w x) = _
  rw [sum_congr rfl each, sum_add_distrib]
  simp

/-- Let `L` bound the light mass and `D=L-#Q` for the distinct light points.
For a chosen subfamily of light-only lines, each unit of excess can be counted
once per line, while unweighted repetitions cost at most one per pair. -/
theorem light_deficit_bound (H : Finset P) (G : Finset J) (inside : G ⊆ A.away H)
    (L : ℕ) (large : mass A.w (A.points \ H) ≤ L) :
    G.card*t ≤ L + G.card.choose 2 + (G.card-1)*(L-(A.points \ H).card) := by
  classical
  rcases G.eq_empty_or_nonempty with he | hn
  · simp [he]
  let Q := A.points \ H
  let D := L-Q.card
  have subG : G ⊆ A.lines := inside.trans (filter_subset _ _)
  have light (j) (hj : j ∈ G) : A.block j ⊆ Q := fun _ hx =>
    mem_sdiff.mpr ⟨A.inside _ (subG hj) hx, disjoint_left.mp (mem_filter.mp (inside hj)).2 hx⟩
  have decomp := A.mass_eq_card_add_excess Q sdiff_subset
  have cap : (∑ x ∈ Q, (A.w x-1)) ≤ D := by
    dsimp [D]
    change mass A.w Q ≤ L at large
    omega
  have total (j) (hj : j ∈ G) : t ≤ (A.block j).card + D := by
    have w := A.rich j (subG hj)
    rw [A.mass_eq_card_add_excess _ (A.inside j (subG hj))] at w
    exact w.trans (Nat.add_le_add_left ((sum_le_sum_of_subset (light j hj)).trans cap) _)
  have add : G.card*t ≤ (∑ j ∈ G, (A.block j).card) + G.card*D := by
    simpa only [sum_const, smul_eq_mul, sum_add_distrib] using sum_le_sum (s := G) total
  have all := A.incidence_le_union_add_pairs G subG
  have uni := card_le_card (biUnion_subset.mpr light)
  have eq : Q.card + D = L := Nat.add_sub_of_le (by
    change mass A.w Q ≤ L at large
    omega)
  have mul : (G.card-1)*D + D = G.card*D := by
    rw [← Nat.succ_mul]
    exact congrArg (· * D) (by have := card_pos.mpr hn; omega)
  change G.card*t ≤ L + G.card.choose 2 + (G.card-1)*D
  omega

omit [DecidableEq J] in
/-- When light-point excess is small, the lines have many distinct light points.
Their dual second moment bounds the actual number of light-only rich lines. -/
theorem light_pair_moment (H : Finset P) (G : Finset J) (inside : G ⊆ A.away H)
    (D T : ℕ) (extra : mass A.w (A.points \ H) ≤ (A.points \ H).card + D) (needed : T+D ≤ t) :
    G.card * T^2 ≤ (A.points \ H).card * (T + (G.card-1)) := by
  classical
  let Q := A.points \ H
  have subG : G ⊆ A.lines := inside.trans (filter_subset _ _)
  have light (j) (hj : j ∈ G) : A.block j ⊆ Q := fun _ hx =>
    mem_sdiff.mpr ⟨A.inside _ (subG hj) hx, disjoint_left.mp (mem_filter.mp (inside hj)).2 hx⟩
  have excess := A.mass_eq_card_add_excess Q sdiff_subset
  have cap : (∑ x ∈ Q, (A.w x-1)) ≤ D := by
    change mass A.w Q ≤ Q.card + D at extra
    omega
  let supp (j : ↥G) := (A.block j.val).subtype (fun x => x ∈ Q)
  have enough (j : ↥G) : T ≤ (supp j).card := by
    have rich := A.rich _ (subG j.property)
    have sum := A.mass_eq_card_add_excess (A.block j.val) (A.inside _ (subG j.property))
    have le := (sum_le_sum_of_subset (light _ j.property)).trans cap
    have eq : (supp j).card = (A.block j.val).card := by
      dsimp only [supp]
      rw [card_subtype]
      exact congrArg card (filter_eq_self.mpr (fun x hx => light _ j.property hx))
    omega
  choose S sub size using fun j => exists_subset_card_eq (enough j)
  have pair (i j : ↥G) (ne : i ≠ j) : (S i ∩ S j).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    apply Subtype.ext
    have mem (a b : ↥G) (z : ↥Q) (hz : z ∈ S a ∩ S b) :
        z.val ∈ A.block a.val ∩ A.block b.val :=
      mem_inter.mpr ⟨mem_subtype.mp (sub _ (mem_inter.mp hz).1),
        mem_subtype.mp (sub _ (mem_inter.mp hz).2)⟩
    exact card_le_one.mp (A.linear i.val (subG i.property) j.val (subG j.property)
      (fun he => ne (Subtype.ext he))) _ (mem i j x hx) _ (mem i j y hy)
  have h := _root_.ProximityGap.AgreementSlicePacking.plotkin (univ : Finset ↥G) S T 1
    (fun j _ => size j) (fun i _ j _ => pair i j)
  simpa only [card_univ, Fintype.card_coe, Nat.mul_one] using h

#print axioms light_deficit_bound
#print axioms light_pair_moment
end ArkLib.ProximityGap.Frontier.WeightedRichLinePacking.Arrangement
