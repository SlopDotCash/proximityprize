/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetAugmentation
import Mathlib.Tactic.FinCases

/-!
# The `a = 8`, `n = 16` coset-structure check

Campaign #357. The depth-1 census probes found that every balanced 8-subset at `n = 16`
contains a full coset of the order-4 subgroup `{0, 4, 8, 12}`. Combined with the coset
augmentation law, this is the finite structural reason behind the measured
`census(8) = census(4)` duality at the first nontrivial scale.

This file promotes that probe verdict into a kernel-checked finite theorem. It is not the
general arbitrary-scale structure theorem; it is the exact `n = 16` base datum that the
general peeling argument should explain.

## References

* Issue #357; probe `probe_8set_coset_structure.py`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.WindowTwoLayer

open Multiset

/-- A computable canonical listing of the residues of `ZMod 16`. -/
def zmod16Universe : List (ZMod 16) :=
  (List.range 16).map fun i => (i : ZMod 16)

/-- Every residue appears in the canonical listing. -/
theorem mem_zmod16Universe (x : ZMod 16) : x ∈ zmod16Universe := by
  fin_cases x <;> decide

/-- The order-4 coset through `x` in `ZMod 16`. -/
def orderFourCoset16 (x : ZMod 16) : Finset (ZMod 16) :=
  {x, x + 4, x + 8, x + 12}

/-- An 8-subset of `ZMod 16` contains a full order-4 coset. -/
def ContainsOrderFourCoset16 (A : Finset (ZMod 16)) : Prop :=
  ∃ x : ZMod 16, orderFourCoset16 x ⊆ A

/-- Boolean balance check over the finite group `ZMod 16`. -/
def balanced16 (M : Multiset (ZMod 16)) : Bool :=
  zmod16Universe.all fun t =>
    decide (M.count t = M.count (t + ((8 : ℕ) : ZMod 16)))

/-- The Boolean checker is equivalent to the `Balanced` predicate at `n = 16`. -/
theorem balanced16_eq_true_iff (M : Multiset (ZMod 16)) :
    balanced16 M = true ↔ Balanced ((8 : ℕ) : ZMod 16) M := by
  unfold balanced16 Balanced
  rw [List.all_eq_true]
  constructor
  · intro h t
    exact of_decide_eq_true (h t (mem_zmod16Universe t))
  · intro h t _
    exact decide_eq_true (h t)

/-- Boolean check for whether a subset contains a full order-4 coset. -/
def containsOrderFourCoset16Bool (A : Finset (ZMod 16)) : Bool :=
  zmod16Universe.any fun x =>
    decide (orderFourCoset16 x ⊆ A)

/-- The Boolean coset checker is equivalent to the Prop-level statement. -/
theorem containsOrderFourCoset16Bool_eq_true_iff (A : Finset (ZMod 16)) :
    containsOrderFourCoset16Bool A = true ↔ ContainsOrderFourCoset16 A := by
  unfold containsOrderFourCoset16Bool ContainsOrderFourCoset16
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, _hx, hsub⟩
    exact ⟨x, of_decide_eq_true hsub⟩
  · rintro ⟨x, hsub⟩
    exact ⟨x, mem_zmod16Universe x, decide_eq_true hsub⟩

/-- The general coset-augmentation law specialized to the order-4 cosets in `ZMod 16`. -/
theorem balanced_pairSums_orderFourCoset16_augment (x : ZMod 16) (A : Multiset (ZMod 16)) :
    Balanced ((8 : ℕ) : ZMod 16)
        (pairSums (x ::ₘ (x + 4) ::ₘ (x + 8) ::ₘ (x + 12) ::ₘ A)) ↔
      Balanced ((8 : ℕ) : ZMod 16) (pairSums A) := by
  convert balanced_pairSums_coset_augment (R := ZMod 16) (h := ((8 : ℕ) : ZMod 16))
    (q := ((4 : ℕ) : ZMod 16)) (by decide) (by decide) x A using 1
  ring_nf

/-- A single order-4 coset has balanced pair sums at half-period `8`. -/
theorem balanced_pairSums_orderFourCoset16 (x : ZMod 16) :
    Balanced ((8 : ℕ) : ZMod 16)
      (pairSums ({x, x + 4, x + 8, x + 12} : Multiset (ZMod 16))) := by
  have h := (balanced_pairSums_orderFourCoset16_augment x 0).mpr ?_
  · simpa using h
  · intro t
    unfold pairSums
    simp

/-- The canonical computable list of 8-subsets of `ZMod 16`. -/
def zmod16Subsets8 : List (Finset (ZMod 16)) :=
  (zmod16Universe.sublists.filter (fun xs => xs.length = 8)).map List.toFinset

/-- The balanced members of the canonical 8-subset enumeration. -/
def balancedEightSubsets16 : List (Finset (ZMod 16)) :=
  zmod16Subsets8.filter fun A => balanced16 (pairSums A.val)

/-- Finite checked form: every balanced member of the canonical 8-subset enumeration
contains a full order-4 coset, and there are exactly the probe-predicted `70` of them. -/
def balancedEightCosetCheck16 : Bool :=
  let xs := balancedEightSubsets16
  (xs.length == 70) && xs.all fun A => containsOrderFourCoset16Bool A

-- Summarize consecutive batches without constructing one large reduction proof.
private def a8Summary (xs : List (Finset (ZMod 16))) : ℕ × Bool :=
  let bs := xs.filter fun A => balanced16 (pairSums A.val)
  (bs.length, bs.all containsOrderFourCoset16Bool)

private def a8Combine (a b : ℕ × Bool) : ℕ × Bool :=
  (a.1 + b.1, a.2 && b.2)

private theorem a8Summary_append (xs ys : List (Finset (ZMod 16))) :
    a8Summary (xs ++ ys) = a8Combine (a8Summary xs) (a8Summary ys) := by
  simp [a8Summary, a8Combine, List.filter_append, List.all_append]

private theorem a8Summary_split (xs : List (Finset (ZMod 16))) :
    a8Summary xs = a8Combine (a8Summary (xs.take 1024)) (a8Summary (xs.drop 1024)) := by
  rw [← a8Summary_append, List.take_append_drop]

private def a8Chunk (j : ℕ) : ℕ × Bool :=
  a8Summary ((zmod16Subsets8.drop (j * 1024)).take 1024)

private theorem a8Summary_check (xs : List (Finset (ZMod 16))) (n : ℕ)
    (h : a8Summary xs = (n, true)) :
    (let bs := xs.filter fun A => balanced16 (pairSums A.val)
     (bs.length == n) && bs.all containsOrderFourCoset16Bool) = true := by
  have hlen : (xs.filter fun A => balanced16 (pairSums A.val)).length = n :=
    congrArg Prod.fst h
  have hall : (xs.filter fun A => balanced16 (pairSums A.val)).all
      containsOrderFourCoset16Bool = true := congrArg Prod.snd h
  change (((xs.filter fun A => balanced16 (pairSums A.val)).length == n) &&
    (xs.filter fun A => balanced16 (pairSums A.val)).all containsOrderFourCoset16Bool) = true
  simp only [hlen, hall, beq_self_eq_true, Bool.true_and]

private theorem a8Summary_glue (xs : List (Finset (ZMod 16))) (a b : ℕ)
    (ha : a8Summary (xs.take 1024) = (a, true))
    (hb : a8Summary (xs.drop 1024) = (b, true)) :
    a8Summary xs = (a + b, true) := by
  simpa only [ha, hb, a8Combine] using a8Summary_split xs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk0 : a8Chunk 0 = (3, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk1 : a8Chunk 1 = (5, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk2 : a8Chunk 2 = (7, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk3 : a8Chunk 3 = (9, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk4 : a8Chunk 4 = (6, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk5 : a8Chunk 5 = (4, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk6 : a8Chunk 6 = (4, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk7 : a8Chunk 7 = (8, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk8 : a8Chunk 8 = (7, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk9 : a8Chunk 9 = (4, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk10 : a8Chunk 10 = (6, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk11 : a8Chunk 11 = (5, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Chunk12 : a8Chunk 12 = (2, true) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem a8Tail13 : a8Summary (zmod16Subsets8.drop 13312) = (0, true) := by
  decide +kernel

private theorem a8Tail12 : a8Summary (zmod16Subsets8.drop 12288) = (2, true) := by
  apply a8Summary_glue _ 2 0
  · exact a8Chunk12
  · simpa only [List.drop_drop] using a8Tail13

private theorem a8Tail11 : a8Summary (zmod16Subsets8.drop 11264) = (7, true) := by
  apply a8Summary_glue _ 5 2
  · exact a8Chunk11
  · simpa only [List.drop_drop] using a8Tail12

private theorem a8Tail10 : a8Summary (zmod16Subsets8.drop 10240) = (13, true) := by
  apply a8Summary_glue _ 6 7
  · exact a8Chunk10
  · simpa only [List.drop_drop] using a8Tail11

private theorem a8Tail9 : a8Summary (zmod16Subsets8.drop 9216) = (17, true) := by
  apply a8Summary_glue _ 4 13
  · exact a8Chunk9
  · simpa only [List.drop_drop] using a8Tail10

private theorem a8Tail8 : a8Summary (zmod16Subsets8.drop 8192) = (24, true) := by
  apply a8Summary_glue _ 7 17
  · exact a8Chunk8
  · simpa only [List.drop_drop] using a8Tail9

private theorem a8Tail7 : a8Summary (zmod16Subsets8.drop 7168) = (32, true) := by
  apply a8Summary_glue _ 8 24
  · exact a8Chunk7
  · simpa only [List.drop_drop] using a8Tail8

private theorem a8Tail6 : a8Summary (zmod16Subsets8.drop 6144) = (36, true) := by
  apply a8Summary_glue _ 4 32
  · exact a8Chunk6
  · simpa only [List.drop_drop] using a8Tail7

private theorem a8Tail5 : a8Summary (zmod16Subsets8.drop 5120) = (40, true) := by
  apply a8Summary_glue _ 4 36
  · exact a8Chunk5
  · simpa only [List.drop_drop] using a8Tail6

private theorem a8Tail4 : a8Summary (zmod16Subsets8.drop 4096) = (46, true) := by
  apply a8Summary_glue _ 6 40
  · exact a8Chunk4
  · simpa only [List.drop_drop] using a8Tail5

private theorem a8Tail3 : a8Summary (zmod16Subsets8.drop 3072) = (55, true) := by
  apply a8Summary_glue _ 9 46
  · exact a8Chunk3
  · simpa only [List.drop_drop] using a8Tail4

private theorem a8Tail2 : a8Summary (zmod16Subsets8.drop 2048) = (62, true) := by
  apply a8Summary_glue _ 7 55
  · exact a8Chunk2
  · simpa only [List.drop_drop] using a8Tail3

private theorem a8Tail1 : a8Summary (zmod16Subsets8.drop 1024) = (67, true) := by
  apply a8Summary_glue _ 5 62
  · exact a8Chunk1
  · simpa only [List.drop_drop] using a8Tail2

private theorem a8Tail0 : a8Summary (zmod16Subsets8.drop 0) = (70, true) := by
  apply a8Summary_glue _ 3 67
  · exact a8Chunk0
  · simpa only [List.drop_drop] using a8Tail1

-- Each batch is checked separately by the kernel to bound peak reduction memory.
theorem balancedEightCosetCheck16_eq_true : balancedEightCosetCheck16 = true := by
  have h : a8Summary zmod16Subsets8 = (70, true) := by
    simpa only [List.drop_zero] using a8Tail0
  exact a8Summary_check zmod16Subsets8 70 h

/-- The probe's `70` balanced 8-sets are exactly the balanced members of this enumeration. -/
theorem balancedEightSubsets16_length : balancedEightSubsets16.length = 70 := by
  have h := balancedEightCosetCheck16_eq_true
  unfold balancedEightCosetCheck16 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- **The `a = 8`, `n = 16` coset-structure theorem, finite-list form.** Every member of
the canonical 8-subset enumeration with antipodally balanced pair sums contains a full
coset of the order-4 subgroup. -/
theorem balanced_eight_contains_orderFourCoset_zmod16 :
    ∀ A ∈ zmod16Subsets8,
      Balanced ((8 : ℕ) : ZMod 16) (pairSums A.val) → ContainsOrderFourCoset16 A := by
  intro A hA hbal
  have hall := balancedEightCosetCheck16_eq_true
  unfold balancedEightCosetCheck16 at hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  have hallAll := hall.2
  rw [List.all_eq_true] at hallAll
  have hA' : A ∈ balancedEightSubsets16 := by
    simp [balancedEightSubsets16, hA, (balanced16_eq_true_iff (pairSums A.val)).mpr hbal]
  exact (containsOrderFourCoset16Bool_eq_true_iff A).mp (hallAll A hA')

/-! ## Source audit -/

#print axioms balanced_eight_contains_orderFourCoset_zmod16
#print axioms balanced_pairSums_orderFourCoset16_augment
#print axioms balanced_pairSums_orderFourCoset16

end ArkLib.ProximityGap.WindowTwoLayer
