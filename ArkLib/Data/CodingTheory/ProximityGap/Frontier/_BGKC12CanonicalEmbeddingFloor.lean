/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKC12TranslateIntersectionReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R348PeriodSquareRecursion

/-!
# A canonical adjacent-subset witness inside the late Newton `C12` row

For a marked pair `(x,y)` in a multiplicative subgroup containing `-1`, the identity

`2*y-x = (y+(-x))-(-y)`

puts its marked difference into the adjacent subset-difference row.  At adjacent ranks `k+2`
and `k+1`, one may add the same `k`-subset `C` to both sides, provided `C` avoids
`{y,-x,-y}`.  This file makes that construction collision-free and proves the exact support
floor

`choose(|G \ {y,-x,-y}|, k) <= R_{k+2}(2*y-x)`.

If the field has odd characteristic and `(x,y)` is good (`x != y` and `x != -y`), the three
forbidden labels are distinct, so the left side is `choose(|G|-3,k)`.  The injection is recovered
from the lower subset by erasing `-y`; no unproved recovery-multiplicity assertion is used.

This is a genuine support inclusion, but it is only a local floor.  It does not assert the much
larger production-scale alignment needed for the fifth and sixth Newton gates.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKC12CanonicalEmbeddingFloor

open ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance
open ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction
open ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion

section CanonicalEmbedding

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The labelled copy of a finite subset of the field. -/
abbrev SubgroupPoint (G : Finset F) := {a : F // a ∈ G}

/-- Negation preserves a multiplicative subgroup when `-1` belongs to it. -/
def negPoint (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (x : SubgroupPoint G) : SubgroupPoint G :=
  ⟨-x.1, by
    simpa using hG.mul_mem (-1) hnegOne x.1 x.2⟩

@[simp] theorem negPoint_val (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (x : SubgroupPoint G) :
    (negPoint G hG hnegOne x).1 = -x.1 := rfl

/-- The two marked-point exclusions used by the canonical embedding. -/
def IsGoodMarkedPair (G : Finset F) (z : MarkedPair G) : Prop :=
  z.1.1 ≠ z.2.1 ∧ z.1.1 ≠ -z.2.1

/-- The three labels which cannot be used by the common core. -/
def canonicalForbidden (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) : Finset (SubgroupPoint G) :=
  {z.2, negPoint G hG hnegOne z.1, negPoint G hG hnegOne z.2}

/-- Labels available for the common core. -/
def canonicalAvailable (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) : Finset (SubgroupPoint G) :=
  Finset.univ \ canonicalForbidden G hG hnegOne z

/-- A fixed-cardinality common core avoiding all three marked labels. -/
abbrev CanonicalCore (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat) :=
  {C : Finset (SubgroupPoint G) //
    C ∈ (canonicalAvailable G hG hnegOne z).powersetCard k}

theorem canonicalCore_card (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) : C.1.card = k :=
  (Finset.mem_powersetCard.mp C.2).2

theorem canonicalCore_not_mem_forbidden (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) {a : SubgroupPoint G}
    (ha : a ∈ canonicalForbidden G hG hnegOne z) : a ∉ C.1 := by
  intro haC
  have hsub := (Finset.mem_powersetCard.mp C.2).1 haC
  exact (Finset.mem_sdiff.mp hsub).2 ha

theorem second_ne_neg_first_of_good (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (hz : IsGoodMarkedPair G z) :
    z.2 ≠ negPoint G hG hnegOne z.1 := by
  intro h
  apply hz.2
  have hv := congrArg Subtype.val h
  change z.2.1 = -z.1.1 at hv
  linear_combination hv

/-- The upper `(k+2)`-subset `C union {y,-x}`. -/
def canonicalUpper (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) : Finset (SubgroupPoint G) :=
  insert z.2 (insert (negPoint G hG hnegOne z.1) C.1)

/-- The lower `(k+1)`-subset `C union {-y}`. -/
def canonicalLower (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) : Finset (SubgroupPoint G) :=
  insert (negPoint G hG hnegOne z.2) C.1

theorem neg_first_not_mem_core (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) :
    negPoint G hG hnegOne z.1 ∉ C.1 := by
  apply canonicalCore_not_mem_forbidden G hG hnegOne z k C
  simp [canonicalForbidden]

theorem second_not_mem_core (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) : z.2 ∉ C.1 := by
  apply canonicalCore_not_mem_forbidden G hG hnegOne z k C
  simp [canonicalForbidden]

theorem neg_second_not_mem_core (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) :
    negPoint G hG hnegOne z.2 ∉ C.1 := by
  apply canonicalCore_not_mem_forbidden G hG hnegOne z k C
  simp [canonicalForbidden]

theorem canonicalUpper_card (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (hz : IsGoodMarkedPair G z)
    (k : Nat) (C : CanonicalCore G hG hnegOne z k) :
    (canonicalUpper G hG hnegOne z k C).card = k + 2 := by
  classical
  have hnegC := neg_first_not_mem_core G hG hnegOne z k C
  have hyC := second_not_mem_core G hG hnegOne z k C
  have hyNeg := second_ne_neg_first_of_good G hG hnegOne z hz
  have hyInsert : z.2 ∉ insert (negPoint G hG hnegOne z.1) C.1 := by
    simp [hyNeg, hyC]
  rw [canonicalUpper, Finset.card_insert_of_notMem hyInsert,
    Finset.card_insert_of_notMem hnegC, canonicalCore_card]

theorem canonicalLower_card (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat)
    (C : CanonicalCore G hG hnegOne z k) :
    (canonicalLower G hG hnegOne z k C).card = k + 1 := by
  classical
  rw [canonicalLower, Finset.card_insert_of_notMem
    (neg_second_not_mem_core G hG hnegOne z k C), canonicalCore_card]

/-- The canonical adjacent-subset pair built from one marked pair and one avoiding core. -/
noncomputable def canonicalAdjacentWitness (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (hz : IsGoodMarkedPair G z)
    (k : Nat) (C : CanonicalCore G hG hnegOne z k) : AdjacentSubsetPair G (k + 2) :=
  (⟨canonicalUpper G hG hnegOne z k C,
      Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, canonicalUpper_card G hG hnegOne z hz k C⟩⟩,
    ⟨canonicalLower G hG hnegOne z k C,
      Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, by
          simpa using canonicalLower_card G hG hnegOne z k C⟩⟩)

/-- The common core cancels exactly, leaving `2*y-x`. -/
theorem canonicalAdjacentWitness_phase (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (hz : IsGoodMarkedPair G z)
    (k : Nat) (C : CanonicalCore G hG hnegOne z k) :
    subsetDifferencePhase G (k + 2) (canonicalAdjacentWitness G hG hnegOne z hz k C) =
      markedDifferencePhase G z := by
  classical
  have hnegC := neg_first_not_mem_core G hG hnegOne z k C
  have hyC := second_not_mem_core G hG hnegOne z k C
  have hyNeg := second_ne_neg_first_of_good G hG hnegOne z hz
  have hyInsert : z.2 ∉ insert (negPoint G hG hnegOne z.1) C.1 := by
    simp [hyNeg, hyC]
  have hnegyC := neg_second_not_mem_core G hG hnegOne z k C
  change
    (∑ a ∈ canonicalUpper G hG hnegOne z k C, a.1) -
        ∑ a ∈ canonicalLower G hG hnegOne z k C, a.1 =
      2 * z.2.1 - z.1.1
  rw [canonicalUpper, canonicalLower, Finset.sum_insert hyInsert,
    Finset.sum_insert hnegC, Finset.sum_insert hnegyC]
  simp only [negPoint_val]
  ring

/-- For a fixed marked pair, the lower subset recovers the common core by erasing `-y`. -/
theorem canonicalAdjacentWitness_injective (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (hz : IsGoodMarkedPair G z)
    (k : Nat) : Function.Injective (canonicalAdjacentWitness G hG hnegOne z hz k) := by
  classical
  intro C D hCD
  apply Subtype.ext
  have hlower := congrArg (fun p : AdjacentSubsetPair G (k + 2) => p.2.1) hCD
  change canonicalLower G hG hnegOne z k C =
    canonicalLower G hG hnegOne z k D at hlower
  have herase := congrArg (fun S => S.erase (negPoint G hG hnegOne z.2)) hlower
  simpa [canonicalLower, neg_second_not_mem_core G hG hnegOne z k C,
    neg_second_not_mem_core G hG hnegOne z k D] using herase

/-- The actual fibre of the adjacent subset-difference phase. -/
abbrev DifferenceFiber (G : Finset F) (r : Nat) (t : F) :=
  {p : AdjacentSubsetPair G r // subsetDifferencePhase G r p = t}

/-- The canonical construction, now packaged as a map into the correct physical fibre. -/
noncomputable def canonicalFiberWitness (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (hz : IsGoodMarkedPair G z)
    (k : Nat) (C : CanonicalCore G hG hnegOne z k) :
    DifferenceFiber G (k + 2) (markedDifferencePhase G z) :=
  ⟨canonicalAdjacentWitness G hG hnegOne z hz k C,
    canonicalAdjacentWitness_phase G hG hnegOne z hz k C⟩

theorem canonicalFiberWitness_injective (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (hz : IsGoodMarkedPair G z)
    (k : Nat) : Function.Injective (canonicalFiberWitness G hG hnegOne z hz k) := by
  intro C D h
  apply canonicalAdjacentWitness_injective G hG hnegOne z hz k
  exact congrArg Subtype.val h

theorem card_canonicalCore (G : Finset F) (hG : IsMulSubgroup G)
    (hnegOne : (-1 : F) ∈ G) (z : MarkedPair G) (k : Nat) :
    Fintype.card (CanonicalCore G hG hnegOne z k) =
      (canonicalAvailable G hG hnegOne z).card.choose k := by
  simp only [CanonicalCore, Fintype.card_coe, Finset.card_powersetCard]

theorem card_differenceFiber_eq_subsetDifferenceMultiplicity (G : Finset F)
    (r : Nat) (t : F) :
    Fintype.card (DifferenceFiber G r t) = subsetDifferenceMultiplicity G r t := by
  classical
  simp only [DifferenceFiber, subsetDifferenceMultiplicity, phaseFiberCount,
    Fintype.card_subtype]

/-- **Exact local support floor.**  Every avoiding common core produces a different point of the
adjacent subset-difference fibre over `2*y-x`. -/
theorem canonicalAvailable_choose_le_subsetDifferenceMultiplicity
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (z : MarkedPair G) (hz : IsGoodMarkedPair G z) (k : Nat) :
    (canonicalAvailable G hG hnegOne z).card.choose k ≤
      subsetDifferenceMultiplicity G (k + 2) (markedDifferencePhase G z) := by
  rw [← card_canonicalCore G hG hnegOne z k,
    ← card_differenceFiber_eq_subsetDifferenceMultiplicity G (k + 2)
      (markedDifferencePhase G z)]
  exact Fintype.card_le_of_injective _
    (canonicalFiberWitness_injective G hG hnegOne z hz k)

/-! ## The odd-characteristic `|G|-3` specialization -/

/-- Every member of a finite multiplicative subgroup of a field is nonzero. -/
theorem subgroupPoint_ne_zero (G : Finset F) (hG : IsMulSubgroup G)
    (x : SubgroupPoint G) : x.1 ≠ 0 := by
  obtain ⟨xi, _hxi, hxxi⟩ := hG.exists_inv x.1 x.2
  intro hx0
  rw [hx0, zero_mul] at hxxi
  exact zero_ne_one hxxi

theorem second_ne_neg_second_of_two_ne_zero
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (z : MarkedPair G) :
    z.2 ≠ negPoint G hG hnegOne z.2 := by
  intro h
  have hv := congrArg Subtype.val h
  change z.2.1 = -z.2.1 at hv
  have hprod : (2 : F) * z.2.1 = 0 := by
    linear_combination hv
  rcases mul_eq_zero.mp hprod with h2 | hy
  · exact htwo h2
  · exact subgroupPoint_ne_zero G hG z.2 hy

theorem neg_first_ne_neg_second_of_good
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (z : MarkedPair G) (hz : IsGoodMarkedPair G z) :
    negPoint G hG hnegOne z.1 ≠ negPoint G hG hnegOne z.2 := by
  intro h
  apply hz.1
  have hv := congrArg Subtype.val h
  change -z.1.1 = -z.2.1 at hv
  exact neg_injective hv

/-- In odd characteristic, goodness makes the three forbidden labels pairwise distinct. -/
theorem card_canonicalForbidden_of_good
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (z : MarkedPair G) (hz : IsGoodMarkedPair G z) :
    (canonicalForbidden G hG hnegOne z).card = 3 := by
  classical
  have hyNegX := second_ne_neg_first_of_good G hG hnegOne z hz
  have hyNegY := second_ne_neg_second_of_two_ne_zero G hG hnegOne htwo z
  have hNegXNegY := neg_first_ne_neg_second_of_good G hG hnegOne z hz
  simp [canonicalForbidden, hyNegX, hyNegY, hNegXNegY]

/-- Hence the common-core reservoir has exactly `|G|-3` labels. -/
theorem card_canonicalAvailable_of_good
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (z : MarkedPair G) (hz : IsGoodMarkedPair G z) :
    (canonicalAvailable G hG hnegOne z).card = G.card - 3 := by
  rw [canonicalAvailable, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_coe, card_canonicalForbidden_of_good G hG hnegOne htwo z hz]

/-- A phase lies in the good marked support if it is represented by some non-diagonal,
non-antipodal marked pair. -/
def InGoodMarkedDifferenceSupport (G : Finset F) (t : F) : Prop :=
  ∃ z : MarkedPair G, IsGoodMarkedPair G z ∧ markedDifferencePhase G z = t

/-- Number of good marked pairs in one marked-difference fibre. -/
noncomputable def goodMarkedDifferenceMultiplicity (G : Finset F) (t : F) : Nat := by
    classical
    exact (Finset.univ.filter fun z : MarkedPair G =>
      IsGoodMarkedPair G z ∧ markedDifferencePhase G z = t).card

/-- Total number of good ordered marked pairs. -/
noncomputable def goodMarkedPairCount (G : Finset F) : Nat := by
    classical
    exact (Finset.univ.filter fun z : MarkedPair G => IsGoodMarkedPair G z).card

/-- A good fibre is a literal sub-fibre of the full marked row. -/
theorem goodMarkedDifferenceMultiplicity_le_markedDifferenceMultiplicity
    (G : Finset F) (t : F) :
    goodMarkedDifferenceMultiplicity G t ≤ markedDifferenceMultiplicity G t := by
  classical
  unfold goodMarkedDifferenceMultiplicity markedDifferenceMultiplicity phaseFiberCount
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact hz.2

/-- Positivity of the restricted fibre is exactly membership in the good marked support. -/
theorem goodMarkedDifferenceMultiplicity_pos_iff_goodSupport
    (G : Finset F) (t : F) :
    0 < goodMarkedDifferenceMultiplicity G t ↔ InGoodMarkedDifferenceSupport G t := by
  classical
  unfold goodMarkedDifferenceMultiplicity InGoodMarkedDifferenceSupport
  rw [Finset.card_pos]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa using hz⟩

/-- The restricted fibres partition the set of good marked pairs exactly. -/
theorem sum_goodMarkedDifferenceMultiplicity (G : Finset F) :
    ∑ t : F, goodMarkedDifferenceMultiplicity G t = goodMarkedPairCount G := by
  classical
  unfold goodMarkedDifferenceMultiplicity goodMarkedPairCount
  calc
    (∑ t : F, (Finset.univ.filter fun z : MarkedPair G =>
        IsGoodMarkedPair G z ∧ markedDifferencePhase G z = t).card) =
        ∑ t : F, ∑ z : MarkedPair G,
          if IsGoodMarkedPair G z ∧ markedDifferencePhase G z = t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.card_filter]
    _ = ∑ z : MarkedPair G, ∑ t : F,
          if IsGoodMarkedPair G z ∧ markedDifferencePhase G z = t then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z : MarkedPair G, if IsGoodMarkedPair G z then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hgood : IsGoodMarkedPair G z
      · simp [hgood]
      · simp [hgood]
    _ = (Finset.univ.filter fun z : MarkedPair G => IsGoodMarkedPair G z).card := by
      rw [Finset.card_filter]

/-! ### Exact mass of the good marked sector -/

/-- Goodness may equivalently be tested by deleting `x` and `-x` from the second coordinate. -/
theorem isGoodMarkedPair_iff_second_avoids_first_and_negFirst
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (z : MarkedPair G) :
    IsGoodMarkedPair G z ↔
      z.2 ≠ z.1 ∧ z.2 ≠ negPoint G hG hnegOne z.1 := by
  constructor
  · rintro ⟨hxy, hxNegY⟩
    constructor
    · intro hyx
      apply hxy
      exact congrArg Subtype.val hyx.symm
    · intro hyNegX
      apply hxNegY
      have hv := congrArg Subtype.val hyNegX
      change z.2.1 = -z.1.1 at hv
      linear_combination hv
  · rintro ⟨hyx, hyNegX⟩
    constructor
    · intro hxy
      apply hyx
      apply Subtype.ext
      exact hxy.symm
    · intro hxNegY
      apply hyNegX
      apply Subtype.ext
      change z.2.1 = -z.1.1
      linear_combination hxNegY

/-- In odd characteristic, exactly `|G|-2` second coordinates make a fixed first coordinate
good: all subgroup points except `x` and `-x`. -/
theorem card_good_second_coordinates
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (x : SubgroupPoint G) :
    (Finset.univ.filter fun y : SubgroupPoint G =>
      y ≠ x ∧ y ≠ negPoint G hG hnegOne x).card = G.card - 2 := by
  classical
  have hxNeg : x ≠ negPoint G hG hnegOne x :=
    second_ne_neg_second_of_two_ne_zero G hG hnegOne htwo (x, x)
  have hset :
      (Finset.univ.filter fun y : SubgroupPoint G =>
        y ≠ x ∧ y ≠ negPoint G hG hnegOne x) =
        (Finset.univ.erase x).erase (negPoint G hG hnegOne x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [hset]
  have hnegMem : negPoint G hG hnegOne x ∈ (Finset.univ.erase x) :=
    Finset.mem_erase.mpr ⟨Ne.symm hxNeg, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem hnegMem,
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_coe]
  omega

/-- The good ordered marked-pair mass is exactly `|G|*(|G|-2)`. -/
theorem goodMarkedPairCount_eq_card_mul_card_sub_two
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) :
    goodMarkedPairCount G = G.card * (G.card - 2) := by
  classical
  unfold goodMarkedPairCount
  rw [Finset.card_filter]
  calc
    (∑ z : MarkedPair G, if IsGoodMarkedPair G z then 1 else 0) =
        ∑ x : SubgroupPoint G, ∑ y : SubgroupPoint G,
          if IsGoodMarkedPair G (x, y) then 1 else 0 := by
      exact Fintype.sum_prod_type _
    _ = ∑ x : SubgroupPoint G,
        (Finset.univ.filter fun y : SubgroupPoint G =>
          y ≠ x ∧ y ≠ negPoint G hG hnegOne x).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [isGoodMarkedPair_iff_second_avoids_first_and_negFirst
        G hG hnegOne (x, y)]
      by_cases h : y ≠ x ∧ y ≠ negPoint G hG hnegOne x
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    _ = ∑ _x : SubgroupPoint G, (G.card - 2) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact card_good_second_coordinates G hG hnegOne htwo x
    _ = G.card * (G.card - 2) := by simp

/-- Equivalent polynomial form of the exact good-pair mass. -/
theorem goodMarkedPairCount_eq_card_sq_sub_two_mul_card
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) :
    goodMarkedPairCount G = G.card ^ 2 - 2 * G.card := by
  rw [goodMarkedPairCount_eq_card_mul_card_sub_two G hG hnegOne htwo,
    Nat.mul_sub_left_distrib]
  simp [pow_two, Nat.mul_comm]

/-- **Uniform support floor.**  Every good marked phase has at least
`choose(|G|-3,k)` canonical witnesses in the adjacent row. -/
theorem choose_card_sub_three_le_subsetDifferenceMultiplicity_of_goodSupport
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (k : Nat) (t : F)
    (ht : InGoodMarkedDifferenceSupport G t) :
    (G.card - 3).choose k ≤ subsetDifferenceMultiplicity G (k + 2) t := by
  rcases ht with ⟨z, hz, rfl⟩
  rw [← card_canonicalAvailable_of_good G hG hnegOne htwo z hz]
  exact canonicalAvailable_choose_le_subsetDifferenceMultiplicity G hG hnegOne z hz k

theorem fifth_subsetDifference_floor_of_goodSupport
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (t : F) (ht : InGoodMarkedDifferenceSupport G t) :
    (G.card - 3).choose 3 ≤ subsetDifferenceMultiplicity G 5 t := by
  simpa using
    choose_card_sub_three_le_subsetDifferenceMultiplicity_of_goodSupport
      G hG hnegOne htwo 3 t ht

theorem sixth_subsetDifference_floor_of_goodSupport
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (t : F) (ht : InGoodMarkedDifferenceSupport G t) :
    (G.card - 3).choose 4 ≤ subsetDifferenceMultiplicity G 6 t := by
  simpa using
    choose_card_sub_three_le_subsetDifferenceMultiplicity_of_goodSupport
      G hG hnegOne htwo 4 t ht

/-! ## Globalization across all good marked fibres -/

/-- Pointwise product domination: the local support floor is multiplied by the *actual* number
of good marked representatives, then absorbed by the full physical product `W(t) * R(t)`. -/
theorem choose_mul_goodMultiplicity_le_marked_mul_subsetMultiplicity
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (k : Nat) (t : F) :
    (G.card - 3).choose k * goodMarkedDifferenceMultiplicity G t ≤
      markedDifferenceMultiplicity G t * subsetDifferenceMultiplicity G (k + 2) t := by
  by_cases hg0 : goodMarkedDifferenceMultiplicity G t = 0
  · simp [hg0]
  · have hgpos : 0 < goodMarkedDifferenceMultiplicity G t := Nat.pos_of_ne_zero hg0
    have hsupport : InGoodMarkedDifferenceSupport G t :=
      (goodMarkedDifferenceMultiplicity_pos_iff_goodSupport G t).mp hgpos
    have hgoodW := goodMarkedDifferenceMultiplicity_le_markedDifferenceMultiplicity G t
    have hfloor := choose_card_sub_three_le_subsetDifferenceMultiplicity_of_goodSupport
      G hG hnegOne htwo k t hsupport
    simpa [Nat.mul_comm] using Nat.mul_le_mul hgoodW hfloor

/-- **Global canonical-embedding floor for raw `C12`.**  Summing the pointwise domination gives
the exact good-pair mass times `choose(|G|-3,k)` as a lower bound for the actual cross collision. -/
theorem choose_mul_goodPairCount_le_newtonJoinCollisionCount
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (k : Nat) :
    (G.card - 3).choose k * goodMarkedPairCount G ≤
      newtonJoinCollisionCount G 1 (k + 2) 2 (k + 1) := by
  rw [← sum_goodMarkedDifferenceMultiplicity G, Finset.mul_sum]
  rw [show k + 1 = (k + 2) - 1 by omega]
  rw [newtonJoinCollisionCount_one_two_eq_translateCorrelation]
  exact Finset.sum_le_sum fun t _ =>
    choose_mul_goodMultiplicity_le_marked_mul_subsetMultiplicity
      G hG hnegOne htwo k t

/-- Polynomial-mass form of the global canonical floor. -/
theorem choose_mul_card_sq_sub_two_mul_card_le_newtonJoinCollisionCount
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) (k : Nat) :
    (G.card - 3).choose k * (G.card ^ 2 - 2 * G.card) ≤
      newtonJoinCollisionCount G 1 (k + 2) 2 (k + 1) := by
  rw [← goodMarkedPairCount_eq_card_sq_sub_two_mul_card G hG hnegOne htwo]
  exact choose_mul_goodPairCount_le_newtonJoinCollisionCount G hG hnegOne htwo k

/-- Rank-five specialization of the global canonical floor. -/
theorem fifth_choose_mul_goodPairCount_le_newtonJoinCollisionCount
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) :
    (G.card - 3).choose 3 * goodMarkedPairCount G ≤
      newtonJoinCollisionCount G 1 5 2 4 := by
  simpa using choose_mul_goodPairCount_le_newtonJoinCollisionCount
    G hG hnegOne htwo 3

/-- Rank-six specialization of the global canonical floor. -/
theorem sixth_choose_mul_goodPairCount_le_newtonJoinCollisionCount
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) :
    (G.card - 3).choose 4 * goodMarkedPairCount G ≤
      newtonJoinCollisionCount G 1 6 2 5 := by
  simpa using choose_mul_goodPairCount_le_newtonJoinCollisionCount
    G hG hnegOne htwo 4

/-- Fully explicit rank-five global floor. -/
theorem fifth_explicit_canonical_floor
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) :
    (G.card - 3).choose 3 * (G.card ^ 2 - 2 * G.card) ≤
      newtonJoinCollisionCount G 1 5 2 4 := by
  simpa using choose_mul_card_sq_sub_two_mul_card_le_newtonJoinCollisionCount
    G hG hnegOne htwo 3

/-- Fully explicit rank-six global floor. -/
theorem sixth_explicit_canonical_floor
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (htwo : (2 : F) ≠ 0) :
    (G.card - 3).choose 4 * (G.card ^ 2 - 2 * G.card) ≤
      newtonJoinCollisionCount G 1 6 2 5 := by
  simpa using choose_mul_card_sq_sub_two_mul_card_le_newtonJoinCollisionCount
    G hG hnegOne htwo 4

/-! ## A one-phase raw `C12` consumer -/

theorem one_le_markedDifferenceMultiplicity_of_representation
    (G : Finset F) (z : MarkedPair G) :
    1 ≤ markedDifferenceMultiplicity G (markedDifferencePhase G z) := by
  classical
  unfold markedDifferenceMultiplicity phaseFiberCount
  exact Finset.card_pos.mpr ⟨z, by simp⟩

/-- The local support floor already embeds into the full raw cross-collision count.  This records
the honest scale of the construction without claiming that one marked pair supplies the full
production alignment. -/
theorem canonical_floor_le_newtonJoinCollisionCount
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (z : MarkedPair G) (hz : IsGoodMarkedPair G z) (k : Nat) :
    (canonicalAvailable G hG hnegOne z).card.choose k ≤
      newtonJoinCollisionCount G 1 (k + 2) 2 (k + 1) := by
  have hR := canonicalAvailable_choose_le_subsetDifferenceMultiplicity
    G hG hnegOne z hz k
  have hW := one_le_markedDifferenceMultiplicity_of_representation G z
  rw [show k + 1 = (k + 2) - 1 by omega]
  rw [newtonJoinCollisionCount_one_two_eq_translateCorrelation]
  calc
    (canonicalAvailable G hG hnegOne z).card.choose k ≤
        subsetDifferenceMultiplicity G (k + 2) (markedDifferencePhase G z) := hR
    _ = 1 * subsetDifferenceMultiplicity G (k + 2) (markedDifferencePhase G z) := by simp
    _ ≤ markedDifferenceMultiplicity G (markedDifferencePhase G z) *
        subsetDifferenceMultiplicity G (k + 2) (markedDifferencePhase G z) :=
      Nat.mul_le_mul_right _ hW
    _ ≤ ∑ t : F, markedDifferenceMultiplicity G t *
        subsetDifferenceMultiplicity G (k + 2) t :=
      Finset.single_le_sum
        (f := fun t : F => markedDifferenceMultiplicity G t *
          subsetDifferenceMultiplicity G (k + 2) t)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (markedDifferencePhase G z))

/-! ## Axiom audit -/

#print axioms canonicalAdjacentWitness_phase
#print axioms canonicalAdjacentWitness_injective
#print axioms canonicalAvailable_choose_le_subsetDifferenceMultiplicity
#print axioms choose_card_sub_three_le_subsetDifferenceMultiplicity_of_goodSupport
#print axioms fifth_subsetDifference_floor_of_goodSupport
#print axioms sixth_subsetDifference_floor_of_goodSupport
#print axioms sum_goodMarkedDifferenceMultiplicity
#print axioms goodMarkedPairCount_eq_card_sq_sub_two_mul_card
#print axioms choose_mul_goodPairCount_le_newtonJoinCollisionCount
#print axioms fifth_choose_mul_goodPairCount_le_newtonJoinCollisionCount
#print axioms sixth_choose_mul_goodPairCount_le_newtonJoinCollisionCount
#print axioms fifth_explicit_canonical_floor
#print axioms sixth_explicit_canonical_floor
#print axioms canonical_floor_le_newtonJoinCollisionCount

end CanonicalEmbedding

end ArkLib.ProximityGap.Frontier.BGKC12CanonicalEmbeddingFloor
