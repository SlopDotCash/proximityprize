/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKInjectiveFiveWeld

/-!
# The fiber-square census bridge: `injEnergy` = the G112 collision count — #466

The G112 socket (`_G112FiberCollisionVarianceIdentity.lean`) measures the production
depth-five map by its **sum of squared fiber sizes** `∑_y (fiberCount f y)²`. The BGK-side
chain (`_BGKInjectiveFiveWeld.lean`) bounds the **pair census** `injEnergy G r`
(= #{(x, y) injective tuples with equal sums}). This file proves they are the SAME number:

* `sq_fiberCount_eq_pairs` — for any finite map `f : X → Y`, `∑_y (fiberCount f y)²` equals
  the number of pairs `(x, x')` with `f x = f x'` (the standard fiber-pair double count).
* `injEnergy_eq_fiberSquareSum` — specialized to the injective-tuple sum map:
  `injEnergy G r = ∑_y (fiberCount (sumMap) y)²` where `sumMap : injTuples → F` sends a
  tuple to its coordinate sum.
* `bgk_production_fiberSquare_weld` — therefore, at the literal prize numbers, any BGK
  sup-bound `M ≤ 2⁴⁰` forces `(∑_y (fiberCount sumMap y)²) · productionDepthFiveBase ≤
  productionWick` — the EXACT conclusion of G112's
  `production_depth_five_of_centered_variance`, but with the (unproven, open) centered
  variance certificate hypothesis REPLACED by the named BGK Prop. The two open routes to the
  depth-five envelope are thereby proven equivalent-in-effect; the single open input remains
  `WorstCaseIncompleteSumBound`. Nothing here discharges it. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity
open ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld
open ArkLib.ProximityGap.Frontier.BGKInjectiveFiveWeld

namespace ArkLib.ProximityGap.Frontier.BGKFiberSquareCensusBridge

/-- **Fiber-pair double count**: for a map between fintypes, the sum of squared fiber sizes
is the number of collision pairs `#{(x, x') : f x = f x'}`. -/
theorem sq_fiberCount_eq_pairs {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    ∑ y, (fiberCount f y) ^ 2
      = (Finset.univ.filter (fun p : X × X => f p.1 = f p.2)).card := by
  classical
  have hfc : ∀ y, fiberCount f y = (Finset.univ.filter (fun x => f x = y)).card := by
    intro y
    rw [fiberCount, Fintype.card_subtype]
  calc ∑ y, (fiberCount f y) ^ 2
      = ∑ y, ((Finset.univ.filter (fun x => f x = y)).card
          * (Finset.univ.filter (fun x' => f x' = y)).card) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hfc]; ring
    _ = ∑ y, ((Finset.univ.filter (fun x => f x = y))
          ×ˢ (Finset.univ.filter (fun x' => f x' = y))).card := by
        simp [Finset.card_product]
    _ = ∑ y, (Finset.univ.filter (fun p : X × X => f p.1 = y ∧ f p.2 = y)).card := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        congr 1
        ext p
        simp [Finset.mem_product]
    _ = (Finset.univ.filter (fun p : X × X => f p.1 = f p.2)).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext p
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          constructor
          · rintro ⟨y, ⟨h1, h2⟩⟩; rw [h1, h2]
          · intro h; exact ⟨f p.2, ⟨h, rfl⟩⟩
        · intro a _ b _ hab
          apply Finset.disjoint_left.mpr
          intro p hp hq
          simp only [Finset.mem_filter] at hp hq
          exact hab (hp.2.1.symm.trans hq.2.1)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The coordinate-sum map on the injective `r`-tuple domain. -/
noncomputable def sumMap (G : Finset F) (r : ℕ) (p : {p // p ∈ injTuples G r}) : F :=
  ∑ i, p.1 i

/-- **The census identity**: the injective depth-`r` collision count IS the sum of squared
fiber sizes of the coordinate-sum map — the exact quantity the G112 socket measures. -/
theorem injEnergy_eq_fiberSquareSum (G : Finset F) (r : ℕ) :
    injEnergy G r = ∑ y, (fiberCount (sumMap G r) y) ^ 2 := by
  classical
  rw [sq_fiberCount_eq_pairs (sumMap G r)]
  -- Both sides count pairs of injective tuples with equal sums; exhibit the equivalence
  -- between the two subtype presentations.
  rw [injEnergy, ← Fintype.card_coe, ← Fintype.card_coe]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q =>
        ⟨(⟨q.1.1, ?_⟩, ⟨q.1.2, ?_⟩), ?_⟩
      invFun := fun q => ⟨(q.1.1.1, q.1.2.1), ?_⟩
      left_inv := fun q => rfl
      right_inv := fun q => rfl }
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp q.2).1).1
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp q.2).1).2
  · have hsum := (Finset.mem_filter.mp q.2).2
    simpa [sumMap] using hsum
  · have hmem := q.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨q.1.1.2, q.1.2.2⟩, ?_⟩
    simpa [sumMap] using hmem

/-- **BGK ⟹ the G112 fiber-square envelope, end to end.** At the literal prize numbers,
any BGK sup-bound `M ≤ 2⁴⁰` forces the exact G112 conclusion

  `(∑_y (fiberCount (sumMap G 5) y)²) · productionDepthFiveBase ≤ productionWick`

— the same inequality `production_depth_five_of_centered_variance` derives from its (open)
centered-variance certificate, now derived instead from the single named open BGK Prop. -/
theorem bgk_production_fiberSquare_weld {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 2 ^ 40)
    (hwc : WorstCaseIncompleteSumBound ψ G M)
    (hG : G.card = 2 ^ 30) (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) :
    (∑ y, (fiberCount (sumMap G 5) y) ^ 2) * productionDepthFiveBase ≤ productionWick := by
  rw [← injEnergy_eq_fiberSquareSum]
  exact bgk_production_injective_weld hψ G hM0 hM hwc hG hq

end ArkLib.ProximityGap.Frontier.BGKFiberSquareCensusBridge

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKFiberSquareCensusBridge.sq_fiberCount_eq_pairs
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFiberSquareCensusBridge.injEnergy_eq_fiberSquareSum
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFiberSquareCensusBridge.bgk_production_fiberSquare_weld
