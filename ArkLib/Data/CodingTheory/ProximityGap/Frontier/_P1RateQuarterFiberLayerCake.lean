/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterLayerCakeBudget

/-!
# Exact layer-cake identities for finite pencil fibers

This file isolates the combinatorial assembly needed by the rate-quarter small-pool
ledger.  A family split into fibers is not controlled by merely counting the fibers:
one must sum their multiplicities.  The exact discrete layer-cake identity rewrites
that mass as the sum of the numbers of fibers surviving each positive multiplicity
threshold.  Consequently, levelwise bounds may be summed without losing marginal
information.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterFiberLayerCake

attribute [local instance] Classical.propDecidable

open _root_.ProximityGap Code
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge

/-- The contribution of one natural weight is the number of positive integer levels
strictly below it. -/
theorem card_filter_range_lt_weight (w M : ℕ) (hw : w ≤ M) :
    ((Finset.range M).filter (fun m => m < w)).card = w := by
  have hfin : (Finset.range M).filter (fun m => m < w) = Finset.range w := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfin, Finset.card_range]

/-- **Exact discrete layer cake.**  The total mass of bounded natural weights equals
the sum, over levels `m < M`, of the number of objects whose weight exceeds `m`.

The bound `w x ≤ M` is used only to truncate the otherwise infinite level sum. -/
theorem sum_eq_sum_card_superlevel {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (M : ℕ) (hw : ∀ x ∈ s, w x ≤ M) :
    ∑ x ∈ s, w x = ∑ m ∈ Finset.range M, (s.filter (fun x => m < w x)).card := by
  classical
  calc
    ∑ x ∈ s, w x
        = ∑ x ∈ s, ((Finset.range M).filter (fun m => m < w x)).card := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (card_filter_range_lt_weight (w x) M (hw x hx)).symm
    _ = ∑ x ∈ s, ∑ m ∈ Finset.range M, if m < w x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.card_filter]
    _ = ∑ m ∈ Finset.range M, ∑ x ∈ s, if m < w x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range M, (s.filter (fun x => m < w x)).card := by
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.card_filter]

/-- Levelwise caps sum to a total mass cap.  This is the direct consumer required by
the small-pool histogram: no monotonicity or disjointness between superlevel sets is
needed. -/
theorem sum_le_sum_superlevel_caps {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (M : ℕ) (cap : ℕ → ℕ)
    (hw : ∀ x ∈ s, w x ≤ M)
    (hcap : ∀ m < M, (s.filter (fun x => m < w x)).card ≤ cap m) :
    ∑ x ∈ s, w x ≤ ∑ m ∈ Finset.range M, cap m := by
  rw [sum_eq_sum_card_superlevel s w M hw]
  exact Finset.sum_le_sum fun m hm => hcap m (Finset.mem_range.mp hm)

/-! ## Specialization to the predecessor pencil partition -/

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩

/-- **Exact pencil-fiber mass.**  After choosing a base scalar, the number of remaining
bad scalars is exactly the sum of the multiplicities of the distinct pencils through
that base.  This is the equality underlying `badFamily_card_le_one_add_pencilImage`;
keeping the individual multiplicities is what makes a marginal ledger possible. -/
theorem erase_card_eq_sum_pencilFiber
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (γ₀ : F) :
    (G.erase γ₀).card =
      ∑ π ∈ (G.erase γ₀).image (pencilOf pf γ₀),
        ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise
    (fun γ hγ => Finset.mem_image_of_mem (pencilOf pf γ₀) hγ)

/-- The corresponding identity including the chosen base scalar. -/
theorem badFamily_card_eq_one_add_sum_pencilFiber
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G) :
    G.card = 1 +
      ∑ π ∈ (G.erase γ₀).image (pencilOf pf γ₀),
        ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card := by
  rw [← erase_card_eq_sum_pencilFiber dom u₀ u₁ G Sf pf γ₀]
  calc
    G.card = (G.erase γ₀).card + 1 := (Finset.card_erase_add_one hγ₀).symm
    _ = 1 + (G.erase γ₀).card := Nat.add_comm _ _

/-- **Pencil-superlevel consumer.**  Suppose every pencil fiber has size at most `M`
and, for each multiplicity level `m < M`, at most `cap m` distinct pencils have more
than `m` riders.  Then the whole bad family has size at most one plus the sum of these
level caps.

This is the precise combinatorial socket required by the small-pool Johnson ledger. -/
theorem badFamily_card_le_one_add_sum_superlevelCaps
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G) (M : ℕ) (cap : ℕ → ℕ)
    (hfiber : ∀ π ∈ (G.erase γ₀).image (pencilOf pf γ₀),
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card ≤ M)
    (hlevel : ∀ m < M,
      (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
        m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ cap m) :
    G.card ≤ 1 + ∑ m ∈ Finset.range M, cap m := by
  let pencils := (G.erase γ₀).image (pencilOf pf γ₀)
  let weight := fun π =>
    ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card
  have hmass : ∑ π ∈ pencils, weight π ≤ ∑ m ∈ Finset.range M, cap m :=
    sum_le_sum_superlevel_caps pencils weight M cap
      (fun π hπ => hfiber π hπ)
      (fun m hm => hlevel m hm)
  rw [badFamily_card_eq_one_add_sum_pencilFiber dom u₀ u₁ G Sf pf γ₀ hγ₀]
  exact Nat.add_le_add_left hmass 1

/-- The prize-facing version: `fiber_card_le` supplies the truncation automatically,
so proving a level cap for each `m < N-T` is sufficient to bound the bad family. -/
theorem badFamily_card_le_one_add_sum_superlevelCaps_of_data
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G) (cap : ℕ → ℕ)
    (hlevel : ∀ m < N - predecessorThreshold,
      (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
        m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ cap m) :
    G.card ≤ 1 + ∑ m ∈ Finset.range (N - predecessorThreshold), cap m := by
  exact badFamily_card_le_one_add_sum_superlevelCaps dom u₀ u₁ G Sf pf γ₀ hγ₀
    (N - predecessorThreshold) cap
    (fiber_card_le dom u₀ u₁ G Sf pf hdata γ₀ hγ₀) hlevel

end ArkLib.ProximityGap.Frontier.P1RateQuarterFiberLayerCake

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterFiberLayerCake

#print axioms sum_eq_sum_card_superlevel
#print axioms sum_le_sum_superlevel_caps
#print axioms erase_card_eq_sum_pencilFiber
#print axioms badFamily_card_eq_one_add_sum_pencilFiber
#print axioms badFamily_card_le_one_add_sum_superlevelCaps
#print axioms badFamily_card_le_one_add_sum_superlevelCaps_of_data
