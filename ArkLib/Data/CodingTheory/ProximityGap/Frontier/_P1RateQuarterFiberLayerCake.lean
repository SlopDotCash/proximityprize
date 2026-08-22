/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilHarvestCap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSmallPoolAssembly

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
set_option maxRecDepth 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterFiberLayerCake

attribute [local instance] Classical.propDecidable

open _root_.ProximityGap Code
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolAssembly
open ArkLib.ProximityGap.Frontier.P1RateQuarterLayerCakeBudget
open ProximityGap.SharedFreshPencil

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

local instance localInstance_P1RateQuarterFiberLayerCake_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterFiberLayerCake_2 : NeZero N := ⟨by norm_num [N]⟩

/-- The fiber over an image pencil is literally a family riding that pencil.  This
packages the reconstruction repeated inside `fiber_card_le` as a reusable bridge. -/
theorem pencilFiber_ridesAll
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (π : (Fin N → F) × (Fin N → F)) :
    RidesAll dom u₀ u₁ π.1 π.2
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)) Sf := by
  classical
  apply ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata
  · intro γ hγ
    exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hγ).1
  · intro γ hγ
    have hγerase := (Finset.mem_filter.mp hγ).1
    have hπ := (Finset.mem_filter.mp hγ).2
    have hne : γ₀ ≠ γ := fun h => (Finset.mem_erase.mp hγerase).1 h.symm
    have hrepro := pencil_reproduces_second hne (pf γ₀) (pf γ)
    rw [← hπ]
    simpa [pencilOf] using hrepro.symm

/-- An image pencil passes through the chosen base witness. -/
theorem imagePencil_base
    (pf : F → Fin N → F) (G : Finset F) (γ₀ : F)
    (π : (Fin N → F) × (Fin N → F))
    (hπ : π ∈ (G.erase γ₀).image (pencilOf pf γ₀)) :
    ∀ i, π.1 i + γ₀ * π.2 i = pf γ₀ i := by
  classical
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hπ
  intro i
  have hrepro := pencil_reproduces_first γ₀ γ (pf γ₀) (pf γ)
  simpa [pencilOf, smul_eq_mul] using congrFun hrepro i

/-- Both components of an image pencil are predecessor codewords. -/
theorem imagePencil_mem
    (dom : Fin N ↪ F) (pf : F → Fin N → F) (G : Finset F) (γ₀ : F)
    (hγ₀ : γ₀ ∈ G) (hcode : ∀ γ ∈ G, pf γ ∈ predecessorCode dom)
    (π : (Fin N → F) × (Fin N → F))
    (hπ : π ∈ (G.erase γ₀).image (pencilOf pf γ₀)) :
    π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom := by
  classical
  obtain ⟨γ, hγerase, hEq⟩ := Finset.mem_image.mp hπ
  have hγ : γ ∈ G := Finset.mem_of_mem_erase hγerase
  constructor
  · rw [← hEq]
    exact pencilBase_mem (predecessorCode dom) (hcode γ₀ hγ₀) (hcode γ hγ)
  · rw [← hEq]
    exact pencilDir_mem (predecessorCode dom) (hcode γ₀ hγ₀) (hcode γ hγ)

/-- **Exact shared-pool charge for one divided-difference fiber.**  Fiber
multiplicity times alignment deficit is bounded by the base discrepancy pool. -/
theorem pencilFiber_mul_deficit_le_pool
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (π : (Fin N → F) × (Fin N → F))
    (hπ : π ∈ (G.erase γ₀).image (pencilOf pf γ₀)) :
    ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card *
        (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) ≤
      (Dsupport u₀ u₁ (pf γ₀) γ₀).card := by
  classical
  exact riders_mul_le_Dsupport u₀ u₁ (pf γ₀) γ₀ dom
    ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)) Sf
    (imagePencil_base pf G γ₀ π hπ)
    (pencilFiber_ridesAll dom u₀ u₁ G Sf pf hdata γ₀ π)
    (fun hmem => (Finset.mem_erase.mp (Finset.mem_filter.mp hmem).1).1 rfl)

/-- Every divided-difference fiber is bounded by the *actual* shared pool size.
This supplies the sharp truncation length for the layer-cake sum. -/
theorem pencilFiber_card_le_pool
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G) (π : (Fin N → F) × (Fin N → F))
    (hπ : π ∈ (G.erase γ₀).image (pencilOf pf γ₀)) :
    ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card ≤
      (Dsupport u₀ u₁ (pf γ₀) γ₀).card := by
  classical
  have hmem := imagePencil_mem dom pf G γ₀ hγ₀
    (fun γ hγ => (hdata γ hγ).2.1) π hπ
  exact riders_card_le_pool u₀ u₁ (pf γ₀) γ₀ dom
    ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)) Sf
    hmem.1 hmem.2 (imagePencil_base pf G γ₀ π hπ)
    (pencilFiber_ridesAll dom u₀ u₁ G Sf pf hdata γ₀ π)
    (fun hmemγ => (Finset.mem_erase.mp (Finset.mem_filter.mp hmemγ).1).1 rfl)

/-- A superlevel condition gives the exact marginal alignment constraint used by the
small-pool ledger.  Notice the `m+1`: fiber size excludes the base scalar, so this is
equivalently a pencil with at least `m+2` total riders. -/
theorem superlevel_mul_deficit_le_pool
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (π : (Fin N → F) × (Fin N → F))
    (hπ : π ∈ (G.erase γ₀).image (pencilOf pf γ₀)) (m : ℕ)
    (hm : m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card) :
    (m + 1) * (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) ≤
      (Dsupport u₀ u₁ (pf γ₀) γ₀).card := by
  have hcharge := pencilFiber_mul_deficit_le_pool dom u₀ u₁ G Sf pf hdata γ₀ π hπ
  exact (Nat.mul_le_mul_right _ (Nat.add_one_le_iff.mpr hm)).trans hcharge

/-- A pool upper bound converts a fiber superlevel into a concrete alignment floor.
The strict `+1` boundary is the exact natural-number rounding of
`(m+1)(T-A) ≤ pool`. -/
theorem alignment_floor_of_superlevel_and_pool
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (π : (Fin N → F) × (Fin N → F))
    (hπ : π ∈ (G.erase γ₀).image (pencilOf pf γ₀)) (m a : ℕ)
    (hm : m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)
    (haT : a ≤ predecessorThreshold)
    (hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card <
      (m + 1) * (predecessorThreshold - a + 1)) :
    a ≤ (alignedSet u₀ u₁ π.1 π.2).card := by
  have hcharge := superlevel_mul_deficit_le_pool dom u₀ u₁ G Sf pf hdata γ₀ π hπ m hm
  by_contra hnot
  rw [not_le] at hnot
  have hdef : predecessorThreshold - a + 1 ≤
      predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card := by omega
  have hmul := Nat.mul_le_mul_left (m + 1) hdef
  omega

/-- **Superlevel pencils are relative-Johnson packed.**  This theorem performs all
previously missing plumbing: image pencils are code-valued, pass through the base,
their fiber superlevel forces alignment `≥ a` from the common pool bound, and their
aligned regions are packed inside `Dzero`.

Only the two numerical side conditions remain: `a ≥ k-1` and the strict rounded pool
threshold `pool < (m+1)(T-a+1)`. -/
theorem pencilSuperlevel_johnson_on_Dzero
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G) (m a : ℕ)
    (haT : a ≤ predecessorThreshold) (hka : k - 1 ≤ a)
    (hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card <
      (m + 1) * (predecessorThreshold - a + 1)) :
    let Fam := ((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
      m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)
    Fam.card * a ^ 2 + (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) ≤
      (Dzero u₀ u₁ (pf γ₀) γ₀).card * a +
        Fam.card * ((Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1)) := by
  classical
  dsimp only
  apply dirFamily_johnson_on_Dzero dom u₀ u₁ (pf γ₀) γ₀ _ a
  · intro π hπ
    have himage := (Finset.mem_filter.mp hπ).1
    exact imagePencil_mem dom pf G γ₀ hγ₀
      (fun γ hγ => (hdata γ hγ).2.1) π himage
  · intro π hπ
    exact imagePencil_base pf G γ₀ π (Finset.mem_filter.mp hπ).1
  · intro π hπ
    exact alignment_floor_of_superlevel_and_pool dom u₀ u₁ G Sf pf hdata γ₀ π
      (Finset.mem_filter.mp hπ).1 m a (Finset.mem_filter.mp hπ).2 haT hpool
  · exact hka

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

/-- Sharp-pool version of the layer-cake consumer.  Its sum has exactly `|Dsupport|`
levels, matching the probe and the small-pool histogram. -/
theorem badFamily_card_le_one_add_sum_poolSuperlevelCaps
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G) (cap : ℕ → ℕ)
    (hlevel : ∀ m < (Dsupport u₀ u₁ (pf γ₀) γ₀).card,
      (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
        m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ cap m) :
    G.card ≤ 1 +
      ∑ m ∈ Finset.range (Dsupport u₀ u₁ (pf γ₀) γ₀).card, cap m := by
  exact badFamily_card_le_one_add_sum_superlevelCaps dom u₀ u₁ G Sf pf γ₀ hγ₀
    (Dsupport u₀ u₁ (pf γ₀) γ₀).card cap
    (pencilFiber_card_le_pool dom u₀ u₁ G Sf pf hdata γ₀ hγ₀) hlevel

/-- The probe-swept uniform histogram used by the robust small-pool ledger. -/
def uniformSmallPoolCap (m : ℕ) : ℕ :=
  if m = 0 then 657668325 else if m = 1 then 7 else 5

/-- Closed form upper bound for the uniform histogram at an arbitrary truncation. -/
theorem sum_uniformSmallPoolCap_le (M : ℕ) :
    ∑ m ∈ Finset.range M, uniformSmallPoolCap m ≤
      657668325 + 7 + 5 * (M - 2) := by
  rcases M with _ | _ | q
  · simp
  · simp [uniformSmallPoolCap]
  · have hexact : ∑ m ∈ Finset.range (q + 2), uniformSmallPoolCap m =
        657668325 + 7 + q * 5 := by
      induction q with
      | zero => norm_num [Finset.sum_range_succ, uniformSmallPoolCap]
      | succ q ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [uniformSmallPoolCap]
          split <;> rename_i hzero
          · omega
          · split <;> rename_i hone
            · omega
            · omega
    rw [hexact]
    omega

/-- **Uniform-cap small-pool consumer.**  Once the three claimed superlevel caps
(`657668325`, `7`, and `5`) have been established, every base pool of size at most
`F₀ = 75018133` closes the full bad-family budget. -/
theorem badFamily_card_le_N_of_uniformSmallPoolCaps
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ 75018133)
    (hlevel : ∀ m < (Dsupport u₀ u₁ (pf γ₀) γ₀).card,
      (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
        m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤
          uniformSmallPoolCap m) :
    G.card ≤ N := by
  have hmass := badFamily_card_le_one_add_sum_poolSuperlevelCaps
    dom u₀ u₁ G Sf pf hdata γ₀ hγ₀ uniformSmallPoolCap hlevel
  have hsum := sum_uniformSmallPoolCap_le
    (Dsupport u₀ u₁ (pf γ₀) γ₀).card
  have htail : 5 * ((Dsupport u₀ u₁ (pf γ₀) γ₀).card - 2) ≤
      5 * (75018133 - 2) := Nat.mul_le_mul_left 5 (Nat.sub_le_sub_right hpool 2)
  have hbudget := ledger_uniform_caps_le_N
  omega

/-! ## Correlated Johnson arithmetic over the whole small-pool interval -/

/-- Level zero: the correlation `Z=N-F`, `a=T-F` uniformly rules out the
next integer after the sharp cap `657668325`. -/
theorem levelZero_correlated_gap (x : ℕ) (hx : x ≤ 75018133) :
    (1073741824 - x) * (592794966 - x) +
        657668326 * ((1073741824 - x) * 268435455) <
      657668326 * (592794966 - x) ^ 2 +
        (1073741824 - x) * 268435455 := by
  have hz : 1073741824 - x + x = 1073741824 := Nat.sub_add_cancel (by omega)
  have ha : 592794966 - x + x = 592794966 := Nat.sub_add_cancel (by omega)
  have hap : 592794966 - x - 268435455 + 268435455 = 592794966 - x :=
    Nat.sub_add_cancel (by omega)
  nlinarith

/-- Level one, even pool. -/
theorem levelOne_even_correlated_gap (q : ℕ) (hq : 2 * q ≤ 75018133) :
    (1073741824 - 2*q) * (592794966 - q) +
        8 * ((1073741824 - 2*q) * 268435455) <
      8 * (592794966 - q) ^ 2 +
        (1073741824 - 2*q) * 268435455 := by
  have hz : 1073741824 - 2*q + 2*q = 1073741824 := Nat.sub_add_cancel (by omega)
  have ha : 592794966 - q + q = 592794966 := Nat.sub_add_cancel (by omega)
  have hap : 592794966 - q - 268435455 + 268435455 = 592794966 - q :=
    Nat.sub_add_cancel (by omega)
  nlinarith

/-- Level one, odd pool. -/
theorem levelOne_odd_correlated_gap (q : ℕ) (hq : 2*q + 1 ≤ 75018133) :
    (1073741824 - (2*q+1)) * (592794966 - q) +
        8 * ((1073741824 - (2*q+1)) * 268435455) <
      8 * (592794966 - q) ^ 2 +
        (1073741824 - (2*q+1)) * 268435455 := by
  have hz : 1073741824 - (2*q+1) + (2*q+1) = 1073741824 :=
    Nat.sub_add_cancel (by omega)
  have ha : 592794966 - q + q = 592794966 := Nat.sub_add_cancel (by omega)
  have hap : 592794966 - q - 268435455 + 268435455 = 592794966 - q :=
    Nat.sub_add_cancel (by omega)
  nlinarith

/-- Level two dominates every later level.  The three cases `r=0,1,2` are
the complete residue split for the rounded floor `F/3`. -/
theorem levelTwo_modThree_correlated_gap (q r : ℕ) (hr : r ≤ 2)
    (hq : 3*q + r ≤ 75018133) :
    (1073741824 - (3*q+r)) * (592794966 - q) +
        6 * ((1073741824 - (3*q+r)) * 268435455) <
      6 * (592794966 - q) ^ 2 +
        (1073741824 - (3*q+r)) * 268435455 := by
  have hz : 1073741824 - (3*q+r) + (3*q+r) = 1073741824 :=
    Nat.sub_add_cancel (by omega)
  have ha : 592794966 - q + q = 592794966 := Nat.sub_add_cancel (by omega)
  have hap : 592794966 - q - 268435455 + 268435455 = 592794966 - q :=
    Nat.sub_add_cancel (by omega)
  interval_cases r <;> nlinarith

/-- A strict numerical Johnson gap rules out the indicated next family size. -/
theorem card_lt_of_johnson_core_gap {L z a p card : ℕ} (hap : p ≤ a)
    (hden : z * p < a ^ 2)
    (hcore : card * a ^ 2 + z * p ≤ z * a + card * (z * p))
    (hgap : z * a + L * (z * p) < L * a ^ 2 + z * p) :
    card < L := by
  have hsubcore := johnson_core_to_subtracted hap (le_of_lt hden) hcore
  have hdenEq : a ^ 2 - z * p + z * p = a ^ 2 :=
    Nat.sub_add_cancel (le_of_lt hden)
  have hapEq : a - p + p = a := Nat.sub_add_cancel hap
  have hgap' : z * (a - p) < L * (a ^ 2 - z * p) := by
    nlinarith
  by_contra hnot
  rw [not_lt] at hnot
  have hmono : L * (a ^ 2 - z * p) ≤ card * (a ^ 2 - z * p) :=
    Nat.mul_le_mul_right _ hnot
  omega

/-- Direct consumer combining the superlevel-to-Johnson bridge with a numerical gap. -/
theorem pencilSuperlevel_card_lt_of_gap
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G) (m a L : ℕ)
    (haT : a ≤ predecessorThreshold) (hka : k - 1 ≤ a)
    (hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card <
      (m + 1) * (predecessorThreshold - a + 1))
    (hden : (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) < a ^ 2)
    (hgap : (Dzero u₀ u₁ (pf γ₀) γ₀).card * a +
        L * ((Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1)) <
      L * a ^ 2 + (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1)) :
    (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
      m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card < L := by
  have hcore := pencilSuperlevel_johnson_on_Dzero dom u₀ u₁ G Sf pf hdata γ₀ hγ₀
    m a haT hka hpool
  exact card_lt_of_johnson_core_gap hka hden hcore hgap

/-- Uniform level-zero cap over every small pool. -/
theorem levelZero_superlevel_card_le_657668325
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (hsmall : (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ 75018133) :
    (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
      0 < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤
        657668325 := by
  let x := (Dsupport u₀ u₁ (pf γ₀) γ₀).card
  have hx : x ≤ 75018133 := hsmall
  have hpart := Dsupport_card_add_Dzero_card u₀ u₁ (pf γ₀) γ₀
  have hz : (Dzero u₀ u₁ (pf γ₀) γ₀).card = N - x := by
    dsimp [x] at hpart ⊢
    omega
  have haT : predecessorThreshold - x ≤ predecessorThreshold := Nat.sub_le _ _
  have hka : k - 1 ≤ predecessorThreshold - x := by
    norm_num [predecessorThreshold_eq, k]
    omega
  have hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card <
      (0 + 1) * (predecessorThreshold - (predecessorThreshold - x) + 1) := by
    change x < (0 + 1) * (predecessorThreshold - (predecessorThreshold - x) + 1)
    have hxT : x ≤ predecessorThreshold := by
      norm_num [predecessorThreshold_eq]
      omega
    omega
  have hden : (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) <
      (predecessorThreshold - x) ^ 2 := by
    rw [hz]
    exact johnson_condition_of_le_boundary hx
  have hgap : (Dzero u₀ u₁ (pf γ₀) γ₀).card * (predecessorThreshold - x) +
        657668326 * ((Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1)) <
      657668326 * (predecessorThreshold - x) ^ 2 +
        (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) := by
    rw [hz]
    simpa [N, k, predecessorThreshold_eq] using levelZero_correlated_gap x hx
  have hlt := pencilSuperlevel_card_lt_of_gap dom u₀ u₁ G Sf pf hdata γ₀ hγ₀
    0 (predecessorThreshold - x) 657668326 haT hka hpool hden hgap
  omega

/-- Uniform level-one cap, with the only rounding split being pool parity. -/
theorem levelOne_superlevel_card_le_seven
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (hsmall : (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ 75018133) :
    (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
      1 < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ 7 := by
  let x := (Dsupport u₀ u₁ (pf γ₀) γ₀).card
  let a := predecessorThreshold - x / 2
  have hx : x ≤ 75018133 := hsmall
  have hpart := Dsupport_card_add_Dzero_card u₀ u₁ (pf γ₀) γ₀
  have hz : (Dzero u₀ u₁ (pf γ₀) γ₀).card = N - x := by
    dsimp [x] at hpart ⊢
    omega
  have hxT : x ≤ predecessorThreshold := by
    norm_num [predecessorThreshold_eq]
    omega
  have haT : a ≤ predecessorThreshold := by dsimp [a]; omega
  have hka : k - 1 ≤ a := by
    dsimp [a]
    norm_num [predecessorThreshold_eq, k]
    omega
  have hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card <
      (1 + 1) * (predecessorThreshold - a + 1) := by
    change x < (1 + 1) * (predecessorThreshold - a + 1)
    dsimp [a]
    omega
  have hbaseDen := johnson_condition_of_le_boundary hx
  have hfloor : predecessorThreshold - x ≤ a := by dsimp [a]; omega
  have hden : (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) < a ^ 2 := by
    rw [hz]
    exact hbaseDen.trans_le (Nat.pow_le_pow_left hfloor 2)
  have hgap : (Dzero u₀ u₁ (pf γ₀) γ₀).card * a +
        8 * ((Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1)) <
      8 * a ^ 2 + (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) := by
    rw [hz]
    have hN : N = 1073741824 := by norm_num [N]
    have hk : k - 1 = 268435455 := by norm_num [k]
    rw [hN, hk]
    obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' x
    · rw [hq]
      have ha : a = 592794966 - q := by
        dsimp [a]
        rw [hq]
        rw [predecessorThreshold_eq]
        omega
      rw [ha]
      exact levelOne_even_correlated_gap q (hq ▸ hx)
    · rw [hq]
      have ha : a = 592794966 - q := by
        dsimp [a]
        rw [hq]
        rw [predecessorThreshold_eq]
        omega
      rw [ha]
      exact levelOne_odd_correlated_gap q (hq ▸ hx)
  have hlt := pencilSuperlevel_card_lt_of_gap dom u₀ u₁ G Sf pf hdata γ₀ hγ₀
    1 a 8 haT hka hpool hden hgap
  omega

/-- Uniform level-two cap; every later superlevel is a subset of this one. -/
theorem levelTwo_superlevel_card_le_five
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (hsmall : (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ 75018133) :
    (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
      2 < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ 5 := by
  let x := (Dsupport u₀ u₁ (pf γ₀) γ₀).card
  let a := predecessorThreshold - x / 3
  have hx : x ≤ 75018133 := hsmall
  have hpart := Dsupport_card_add_Dzero_card u₀ u₁ (pf γ₀) γ₀
  have hz : (Dzero u₀ u₁ (pf γ₀) γ₀).card = N - x := by
    dsimp [x] at hpart ⊢
    omega
  have hxT : x ≤ predecessorThreshold := by
    norm_num [predecessorThreshold_eq]
    omega
  have haT : a ≤ predecessorThreshold := by dsimp [a]; omega
  have hka : k - 1 ≤ a := by
    dsimp [a]
    norm_num [predecessorThreshold_eq, k]
    omega
  have hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card <
      (2 + 1) * (predecessorThreshold - a + 1) := by
    change x < (2 + 1) * (predecessorThreshold - a + 1)
    dsimp [a]
    omega
  have hbaseDen := johnson_condition_of_le_boundary hx
  have hfloor : predecessorThreshold - x ≤ a := by dsimp [a]; omega
  have hden : (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) < a ^ 2 := by
    rw [hz]
    exact hbaseDen.trans_le (Nat.pow_le_pow_left hfloor 2)
  have hgap : (Dzero u₀ u₁ (pf γ₀) γ₀).card * a +
        6 * ((Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1)) <
      6 * a ^ 2 + (Dzero u₀ u₁ (pf γ₀) γ₀).card * (k - 1) := by
    rw [hz]
    have hN : N = 1073741824 := by norm_num [N]
    have hk : k - 1 = 268435455 := by norm_num [k]
    rw [hN, hk]
    let q := x / 3
    let r := x % 3
    have hr : r ≤ 2 := by
      have := Nat.mod_lt x (by omega : 0 < 3)
      dsimp [r]
      omega
    have hqr : x = 3 * q + r := by
      have h := Nat.mod_add_div x 3
      dsimp [q, r]
      omega
    rw [hqr]
    have ha : a = 592794966 - q := by
      dsimp [a, q]
      rw [predecessorThreshold_eq]
    rw [ha]
    exact levelTwo_modThree_correlated_gap q r hr (hqr ▸ hx)
  have hlt := pencilSuperlevel_card_lt_of_gap dom u₀ u₁ G Sf pf hdata γ₀ hγ₀
    2 a 6 haT hka hpool hden hgap
  omega

/-- All uniform small-pool superlevel caps, assembled from levels zero, one, and two. -/
theorem uniformSmallPool_superlevel_caps
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (hsmall : (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ 75018133) :
    ∀ m < (Dsupport u₀ u₁ (pf γ₀) γ₀).card,
      (((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
        m < ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤
          uniformSmallPoolCap m := by
  intro m hm
  rcases m with _ | _ | m
  · simpa [uniformSmallPoolCap] using
      levelZero_superlevel_card_le_657668325 dom u₀ u₁ G Sf pf hdata γ₀ hγ₀ hsmall
  · simpa [uniformSmallPoolCap] using
      levelOne_superlevel_card_le_seven dom u₀ u₁ G Sf pf hdata γ₀ hγ₀ hsmall
  · have htwo := levelTwo_superlevel_card_le_five dom u₀ u₁ G Sf pf
      hdata γ₀ hγ₀ hsmall
    have hsub :
        ((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
          m + 2 < ((G.erase γ₀).filter
            (fun γ => pencilOf pf γ₀ γ = π)).card) ⊆
        ((G.erase γ₀).image (pencilOf pf γ₀)).filter (fun π =>
          2 < ((G.erase γ₀).filter
            (fun γ => pencilOf pf γ₀ γ = π)).card) := by
      intro π hπ
      rw [Finset.mem_filter] at hπ ⊢
      exact ⟨hπ.1, by omega⟩
    have hcard := Finset.card_le_card hsub
    simpa [uniformSmallPoolCap] using hcard.trans htwo

/-- **The small-pool residual is discharged.**  The exact layer cake, correlated
relative-Johnson caps, and uniform histogram prove `SmallPoolClosure` for every
canonical evaluation domain. -/
theorem smallPoolClosure_proved (dom : Fin N ↪ F) : SmallPoolClosure dom := by
  intro u₀ u₁ G Sf pf hdata hsmall
  obtain ⟨γ₀, hγ₀, hpool⟩ := hsmall
  exact badFamily_card_le_N_of_uniformSmallPoolCaps dom u₀ u₁ G Sf pf hdata γ₀ hγ₀
    hpool (uniformSmallPool_superlevel_caps dom u₀ u₁ G Sf pf hdata γ₀ hγ₀ hpool)

/-- The predecessor bad-family budget now depends only on the genuine stall residual. -/
theorem predecessor_budget_of_stall_after_layerCake (dom : Fin N ↪ F)
    (hstall : StallResidual dom) :
    ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N))
      (pf : F → Fin N → F),
      BadFamilyData dom u₀ u₁ G Sf pf → G.card ≤ N :=
  predecessor_budget_of_smallPool_and_stall dom (smallPoolClosure_proved dom) hstall

end ArkLib.ProximityGap.Frontier.P1RateQuarterFiberLayerCake

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterFiberLayerCake

#print axioms sum_eq_sum_card_superlevel
#print axioms sum_le_sum_superlevel_caps
#print axioms pencilFiber_ridesAll
#print axioms imagePencil_base
#print axioms imagePencil_mem
#print axioms pencilFiber_mul_deficit_le_pool
#print axioms pencilFiber_card_le_pool
#print axioms superlevel_mul_deficit_le_pool
#print axioms alignment_floor_of_superlevel_and_pool
#print axioms pencilSuperlevel_johnson_on_Dzero
#print axioms erase_card_eq_sum_pencilFiber
#print axioms badFamily_card_eq_one_add_sum_pencilFiber
#print axioms badFamily_card_le_one_add_sum_superlevelCaps
#print axioms badFamily_card_le_one_add_sum_superlevelCaps_of_data
#print axioms badFamily_card_le_one_add_sum_poolSuperlevelCaps
#print axioms sum_uniformSmallPoolCap_le
#print axioms badFamily_card_le_N_of_uniformSmallPoolCaps
#print axioms levelZero_correlated_gap
#print axioms levelOne_even_correlated_gap
#print axioms levelOne_odd_correlated_gap
#print axioms levelTwo_modThree_correlated_gap
#print axioms card_lt_of_johnson_core_gap
#print axioms pencilSuperlevel_card_lt_of_gap
#print axioms levelZero_superlevel_card_le_657668325
#print axioms levelOne_superlevel_card_le_seven
#print axioms levelTwo_superlevel_card_le_five
#print axioms uniformSmallPool_superlevel_caps
#print axioms smallPoolClosure_proved
#print axioms predecessor_budget_of_stall_after_layerCake
