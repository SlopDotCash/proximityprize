/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterFiberChebyshevRefinement

/-!
# Junk-slice ledger: the vote-decomposition theorem, the junk-forced rider
# count, and the calibrated NO-IMPROVEMENT of the five-pencil master

Issue #466, P1 rate-quarter — eleventh and final round of the 2026-07-11
session, composing `foreign_region_rider_energy` (fiber-Chebyshev round) with
the `FiveCoverForm` master budget (cluster-confinement round).

**The exact composition audit** (probe
`scripts/probes/probe_rate_quarter_p1_junk_slice.py`):

* A rider's votes decompose as (foreign-region votes: `≤ k−1` per region by the
  fiber cap) + (junk votes: globally disjoint).  The fiber constraint can force
  a lower rider cap only when the vote DEMAND exceeds the total foreign fiber
  capacity:
  - five-cover geometry (4 foreign regions): capacity `4(k−1) = 1073741820 ≥ T`
    — fiber caps alone host ANY sub-`T` demand: never forcing
    (`fiveCover_fiber_capacity`);
  - two-capacity-region geometry: forcing needs margin `> 2(k−1)`, i.e.
    alignment `A < T − 2(k−1) = 55924056` — **below the pair-pencil floor
    `2T − N = 111848108`**: the crossover range is EMPTY for
    pair-pencil-generated families (`two_region_crossover_empty`);
  - the master's margin demand is `13`, seven orders below the fiber cap
    (`master_margin_no_improvement`).
* Probe: the census's extremal dual family's 230 riders each take exactly ONE
  foreign vote and ZERO junk votes — the quadratic constraint is nowhere near
  binding in practice.

**VERDICT (honest): the composition does NOT improve the five-pencil master
ledger** — no margin hypothesis weakens, no cap shrinks.  The round's real
content, kernel-landed:

* `vote_decomposition_two_regions` — a non-exceptional rider's vote set
  satisfies `#votes ≤ 2(k−1) + #(votes outside both capacity regions)`: the
  exact own/foreign/junk decomposition.
* `junk_forced_riders` — the conditional improvement in the (empty-for-
  pair-pencils, stated for completeness) high-demand regime: a margined pencil
  with margin `b` whose riders are non-exceptional w.r.t. both capacity pencils
  satisfies `#riders · (b − 2(k−1)) ≤ #(complement of the capacity regions)` —
  binding only when `b > 2(k−1)`.
* The calibration rungs above.

**Honesty**: nothing about `SwarmResidual`, the stall band, the master ledger,
or δ* changes; the bracket `3/8 ≤ δ* ≤ 43/96 + ε` is untouched.  This closes
the lane for the session (arc retrospective in the kb note).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterJunkSliceLedger

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap
open ArkLib.ProximityGap.Frontier.P1RateQuarterFiberChebyshevRefinement

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The vote decomposition -/

section Decomposition

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)

/-- **Vote decomposition over two capacity regions**: a rider `γ` of pencil
`(wa₀, wa₁)`, non-exceptional w.r.t. both capacity pencils `(wp₀, wp₁)` and
`(wq₀, wq₁)`, has at most `2(k−1)` votes inside the two capacity regions —
everything else must be junk:
`#votes ≤ 2(k−1) + #(votes \ (A_p ∪ A_q))`. -/
theorem vote_decomposition_two_regions
    {wa₀ wa₁ wp₀ wp₁ wq₀ wq₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwp₀ : wp₀ ∈ predecessorCode dom) (hwp₁ : wp₁ ∈ predecessorCode dom)
    (hwq₀ : wq₀ ∈ predecessorCode dom) (hwq₁ : wq₁ ∈ predecessorCode dom)
    (γ : F)
    (hexcp : (wp₀ - wa₀) + γ • (wp₁ - wa₁) ≠ 0)
    (hexcq : (wq₀ - wa₀) + γ • (wq₁ - wa₁) ≠ 0) :
    (voteSet u₀ u₁ wa₀ wa₁ γ).card ≤ 2 * (k - 1) +
      (voteSet u₀ u₁ wa₀ wa₁ γ \
        (alignedSet u₀ u₁ wp₀ wp₁ ∪ alignedSet u₀ u₁ wq₀ wq₁)).card := by
  classical
  set Vγ := voteSet u₀ u₁ wa₀ wa₁ γ with hV
  set Ap := alignedSet u₀ u₁ wp₀ wp₁ with hAp
  set Aq := alignedSet u₀ u₁ wq₀ wq₁ with hAq
  have hsub : Vγ ⊆ ((Vγ ∩ Ap) ∪ (Vγ ∩ Aq)) ∪ (Vγ \ (Ap ∪ Aq)) := by
    intro i hi
    by_cases hp : i ∈ Ap
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hp⟩))
    · by_cases hq : i ∈ Aq
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hq⟩))
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, ?_⟩)
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hp h
        · exact hq h
  have hp' : (Vγ ∩ Ap).card ≤ k - 1 :=
    foreign_vote_fiber_le dom u₀ u₁ hwa₀ hwa₁ hwp₀ hwp₁ γ hexcp
  have hq' : (Vγ ∩ Aq).card ≤ k - 1 :=
    foreign_vote_fiber_le dom u₀ u₁ hwa₀ hwa₁ hwq₀ hwq₁ γ hexcq
  calc Vγ.card ≤ (((Vγ ∩ Ap) ∪ (Vγ ∩ Aq)) ∪ (Vγ \ (Ap ∪ Aq))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Vγ ∩ Ap) ∪ (Vγ ∩ Aq)).card + (Vγ \ (Ap ∪ Aq)).card :=
        Finset.card_union_le _ _
    _ ≤ ((Vγ ∩ Ap).card + (Vγ ∩ Aq).card) + (Vγ \ (Ap ∪ Aq)).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 2 * (k - 1) + (Vγ \ (Ap ∪ Aq)).card := by omega

/-- **Junk-forced rider count** (the conditional improvement, binding only when
the margin exceeds `2(k−1)` — an EMPTY range for pair-pencil families, see the
calibration rungs): riders of a pencil with alignment `A` (margin `b = T − A`),
all non-exceptional w.r.t. the two capacity pencils, satisfy
`#riders · (b − 2(k−1)) ≤ #(univ \ (A_p ∪ A_q))`. -/
theorem junk_forced_riders
    {wa₀ wa₁ wp₀ wp₁ wq₀ wq₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwp₀ : wp₀ ∈ predecessorCode dom) (hwp₁ : wp₁ ∈ predecessorCode dom)
    (hwq₀ : wq₀ ∈ predecessorCode dom) (hwq₁ : wq₁ ∈ predecessorCode dom)
    (S : Finset F) (Sf : F → Finset (Fin N))
    (hrides : RidesAll dom u₀ u₁ wa₀ wa₁ S Sf)
    (hexc : ∀ γ ∈ S, (wp₀ - wa₀) + γ • (wp₁ - wa₁) ≠ 0 ∧
      (wq₀ - wa₀) + γ • (wq₁ - wa₁) ≠ 0) :
    S.card * (predecessorThreshold - (alignedSet u₀ u₁ wa₀ wa₁).card
        - 2 * (k - 1)) ≤
      (Finset.univ \
        (alignedSet u₀ u₁ wp₀ wp₁ ∪ alignedSet u₀ u₁ wq₀ wq₁)).card := by
  classical
  set A := (alignedSet u₀ u₁ wa₀ wa₁).card with hA
  set Cpl := Finset.univ \
    (alignedSet u₀ u₁ wp₀ wp₁ ∪ alignedSet u₀ u₁ wq₀ wq₁) with hCpl
  set b := predecessorThreshold - A with hb
  -- each rider has ≥ b votes, of which ≥ b − 2(k−1) are junk
  have hjunk : ∀ γ ∈ S, b - 2 * (k - 1) ≤
      (voteSet u₀ u₁ wa₀ wa₁ γ ∩ Cpl).card := by
    intro γ hγ
    obtain ⟨hcard, hagree, _⟩ := hrides γ hγ
    have hvotes : b ≤ (voteSet u₀ u₁ wa₀ wa₁ γ).card := by
      have hsub := witness_subset_aligned_union_votes u₀ u₁ wa₀ wa₁ hagree
      have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    have hdec := vote_decomposition_two_regions dom u₀ u₁
      hwa₀ hwa₁ hwp₀ hwp₁ hwq₀ hwq₁ γ (hexc γ hγ).1 (hexc γ hγ).2
    have heq : voteSet u₀ u₁ wa₀ wa₁ γ \
        (alignedSet u₀ u₁ wp₀ wp₁ ∪ alignedSet u₀ u₁ wq₀ wq₁) =
        voteSet u₀ u₁ wa₀ wa₁ γ ∩ Cpl := by
      rw [hCpl]
      ext i
      simp [Finset.mem_sdiff, Finset.mem_inter]
    rw [heq] at hdec
    omega
  -- junk vote sets are disjoint across riders and live in the complement
  have hdisj : ∀ γ ∈ S, ∀ γ' ∈ S, γ ≠ γ' →
      Disjoint (voteSet u₀ u₁ wa₀ wa₁ γ ∩ Cpl)
        (voteSet u₀ u₁ wa₀ wa₁ γ' ∩ Cpl) := by
    intro γ _ γ' _ hne
    exact Finset.disjoint_left.mpr fun i hi hi' =>
      (Finset.disjoint_left.mp (voteSet_disjoint u₀ u₁ wa₀ wa₁ hne))
        (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi').1
  calc S.card * (b - 2 * (k - 1))
      = ∑ _γ ∈ S, (b - 2 * (k - 1)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ S, (voteSet u₀ u₁ wa₀ wa₁ γ ∩ Cpl).card :=
        Finset.sum_le_sum hjunk
    _ = (S.biUnion (fun γ => voteSet u₀ u₁ wa₀ wa₁ γ ∩ Cpl)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Cpl.card := Finset.card_le_card (by
        intro i hi
        obtain ⟨γ, _, hiγ⟩ := Finset.mem_biUnion.mp hi
        exact (Finset.mem_inter.mp hiγ).2)

end Decomposition

/-! ## The calibration: where the composition binds — and that it never does
for the master -/

/-- **Five-cover fiber capacity exceeds every demand**: with four foreign
regions, the fiber caps alone can host any sub-`T` vote demand —
`T = 592794966 ≤ 4(k−1) = 1073741820`.  The composition never forces anything
in the five-pencil master geometry. -/
theorem fiveCover_fiber_capacity : predecessorThreshold ≤ 4 * (k - 1) := by
  norm_num [predecessorThreshold_eq, k]

/-- **The two-region crossover range is empty for pair-pencil families**:
forcing needs alignment `A < T − 2(k−1) = 55924056`, but every pair-pencil has
`A ≥ 2T − N = 111848108`. -/
theorem two_region_crossover_empty :
    predecessorThreshold - 2 * (k - 1) = 55924056 ∧
    2 * predecessorThreshold - N = 111848108 ∧
    (55924056 : ℕ) < 111848108 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- The master's margin demand (`13`) is seven orders of magnitude below the
fiber cap `k − 1`: the margin-13 rider caps of the five-pencil master cannot be
improved by the fiber-Chebyshev mechanism. -/
theorem master_margin_no_improvement : (13 : ℕ) < k - 1 ∧ k - 1 = 268435455 := by
  constructor <;> norm_num [k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterJunkSliceLedger

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterJunkSliceLedger

#print axioms vote_decomposition_two_regions
#print axioms junk_forced_riders
#print axioms fiveCover_fiber_capacity
#print axioms two_region_crossover_empty
#print axioms master_margin_no_improvement
