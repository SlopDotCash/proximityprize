/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilCountCharge

/-!
# The global `u₁`-consistency charge: the heavy three-pencil over-budget is CLOSED

Successor of `_P1RateQuarterLayerCakeBudget` (which proved the per-pencil counting surface
admits a three-heavy over-budget) and `_P1RateQuarterTwoCoverWindow` (which realized the
three-pencil aligned-region geometry).  This file adds the **cross-pencil global constraint**
that the per-pencil ledger could not see, and it closes the heavy window.

**The key identity.**  Fix the stack `(u₀, u₁)`, a base scalar `γ₀`, and its base witness
codeword `p₀`.  Every pencil `(w₀, w₁)` through the base satisfies `w₀ + γ₀·w₁ = p₀`.  Define
the single global function

  `D := p₀ − u₀ − γ₀·u₁`.

Then for every pencil through the base:

* the aligned region is exactly `{D = 0} ∩ {w₁ = u₁}` — in particular **every aligned region
  of every pencil through the base sinks into the one zero-set `{D = 0}`**
  (`alignedSet_subset_Dzero`); and
* every vote of every rider `γ ≠ γ₀` lies in the **support** `{D ≠ 0}`
  (`voteSet_subset_Dsupport`): at a vote coordinate, `D(i) + (γ−γ₀)·(w₁(i)−u₁(i)) = 0`, so
  `D(i) = 0` would force alignment.

So all pencils through one base scalar draw their rider votes from a SHARED pool of
`F = N − |{D = 0}|` coordinates, while their aligned regions jointly inflate `|{D = 0}|`.
This is the global `u₁`-consistency obstruction: dense alignment (which the two-cover window
realizes) and dense rider population (which over-budget demands) compete for the same
coordinates through the single function `D`.

**The closure** (`three_heavy_riders_budget`): three pencils through one base with aligned
regions of size `T − 1` and pairwise `< k` overlaps (the exact configuration that
`counting_admits_three_heavy_overBudget` could not exclude) have
`|{D = 0}| ≥ 3(T−1) − 3(k−1) = 973078530`, hence a shared vote pool
`F ≤ 100663294`, hence **total riders `≤ 3F = 301989882` and
`#bad ≤ 1 + 301989882 = 301989883 ≤ N`** — a factor `3.6` below budget.  The layer-cake
verdict "counting admits over-budget" is overturned on the heavy side.

**Degenerate corollary** (`base_row_stack_carries_no_riders`): the realized two-cover
geometry (stack first row equal to the shared base codeword, `γ₀ = 0`) has `D ≡ 0`, so it
carries **no riders at all** — geometric realizability and rider-population realizability are
now formally separated.

**What remains open** (`GlobalConsistencySwarmResidual`, honest named Prop): sub-Johnson
pencil swarms.  A pencil at alignment `A` needs `T − A ≤ F` votes per rider, so with the
heavy pool `F` all pencils below alignment `T − F` are sterile; but families of
single-rider pencils at alignment in `[T−F, ⌊√(N(k−1))⌋]` are not counted by any surface in
this arc.  Their structure is pinned: a single-rider pencil for rider `γ` has
`w₁ = u₁ − D/(γ−γ₀)` on ALL of `{D ≠ 0}` (interpolable since `F < k`), i.e. the swarm is an
affine pencil of stacks `s ↦ u₁ − s·D` — the SAME correlated-agreement shape one level down
(`N' = N − F`, `T' = T − F`, same `k`), sitting again just below the Johnson radius of the
shrunken parameters.  See the kb note for the recursion arithmetic.

Executable check: `scripts/probes/probe_rate_quarter_p1_global_consistency.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The global function `D` and its support -/

section GlobalD

variable (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)

/-- The base-discrepancy function `D = p₀ − u₀ − γ₀·u₁`: the failure of the stack's
`γ₀`-line to match the base witness. -/
noncomputable def Dfun : Fin N → F := fun i => p₀ i - u₀ i - γ₀ * u₁ i

/-- The support `{D ≠ 0}`: the shared rider-vote pool of ALL pencils through the base. -/
noncomputable def Dsupport : Finset (Fin N) :=
  Finset.univ.filter (fun i => Dfun u₀ u₁ p₀ γ₀ i ≠ 0)

/-- The zero set `{D = 0}`: the shared alignment sink. -/
noncomputable def Dzero : Finset (Fin N) :=
  Finset.univ.filter (fun i => Dfun u₀ u₁ p₀ γ₀ i = 0)

theorem mem_Dsupport_iff (i : Fin N) :
    i ∈ Dsupport u₀ u₁ p₀ γ₀ ↔ Dfun u₀ u₁ p₀ γ₀ i ≠ 0 := by
  rw [Dsupport, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

theorem mem_Dzero_iff (i : Fin N) :
    i ∈ Dzero u₀ u₁ p₀ γ₀ ↔ Dfun u₀ u₁ p₀ γ₀ i = 0 := by
  rw [Dzero, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

/-- The pool and the sink partition the domain: `|{D≠0}| + |{D=0}| = N`. -/
theorem Dsupport_card_add_Dzero_card :
    (Dsupport u₀ u₁ p₀ γ₀).card + (Dzero u₀ u₁ p₀ γ₀).card = N := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N)))
    (p := fun i => Dfun u₀ u₁ p₀ γ₀ i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hswap : (Dsupport u₀ u₁ p₀ γ₀).card =
      (Finset.univ.filter (fun i => ¬ Dfun u₀ u₁ p₀ γ₀ i = 0)).card := by
    rfl
  rw [hswap, Dzero]
  omega

variable {w₀ w₁ : Fin N → F}

/-- **Alignment sink**: the aligned region of any pencil through the base lies in `{D = 0}`.
At an aligned coordinate both rows match the stack, so `D = (w₀ + γ₀w₁) − u₀ − γ₀u₁ = 0`. -/
theorem alignedSet_subset_Dzero (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i) :
    alignedSet u₀ u₁ w₀ w₁ ⊆ Dzero u₀ u₁ p₀ γ₀ := by
  intro i hi
  rw [mem_alignedSet_iff] at hi
  rw [mem_Dzero_iff, Dfun, ← hbase i, hi.1, hi.2]
  ring

/-- **Vote source**: every vote of every rider `γ ≠ γ₀` on any pencil through the base lies
in the shared pool `{D ≠ 0}`.  If `D(i) = 0`, the vote equation forces
`(γ − γ₀)(w₁(i) − u₁(i)) = 0`, hence alignment — contradiction. -/
theorem voteSet_subset_Dsupport (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i)
    {γ : F} (hγ : γ ≠ γ₀) :
    voteSet u₀ u₁ w₀ w₁ γ ⊆ Dsupport u₀ u₁ p₀ γ₀ := by
  intro i hi
  rw [mem_voteSet_iff] at hi
  obtain ⟨hnal, hline⟩ := hi
  rw [mem_Dsupport_iff]
  intro hD0
  apply hnal
  rw [mem_alignedSet_iff]
  -- D = 0 at i means the γ₀-lines match: w₀ i + γ₀ w₁ i = u₀ i + γ₀ u₁ i
  have hγ₀line : w₀ i + γ₀ * w₁ i = u₀ i + γ₀ * u₁ i := by
    have := hbase i
    rw [Dfun] at hD0
    have hp : p₀ i = u₀ i + γ₀ * u₁ i := by linear_combination hD0
    rw [this, hp]
  -- subtracting the two line equations kills the second row
  have hsub : (γ - γ₀) * (w₁ i - u₁ i) = 0 := by
    linear_combination hline - hγ₀line
  have h₁ : w₁ i = u₁ i := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hγ
    · exact sub_eq_zero.mp h
  refine ⟨?_, h₁⟩
  have := hline
  rw [h₁] at this
  exact add_right_cancel this

/-- **The global rider ledger**: riders of any pencil through the base draw
`riders · (T − A)` disjoint votes from the SHARED pool `{D ≠ 0}` — not from the pencil's own
complement.  This is the cross-pencil constraint the per-pencil vote bound could not see. -/
theorem riders_mul_le_Dsupport (dom : Fin N ↪ F) (R : Finset F) (Sf : F → Finset (Fin N))
    (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i)
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) (hγ₀R : γ₀ ∉ R) :
    R.card * (predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card) ≤
      (Dsupport u₀ u₁ p₀ γ₀).card := by
  classical
  set A := (alignedSet u₀ u₁ w₀ w₁).card with hA
  have hper : ∀ γ ∈ R, predecessorThreshold - A ≤ (voteSet u₀ u₁ w₀ w₁ γ).card := by
    intro γ hγ
    obtain ⟨hcard, hagree, _⟩ := h γ hγ
    have hsub := witness_subset_aligned_union_votes u₀ u₁ w₀ w₁ hagree
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hpool : R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ) ⊆
      Dsupport u₀ u₁ p₀ γ₀ := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, hγR, hiv⟩ := hi
    exact voteSet_subset_Dsupport u₀ u₁ p₀ γ₀ hbase
      (fun hh => hγ₀R (hh ▸ hγR)) hiv
  calc R.card * (predecessorThreshold - A)
      = ∑ _γ ∈ R, (predecessorThreshold - A) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ R, (voteSet u₀ u₁ w₀ w₁ γ).card := Finset.sum_le_sum hper
    _ = (R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ)).card :=
        (card_biUnion_votes u₀ u₁ w₀ w₁ R).symm
    _ ≤ (Dsupport u₀ u₁ p₀ γ₀).card := Finset.card_le_card hpool

end GlobalD

/-! ## Three-set union arithmetic -/

/-- Subtraction-free inclusion–exclusion lower bound for a triple union. -/
theorem card_add_three_le_union_add_pairs (A₁ A₂ A₃ : Finset (Fin N)) :
    A₁.card + A₂.card + A₃.card ≤
      (A₁ ∪ A₂ ∪ A₃).card + ((A₁ ∩ A₂).card + ((A₁ ∩ A₃).card + (A₂ ∩ A₃).card)) := by
  classical
  have h12 : (A₁ ∪ A₂).card + (A₁ ∩ A₂).card = A₁.card + A₂.card :=
    Finset.card_union_add_card_inter A₁ A₂
  have h123 : (A₁ ∪ A₂ ∪ A₃).card + ((A₁ ∪ A₂) ∩ A₃).card =
      (A₁ ∪ A₂).card + A₃.card :=
    Finset.card_union_add_card_inter (A₁ ∪ A₂) A₃
  have hdist : (A₁ ∪ A₂) ∩ A₃ = (A₁ ∩ A₃) ∪ (A₂ ∩ A₃) :=
    Finset.union_inter_distrib_right A₁ A₂ A₃
  have hle : ((A₁ ∪ A₂) ∩ A₃).card ≤ (A₁ ∩ A₃).card + (A₂ ∩ A₃).card := by
    rw [hdist]
    exact Finset.card_union_le _ _
  omega

/-! ## The heavy-window closure -/

/-- The closure numbers: `3(T−1) − 3(k−1) = 973078530`, pool `F ≤ 100663294`, and
`1 + 3F = 301989883 ≤ N` — a factor `3.55` below the budget. -/
theorem heavy_window_closure_numbers :
    3 * (predecessorThreshold - 1) - 3 * (k - 1) = 973078530 ∧
    N - 973078530 = 100663294 ∧
    1 + 3 * 100663294 ≤ N := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- **The heavy three-pencil over-budget is CLOSED.**  Three pairwise-distinct pencils
through one base witness (`w₀ⱼ + γ₀·w₁ⱼ = p₀`), all with aligned regions of the window size
`T − 1`, have their aligned regions jointly sunk in `{D = 0}` (cardinality
`≥ 3(T−1) − 3(k−1) = 973078530`), so the shared rider-vote pool has at most `100663294`
coordinates and the three fibers total at most `301989882` riders:
`#bad ≤ 1 + 301989882 = 301989883 ≤ N`.  The configuration that
`counting_admits_three_heavy_overBudget` showed the per-pencil surface cannot exclude is
excluded by the global charge. -/
theorem three_heavy_riders_budget (dom : Fin N ↪ F)
    (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)
    (w₀₁ w₁₁ w₀₂ w₁₂ w₀₃ w₁₃ : Fin N → F)
    (R₁ R₂ R₃ : Finset F) (Sf₁ Sf₂ Sf₃ : F → Finset (Fin N))
    -- codeword membership
    (hm₀₁ : w₀₁ ∈ predecessorCode dom) (hm₁₁ : w₁₁ ∈ predecessorCode dom)
    (hm₀₂ : w₀₂ ∈ predecessorCode dom) (hm₁₂ : w₁₂ ∈ predecessorCode dom)
    (hm₀₃ : w₀₃ ∈ predecessorCode dom) (hm₁₃ : w₁₃ ∈ predecessorCode dom)
    -- all through the base witness at γ₀
    (hb₁ : ∀ i, w₀₁ i + γ₀ * w₁₁ i = p₀ i)
    (hb₂ : ∀ i, w₀₂ i + γ₀ * w₁₂ i = p₀ i)
    (hb₃ : ∀ i, w₀₃ i + γ₀ * w₁₃ i = p₀ i)
    -- pairwise distinct pencils
    (hne₁₂ : (w₀₁, w₁₁) ≠ (w₀₂, w₁₂)) (hne₁₃ : (w₀₁, w₁₁) ≠ (w₀₃, w₁₃))
    (hne₂₃ : (w₀₂, w₁₂) ≠ (w₀₃, w₁₃))
    -- the heavy window: aligned regions of size exactly T − 1
    (hA₁ : (alignedSet u₀ u₁ w₀₁ w₁₁).card = predecessorThreshold - 1)
    (hA₂ : (alignedSet u₀ u₁ w₀₂ w₁₂).card = predecessorThreshold - 1)
    (hA₃ : (alignedSet u₀ u₁ w₀₃ w₁₃).card = predecessorThreshold - 1)
    -- rider families
    (hr₁ : RidesAll dom u₀ u₁ w₀₁ w₁₁ R₁ Sf₁) (hγ₁ : γ₀ ∉ R₁)
    (hr₂ : RidesAll dom u₀ u₁ w₀₂ w₁₂ R₂ Sf₂) (hγ₂ : γ₀ ∉ R₂)
    (hr₃ : RidesAll dom u₀ u₁ w₀₃ w₁₃ R₃ Sf₃) (hγ₃ : γ₀ ∉ R₃) :
    R₁.card + R₂.card + R₃.card ≤ 301989882 := by
  classical
  set A₁ := alignedSet u₀ u₁ w₀₁ w₁₁ with hA₁def
  set A₂ := alignedSet u₀ u₁ w₀₂ w₁₂ with hA₂def
  set A₃ := alignedSet u₀ u₁ w₀₃ w₁₃ with hA₃def
  -- pairwise aligned overlaps are < k
  have ho₁₂ : (A₁ ∩ A₂).card ≤ k - 1 :=
    alignedSet_inter_card_lt_k dom u₀ u₁ hm₀₁ hm₁₁ hm₀₂ hm₁₂ hne₁₂
  have ho₁₃ : (A₁ ∩ A₃).card ≤ k - 1 :=
    alignedSet_inter_card_lt_k dom u₀ u₁ hm₀₁ hm₁₁ hm₀₃ hm₁₃ hne₁₃
  have ho₂₃ : (A₂ ∩ A₃).card ≤ k - 1 :=
    alignedSet_inter_card_lt_k dom u₀ u₁ hm₀₂ hm₁₂ hm₀₃ hm₁₃ hne₂₃
  -- the union sinks into {D = 0}
  have hsink : A₁ ∪ A₂ ∪ A₃ ⊆ Dzero u₀ u₁ p₀ γ₀ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi' | hi₃
    · rcases Finset.mem_union.mp hi' with hi₁ | hi₂
      · exact alignedSet_subset_Dzero u₀ u₁ p₀ γ₀ hb₁ hi₁
      · exact alignedSet_subset_Dzero u₀ u₁ p₀ γ₀ hb₂ hi₂
    · exact alignedSet_subset_Dzero u₀ u₁ p₀ γ₀ hb₃ hi₃
  -- |{D=0}| ≥ 3(T−1) − 3(k−1) = 973078530
  have hunion := card_add_three_le_union_add_pairs A₁ A₂ A₃
  have hzero : 973078530 ≤ (Dzero u₀ u₁ p₀ γ₀).card := by
    have hle := Finset.card_le_card hsink
    have hT := predecessorThreshold_eq
    have hk : k = 268435456 := by norm_num [k]
    omega
  -- the shared pool is small
  have hpool : (Dsupport u₀ u₁ p₀ γ₀).card ≤ 100663294 := by
    have hpart := Dsupport_card_add_Dzero_card u₀ u₁ p₀ γ₀
    have hN : N = 1073741824 := by norm_num [N]
    omega
  -- each fiber is bounded by the pool (T − A = 1 at the window level)
  have hT := predecessorThreshold_eq
  have hstep₁ := riders_mul_le_Dsupport u₀ u₁ p₀ γ₀ dom R₁ Sf₁ hb₁ hr₁ hγ₁
  have hstep₂ := riders_mul_le_Dsupport u₀ u₁ p₀ γ₀ dom R₂ Sf₂ hb₂ hr₂ hγ₂
  have hstep₃ := riders_mul_le_Dsupport u₀ u₁ p₀ γ₀ dom R₃ Sf₃ hb₃ hr₃ hγ₃
  rw [← hA₁def, hA₁] at hstep₁
  rw [← hA₂def, hA₂] at hstep₂
  rw [← hA₃def, hA₃] at hstep₃
  have hone : predecessorThreshold - (predecessorThreshold - 1) = 1 := by omega
  rw [hone, mul_one] at hstep₁ hstep₂ hstep₃
  omega

/-! ## The degenerate corollary: the realized geometry carries no riders -/

/-- **Geometric vs population realizability, separated.**  If the stack's first row equals
the shared base row (`u₀ = w₀`, the realized two-cover configuration, base scalar `γ₀ = 0`
with `p₀ = u₀`), then `D ≡ 0`: the shared vote pool is EMPTY and any sub-threshold pencil
carries no riders other than the base scalar itself. -/
theorem base_row_stack_carries_no_riders (dom : Fin N ↪ F)
    (u₀ u₁ w₀ w₁ : Fin N → F) (R : Finset F) (Sf : F → Finset (Fin N))
    (hw : ∀ i, w₀ i = u₀ i)
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) (h0 : (0 : F) ∉ R)
    (hA : (alignedSet u₀ u₁ w₀ w₁).card < predecessorThreshold) :
    R = ∅ := by
  classical
  have hbase : ∀ i, w₀ i + (0 : F) * w₁ i = u₀ i := by
    intro i
    rw [hw i]
    ring
  have hD : ∀ i, Dfun u₀ u₁ u₀ (0 : F) i = 0 := by
    intro i
    rw [Dfun]
    ring
  have hsupp : (Dsupport u₀ u₁ u₀ (0 : F)).card = 0 := by
    rw [Finset.card_eq_zero]
    ext i
    rw [mem_Dsupport_iff]
    simp [hD i]
  have hstep := riders_mul_le_Dsupport u₀ u₁ u₀ (0 : F) dom R Sf hbase h h0
  rw [hsupp] at hstep
  have hpos : 0 < predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card := by omega
  rw [← Finset.card_eq_zero]
  have hz := Nat.le_zero.mp hstep
  rcases Nat.mul_eq_zero.mp hz with h' | h'
  · exact h'
  · omega

/-! ## The honest residual: sub-Johnson swarms -/

/-- **Named residual (OPEN): the sub-Johnson swarm budget.**  After this file the only
configurations escaping the counting surfaces are families of pencils through one base whose
alignments sit in `[T − F, ⌊√(N(k−1))⌋]` (below-Johnson, hence uncounted) with few riders
each, all drawing votes from the shared pool `{D ≠ 0}`.  Their forced structure is an affine
pencil of stacks `s ↦ u₁ − s·D` on the pool (one correlated-agreement instance at shrunken
parameters `N' = N − F`, `T' = T − F`, same `k`).  The residual asserts the budget for every
bad family — this is exactly the remaining content of the predecessor pin through the
counting branch. -/
def GlobalConsistencySwarmResidual (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F),
    BadFamilyData dom u₀ u₁ G Sf pf → G.card ≤ N

end ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge

#print axioms Dsupport_card_add_Dzero_card
#print axioms alignedSet_subset_Dzero
#print axioms voteSet_subset_Dsupport
#print axioms riders_mul_le_Dsupport
#print axioms card_add_three_le_union_add_pairs
#print axioms heavy_window_closure_numbers
#print axioms three_heavy_riders_budget
#print axioms base_row_stack_carries_no_riders
