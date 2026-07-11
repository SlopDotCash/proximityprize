/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilCountCharge
import ArkLib.Data.CodingTheory.ProximityGap.ScaleBracketFull

/-!
# The layer-cake budget: the pure counting surface is exhausted

Closing file of the P1 pencil arc.  Per base scalar, `#bad − 1` splits into pencil fibers;
each pencil with `φ` riders has alignment `A ≥ ⌈(φT−N)/(φ−1)⌉` (alignment ladder) and fiber
`≤ (N−T)/(T−A)` (vote bound); distinct pencils' aligned regions pairwise intersect in `< k`
coordinates.  This file assembles the exact layer-cake and settles what counting can and
cannot do.

**Johnson layer counts (proved):** the aligned regions form a Johnson-packable family — the
precise object bounded is the family of *pencil pairs* `(w₀, w₁)`, packed through their
aligned sets `{i : w₀ i = u₀ i ∧ w₁ i = u₁ i}`, with the `< k` pairwise-intersection
property coming from `predecessor_sep` (`alignedSet_inter_card_lt_k`).  For any alignment
level `a` with `a² > N(k−1)` the family count obeys the exact-diagonal Johnson bound
(`alignedFamily_johnson`, via `R15Bracket.johnson_core`).  Instantiated:

* at the ten-rider ladder floor `a = 539356427`: at most `108` pencils
  (`tenRiderLevel_family_card_le`);
* at `a = T − 1 = 592794965`: at most `5` pencils (`thresholdLevel_family_card_le`) — the
  same `5` as the classical threshold joint list.

**Light side (proved):** pencils aligned at or below the Johnson threshold
`⌊√(N(k−1))⌋ = 536870910` carry at most **nine** riders (`subJohnson_riders_le_nine`), but
*no assembled constraint bounds their number* — the two- and three-pencil families landed at
literal P1 in the previous files are of exactly this kind.

**Verdict (proved arithmetic):** counting admits over-budget.  Three pencils at alignment
`T − 1` with full fibers `N − T` satisfy the Johnson count (`J(T−1) = 5 ≥ 3`), the
aligned-region packing (`3(T−1) ≤ N + 3(k−1)`), and the vote bounds, while carrying
`1 + 3(N−T) = 1442840575 > N` bad scalars (`counting_admits_three_heavy_overBudget`).  The
greedy heavy-side layer-cake maximum is `2404735416 > 2N` (probe, info only).

**Honest closing statement:** the pure counting surface — vote partition, alignment ladder,
rider caps, Johnson packing of aligned regions, fiber partition, triple-overlap caps,
four-witness pigeonhole — is EXHAUSTED: it proves the exact per-pencil and per-level caps
above but cannot exclude over-budget.  The minimal open statement for the predecessor pin
through this branch is an **RS-algebraic exclusion of three near-threshold-aligned pencils
through one base point** (three joint pairs, each agreeing with the stack on `~T−1`
coordinates, pairwise sharing `< k`, all passing through the base witness codeword — the
aligned regions must two-cover `3(T−1) − N = 704643071` of at most `3(k−1) = 805306365`
allowed pairwise-overlap coordinates, an `87.5%`-saturated window).  The alternative is the
previously landed structured-floor route (`PredecessorStructuredFloorResidual`).

Executable certificate: `scripts/probes/probe_rate_quarter_p1_layer_cake.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterLayerCakeBudget

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ProximityGap.SharedFreshPencil

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-- Subtraction-free exact-diagonal Johnson rearranges to the sharp natural-number
denominator (local copy of the standard step). -/
theorem johnson_core_to_subtracted {L n a p : ℕ}
    (hap : p ≤ a) (hgap : n * p ≤ a ^ 2)
    (hcore : L * a ^ 2 + n * p ≤ n * a + L * (n * p)) :
    L * (a ^ 2 - n * p) ≤ n * (a - p) := by
  have hleft : L * a ^ 2 = L * (a ^ 2 - n * p) + L * (n * p) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hgap]
  have hright : n * a = n * (a - p) + n * p := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hap]
  omega

/-! ## Johnson packing of pencil aligned regions

The packed objects are the pencil PAIRS `(w₀, w₁)` themselves; the packing sets are their
aligned regions.  Pairwise `< k` intersections come from `predecessor_sep`. -/

/-- **Aligned-family Johnson bound** at level `a` (subtraction-free form). -/
theorem alignedFamily_johnson (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (Fam : Finset ((Fin N → F) × (Fin N → F))) (a : ℕ)
    (hmem : ∀ π ∈ Fam, π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom)
    (halign : ∀ π ∈ Fam, a ≤ (alignedSet u₀ u₁ π.1 π.2).card)
    (hap : k - 1 ≤ a) (hgap : N * (k - 1) ≤ a ^ 2) :
    Fam.card * (a ^ 2 - N * (k - 1)) ≤ N * (a - (k - 1)) := by
  classical
  have hpair : ∀ π ∈ Fam, ∀ π' ∈ Fam, π ≠ π' →
      ((alignedSet u₀ u₁ π.1 π.2) ∩ (alignedSet u₀ u₁ π'.1 π'.2)).card ≤ k - 1 := by
    intro π hπ π' hπ' hne
    exact alignedSet_inter_card_lt_k dom u₀ u₁
      (hmem π hπ).1 (hmem π hπ).2 (hmem π' hπ').1 (hmem π' hπ').2
      (by
        intro h
        exact hne (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)))
  have hcore := R15Bracket.johnson_core Fam
    (fun π => alignedSet u₀ u₁ π.1 π.2) a (k - 1) halign hpair hap
  simp only [Fintype.card_fin] at hcore
  exact johnson_core_to_subtracted hap hgap hcore

/-- Exact ratio at the ten-rider ladder floor. -/
theorem tenRiderLevel_ratio_eq :
    N * (539356427 - (k - 1)) / (539356427 ^ 2 - N * (k - 1)) = 108 := by
  norm_num [N, k]

/-- **At most `108` pencils at the ten-rider alignment floor.** -/
theorem tenRiderLevel_family_card_le (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (Fam : Finset ((Fin N → F) × (Fin N → F)))
    (hmem : ∀ π ∈ Fam, π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom)
    (halign : ∀ π ∈ Fam, 539356427 ≤ (alignedSet u₀ u₁ π.1 π.2).card) :
    Fam.card ≤ 108 := by
  have hsub := alignedFamily_johnson dom u₀ u₁ Fam 539356427 hmem halign
    (by norm_num [k]) (by norm_num [N, k])
  have hden : 0 < 539356427 ^ 2 - N * (k - 1) := by norm_num [N, k]
  calc Fam.card ≤ N * (539356427 - (k - 1)) / (539356427 ^ 2 - N * (k - 1)) :=
        (Nat.le_div_iff_mul_le hden).2 hsub
    _ = 108 := tenRiderLevel_ratio_eq

/-- Exact ratio at alignment `T − 1`. -/
theorem thresholdLevel_ratio_eq :
    N * (592794965 - (k - 1)) / (592794965 ^ 2 - N * (k - 1)) = 5 := by
  norm_num [N, k]

/-- **At most `5` pencils at alignment `T − 1`** — the classical threshold-list five. -/
theorem thresholdLevel_family_card_le (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (Fam : Finset ((Fin N → F) × (Fin N → F)))
    (hmem : ∀ π ∈ Fam, π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom)
    (halign : ∀ π ∈ Fam, 592794965 ≤ (alignedSet u₀ u₁ π.1 π.2).card) :
    Fam.card ≤ 5 := by
  have hsub := alignedFamily_johnson dom u₀ u₁ Fam 592794965 hmem halign
    (by norm_num [k]) (by norm_num [N, k])
  have hden : 0 < 592794965 ^ 2 - N * (k - 1) := by norm_num [N, k]
  calc Fam.card ≤ N * (592794965 - (k - 1)) / (592794965 ^ 2 - N * (k - 1)) :=
        (Nat.le_div_iff_mul_le hden).2 hsub
    _ = 5 := thresholdLevel_ratio_eq

/-! ## The light side: sub-Johnson pencils carry at most nine riders -/

/-- The Johnson threshold: `536870910 = ⌊√(N(k−1))⌋`. -/
theorem johnson_threshold_squares :
    536870910 ^ 2 ≤ N * (k - 1) ∧ N * (k - 1) < 536870911 ^ 2 := by
  constructor <;> norm_num [N, k]

/-- **Sub-Johnson pencils carry at most nine riders** (fiber `≤ 8`). -/
theorem subJohnson_riders_le_nine (dom : Fin N ↪ F) (u₀ u₁ w₀ w₁ : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf)
    (hA : (alignedSet u₀ u₁ w₀ w₁).card ≤ 536870910) :
    R.card ≤ 9 := by
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hAT : (alignedSet u₀ u₁ w₀ w₁).card ≤ predecessorThreshold := by omega
  have hstep := riders_pred_mul_le dom u₀ u₁ w₀ w₁ R Sf h hAT
  have hTA : 55924056 ≤ predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card := by
    omega
  have hmul : (R.card - 1) * 55924056 ≤
      (R.card - 1) * (predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card) :=
    Nat.mul_le_mul_left _ hTA
  omega

/-! ## The verdict: counting admits over-budget -/

/-- **The assembled counting constraints admit a three-pencil over-budget configuration.**
Three pencils at alignment `T − 1` pass the Johnson count (`5 ≥ 3`), fit the aligned-region
packing, and their full fibers `N − T` overshoot the prize budget.  The pure counting surface
therefore cannot prove `#bad ≤ N`; the minimal open statement is the RS-algebraic exclusion
of such near-threshold pencil triples through one base point. -/
theorem counting_admits_three_heavy_overBudget :
    3 * ((predecessorThreshold - 1) ^ 2 - N * (k - 1)) ≤
      N * ((predecessorThreshold - 1) - (k - 1)) ∧
    3 * (predecessorThreshold - 1) ≤ N + 3 * (k - 1) ∧
    N < 1 + 3 * (N - predecessorThreshold) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- The two-cover saturation window of the hypothetical triple: the three aligned regions
must pairwise-overlap `3(T−1) − N = 704643071` coordinates out of at most
`3(k−1) = 805306365` allowed — an `87.5%`-saturated window, the concrete algebraic target. -/
theorem three_heavy_twoCover_window :
    3 * (predecessorThreshold - 1) - N = 704643071 ∧
    3 * (k - 1) = 805306365 := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterLayerCakeBudget

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterLayerCakeBudget

#print axioms johnson_core_to_subtracted
#print axioms alignedFamily_johnson
#print axioms tenRiderLevel_family_card_le
#print axioms thresholdLevel_family_card_le
#print axioms johnson_threshold_squares
#print axioms subJohnson_riders_le_nine
#print axioms counting_admits_three_heavy_overBudget
#print axioms three_heavy_twoCover_window
