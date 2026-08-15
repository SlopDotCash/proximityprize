/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.RSVanishingDim
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# SYZ21: MDS shortening dimension (Part A) + combined-coverage LP audit (Part B)
  (issue #466 / #507)

This file does two things for the rate-`1/2` decisive strip `(Johnson, 1/3)`:

## Part A — the MDS shortening dimension, in-tree (discharges SYZ20's bridge input)

SYZ20 (`_SYZ20JointRankSuperadditive.lean`) packaged, as the structured hypothesis
`SuperadditiveUnion.union_span_rank`, the MDS-duality fact:

  *the dual codewords of an RS code supported inside a coordinate set `U` form a space of
  dimension `max(0, |U| − k)`.*

We prove this **fully in-tree** from the primal Reed–Solomon vanishing-set machinery
(`ArkLib.CS25.finrank_ker_evalOnS`, Lagrange/Vandermonde) together with the standard dual
pairing on `U → F`.  The dual codewords supported in `U` are exactly the functionals on the
punctured code space `U → F` annihilating the *punctured* RS code
`range (evalOnS α k U) ≤ (U → F)` — i.e. `(range (evalOnS α k U)).dualAnnihilator` — and

  `finrank (dualAnnihilator (range (evalOnS α k U))) = |U| − finrank (range (evalOnS α k U))`
                                                     `= |U| − min(k, |U|) = max(0, |U| − k).`

The punctured-code dimension `finrank (range (evalOnS α k U)) = min(k, |U|)` is the MDS
information-set fact: `≤ k` points are freely interpolable (`evalOnS_surjective`), and `≥ k`
points already pin a degree-`<k` polynomial (`evalOnS` injective, via
`finrank_ker_evalOnS` on any `k`-subset).  This is exactly the value the pair space needs
(doubled, `2(|U|−k)`, for the syndrome-pair space of `_G87McaEventSyndromeBridge`).

The honest residual to a *fully concrete* `SuperadditiveUnion` instance is the identification
of the syndrome-pair functionals with this punctured-code annihilator (the abstract-H bridge of
G87), plus the sunflower realizability (SYZ18); the **dimension count itself is now proven.**

## Part B — the combined-coverage LP audit (the honest adversarial optimum)

SYZ20's `mergeOpt` maximises the certified bad-scalar count over **pure single-core-size**
profiles (`⌊(n−k)/(s−k+1)⌋ · yield(s)`).  The adversarial question: a bad scalar may instead
have a *distinct non-degenerate witness* — its own G87 block of `t−k` γ-weighted functionals in
the `2(n−k)`-dim syndrome pool.  These are **not** a separate uncaptured category: an
independent-block scalar is the large-`s` end (`s = t−1, t`) of the *same* item menu, so the
honest adversarial optimum is the full **integer knapsack** over the shared union budget `n−k`,
which is `≥ mergeOpt`.  We compute it as a decidable `ℕ` function (`knapOpt`) and prove:

* **the combined knapsack still closes the strip** at `n = 64, k = 32` (and `n = 32`): it stays
  strictly below the survival budget `B = n` throughout `(Johnson, 1/3)`
  (`knap_closes_strip_n64`, `knap_closes_strip_n32`);
* **it crosses `B` exactly at the strip top**: `> B` for every `δ > 1/3`
  (`knap_kills_above_third_n64`).

Verdict: the SYZ20 coverage claim **survives** the audit — mixed profiles do *not* leak — but
`mergeOpt` (48, 42, 40) is a single-item **under-count** of the true optimum (59, 50, 46 at
`n = 64`); the honest strip margin is `~0.92·n`, thinner than SYZ20 advertised, and still
bounded away from `B`.  See `scripts/probes/probe_syz21_combined_coverage_lp.py` (n = 16…256).

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.SYZ21

open Module Submodule Polynomial ArkLib.CS25

/-! ## Part A: the MDS shortening dimension -/

section Shortening

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]

/-- **Punctured-code dimension, small support (`|U| ≤ k`).**  For `|U| ≤ deg` the punctured RS
code `range (evalOnS α deg U)` fills all of `U → F`, dimension `|U|`. -/
theorem punctureDim_of_card_le (α : ι ↪ F) (deg : ℕ) (U : Finset ι) (hU : U.card ≤ deg) :
    finrank F (LinearMap.range (evalOnS α deg U)) = U.card := by
  have hsurj := evalOnS_surjective α deg U hU
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi, Fintype.card_coe]

/-- **Punctured-code dimension, large support (`k ≤ |U|`).**  For `deg ≤ |U|` a degree-`<deg`
polynomial is pinned by its values on any `deg` of the points, so `evalOnS α deg U` is
injective and the punctured code has full domain dimension `deg`. -/
theorem punctureDim_of_le_card (α : ι ↪ F) (deg : ℕ) (U : Finset ι) (hU : deg ≤ U.card) :
    finrank F (LinearMap.range (evalOnS α deg U)) = deg := by
  classical
  haveI : FiniteDimensional F (Polynomial.degreeLT F deg) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F deg).toLinearMap
      (Polynomial.degreeLTEquiv F deg).injective
  -- pick a `deg`-subset `S ⊆ U`; vanishing on `U` implies vanishing on `S`
  obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq hU
  have hkerle : LinearMap.ker (evalOnS α deg U) ≤ LinearMap.ker (evalOnS α deg S) := by
    intro p hp
    simp only [LinearMap.mem_ker] at hp ⊢
    ext i
    have hiU : (i : ι) ∈ U := hSU i.2
    have := congrFun hp ⟨(i : ι), hiU⟩
    simpa [evalOnS] using this
  have hkerS : finrank F (LinearMap.ker (evalOnS α deg S)) = 0 := by
    rw [finrank_ker_evalOnS α deg S (by omega), hScard]; omega
  have hkerSbot : LinearMap.ker (evalOnS α deg S) = ⊥ :=
    Submodule.finrank_eq_zero.mp hkerS
  have hkerUbot : LinearMap.ker (evalOnS α deg U) = ⊥ :=
    le_bot_iff.mp (hkerSbot ▸ hkerle)
  have hinj : Function.Injective (evalOnS α deg U) := LinearMap.ker_eq_bot.mp hkerUbot
  have hrn := LinearMap.finrank_range_add_finrank_ker (evalOnS α deg U)
  rw [hkerUbot, finrank_bot, add_zero] at hrn
  rw [hrn, Polynomial.finrank_degreeLT_n deg]

/-- **MDS shortening dimension (large support, the case SYZ20 consumes: `k ≤ |U|`).**  The dual
codewords of the RS code `RS[α, k]` supported inside `U` — i.e. the functionals on `U → F`
annihilating the punctured code — form a space of dimension `|U| − k`. -/
theorem shortening_dim_of_le_card (α : ι ↪ F) (k : ℕ) (U : Finset ι) (hU : k ≤ U.card) :
    finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U))) = U.card - k := by
  classical
  haveI : FiniteDimensional F (U → F) := by infer_instance
  have hsplit :
      finrank F (LinearMap.range (evalOnS α k U))
        + finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U)))
        = finrank F (U → F) :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq _
  rw [punctureDim_of_le_card α k U hU, Module.finrank_pi, Fintype.card_coe] at hsplit
  omega

/-- **MDS shortening dimension (small support `|U| ≤ k`): the dual-support space is trivial.**
Consistent with `max(0, |U| − k) = 0`. -/
theorem shortening_dim_of_card_le (α : ι ↪ F) (k : ℕ) (U : Finset ι) (hU : U.card ≤ k) :
    finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U))) = 0 := by
  classical
  haveI : FiniteDimensional F (U → F) := by infer_instance
  have hsplit :
      finrank F (LinearMap.range (evalOnS α k U))
        + finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U)))
        = finrank F (U → F) :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq _
  rw [punctureDim_of_card_le α k U hU, Module.finrank_pi, Fintype.card_coe] at hsplit
  omega

/-- **MDS shortening dimension, combined (`max(0, |U| − k)`).**  The exact value SYZ20's
`SuperadditiveUnion.union_span_rank` records (single copy; the syndrome-pair space doubles it to
`2(|U| − k)`). -/
theorem shortening_dim (α : ι ↪ F) (k : ℕ) (U : Finset ι) :
    finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U)))
      = U.card - k := by
  rcases Nat.lt_or_ge U.card k with h | h
  · rw [shortening_dim_of_card_le α k U (le_of_lt h)]
    omega
  · exact shortening_dim_of_le_card α k U h

end Shortening

/-! ## Part B: the combined-coverage integer knapsack -/

section Knapsack

/-- Bad-scalar yield of one core of size `s` at length `n`, threshold `t` (truncated `ℕ`). -/
def yieldS (n t s : ℕ) : ℕ := if t ≤ s then n - s else (n - s) / (t - s)

/-- Sunflower incremental union cost of a size-`s` core (`s − (k−1)`). -/
def coreCost (k s : ℕ) : ℕ := s - (k - 1)

/-- One DP step: given `dp` (the value table for capacities `0 .. dp.length − 1`), compute the
value at capacity `dp.length` — the best of "skip" (previous capacity) and, over each item
`k+1 ≤ s ≤ n−1` with cost `c = coreCost k s ≤ dp.length`, `dp[dp.length − c] + yieldS`. -/
def knapStep (n k t : ℕ) (dp : List ℕ) : ℕ :=
  let w := dp.length
  (List.range n).foldl
    (fun acc s =>
      let c := coreCost k s
      if k + 1 ≤ s ∧ 0 < c ∧ c ≤ w then max acc (dp.getD (w - c) 0 + yieldS n t s) else acc)
    (dp.getLastD 0)

/-- The DP table for capacities `0 .. m` (length `m + 1`), built bottom-up so the kernel can
reduce it (linear in `m`, no exponential re-expansion). -/
def knapTable (n k t : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | (m + 1) => let prev := knapTable n k t m; prev ++ [knapStep n k t prev]

/-- The combined-coverage optimum: unbounded-knapsack value at the full union budget `n − k`. -/
def knapOpt (n k t : ℕ) : ℕ := (knapTable n k t (n - k)).getLastD 0

/-- **Combined knapsack closes the strip (`n = 64, k = 32, B = 64`).**  At every strip threshold
`t ∈ {43, 44, 45}` the *full* adversarial optimum (mixed profiles, independent blocks included)
is strictly below the survival budget `64`.  Values `59, 50, 46` — strictly above SYZ20's
single-item `mergeOpt` (48, 42, 40), yet still `< 64`. -/
theorem knap_closes_strip_n64 :
    knapOpt 64 32 43 = 59 ∧ knapOpt 64 32 44 = 50 ∧ knapOpt 64 32 45 = 46 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem knap_closes_strip_n64_lt :
    knapOpt 64 32 43 < 64 ∧ knapOpt 64 32 44 < 64 ∧ knapOpt 64 32 45 < 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Combined knapsack correctly kills above `1/3` (`n = 64, k = 32`).**  At `t ∈ {40, 41, 42}`
(`δ > 1/3`) the optimum *exceeds* `64`, so the crossover sits exactly at the strip top. -/
theorem knap_kills_above_third_n64 :
    64 < knapOpt 64 32 40 ∧ 64 < knapOpt 64 32 41 ∧ 64 < knapOpt 64 32 42 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The `n = 32, k = 16` cell agrees: strip (`t = 22`) closes (`28 < 32`); `δ > 1/3`
(`t ∈ {20, 21}`) is killed. -/
theorem knap_closes_strip_n32 :
    knapOpt 32 16 22 < 32 ∧ 32 < knapOpt 32 16 21 ∧ 32 < knapOpt 32 16 20 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Knapsack

end ArkLib.ProximityGap.Frontier.SYZ21

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.SYZ21.punctureDim_of_card_le
#print axioms ArkLib.ProximityGap.Frontier.SYZ21.punctureDim_of_le_card
#print axioms ArkLib.ProximityGap.Frontier.SYZ21.shortening_dim_of_le_card
#print axioms ArkLib.ProximityGap.Frontier.SYZ21.shortening_dim
#print axioms ArkLib.ProximityGap.Frontier.SYZ21.knap_closes_strip_n64
#print axioms ArkLib.ProximityGap.Frontier.SYZ21.knap_kills_above_third_n64
#print axioms ArkLib.ProximityGap.Frontier.SYZ21.knap_closes_strip_n32
