/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueCapstone
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Door (iv) Lane-2 — the Shaw value `O(1)` predicate IS Mathlib's Landau `=O[atTop] 1`

The Shaw-value capstone (`ShawValueCapstone`) packages the prize reduction
`prize ⇔ Sh(n)=O(1)` using the predicate

  `ShawOOneOn q n M  :=  ∃ C ≥ 0, ∀ i, shawValue (q i) (n i) (M i) ≤ C`

i.e. "one absolute constant bounds the Shaw value over the whole family". That `∃`-uniform-constant
form is the *mathematically correct* reading of the prose slogan `Sh(n)=O(1)`, but it is stated in
elementary `∀/∃` language. A referee citing the capstone will expect the slogan in **Mathlib's
official Landau notation** `Asymptotics.IsBigO`. This file proves that the campaign's `ShawOOneOn`
predicate is *literally* the Landau statement

  `(fun i => shawValue (q i) (n i) (M i)) =O[atTop] (fun _ => (1 : ℝ))`

for an `ℕ`-indexed prize family, closing the notational gap between the campaign's elementary
predicate and the symbol a number theorist would write.

Two honest subtleties, both handled:

* `=O[atTop] 1` is an *eventual* (cofinite) bound; `ShawOOneOn` is a *global* `∀`-bound. Over `ℕ`
  the two coincide **only when `shawValue` is nonnegative on the family** (which it is in the prize
  regime, `M ≥ 0` and a positive scale), because then the finitely many small-index terms have a
  finite maximum that can be absorbed into the constant. We therefore state the full equivalence
  under a pointwise `0 ≤ shawValue` hypothesis, and give the unconditional forward implication
  (`ShawOOneOn → IsBigO`) separately.
* `IsBigO ... 1` is phrased through `‖·‖`. We discharge `‖shawValue ...‖ = shawValue ...` from the
  nonnegativity hypothesis.

Nothing here proves the open Gauss-period bound. It is a pure notation bridge for the citable
Lane-2 capstone: it asserts no new analytic estimate. CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Asymptotics Filter

namespace ProximityGap.Frontier.ShawValueCapstone

/-- The `ℕ`-indexed Shaw-value sequence of a prize family, as a function for Landau notation. -/
noncomputable def shawSeq (q n M : ℕ → ℝ) : ℕ → ℝ :=
  fun i => shawValue (q i) (n i) (M i)

/-- **Forward bridge.**  Under pointwise nonnegativity of the Shaw value (the prize regime), a global
uniform Shaw bound `Sh ≤ C` over the whole `ℕ` family is in particular a Landau `O(1)` bound: the
Shaw sequence is `=O[atTop] 1`.  (Nonnegativity is needed only to control the `‖·‖` lower side; without
it a value `≤ C` could still have large norm by being very negative.) -/
theorem shawSeq_isBigO_one_of_shawOOneOn {q n M : ℕ → ℝ}
    (hnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M i))
    (h : ShawOOneOn q n M) :
    (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨C, _hC, hbound⟩ := h
  rw [isBigO_one_iff]
  refine ⟨C, ?_⟩
  rw [eventually_map]
  filter_upwards with i
  -- `‖shawSeq i‖ = shawSeq i ≤ C` from nonnegativity and the global bound.
  rw [show ‖shawSeq q n M i‖ = shawSeq q n M i from abs_of_nonneg (hnn i)]
  exact hbound i

/-- **Backward bridge (needs nonnegativity).**  If the Shaw value is pointwise nonnegative on the
family (the prize-regime situation `M ≥ 0`, positive scale), then a Landau `O(1)` bound on the Shaw
sequence upgrades to a *global* uniform Shaw bound `ShawOOneOn`.  The cofinite-to-global step uses
that, over `ℕ`, the finitely many sub-threshold indices have a finite maximum. -/
theorem shawOOneOn_of_shawSeq_isBigO_one {q n M : ℕ → ℝ}
    (hnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M i))
    (h : (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ))) :
    ShawOOneOn q n M := by
  rw [isBigO_one_iff] at h
  obtain ⟨B, hB⟩ := h
  rw [eventually_map, eventually_atTop] at hB
  obtain ⟨N, hN⟩ := hB
  classical
  -- Prefix budget: each sub-threshold value is `≤ ∑_{j<N} shawSeq j` because every term is `≥ 0`.
  set P : ℝ := ∑ j ∈ Finset.range N, shawSeq q n M j with hP
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun j _ => hnn j)
  have hBnn : 0 ≤ B := by
    have := hN N (le_refl N)
    exact le_trans (abs_nonneg _) (by simpa using this)
  -- Constant: max of the eventual bound `B` and the finite prefix budget `P`.
  refine ⟨max B P, le_max_of_le_left hBnn, ?_⟩
  · intro i
    rcases le_or_gt N i with hi | hi
    · -- eventual regime: `shawSeq i = ‖shawSeq i‖ ≤ B ≤ max B P`
      have h1 : shawValue (q i) (n i) (M i) ≤ B := by
        have := hN i hi
        simpa [shawSeq, abs_of_nonneg (hnn i)] using this
      exact le_trans h1 (le_max_left _ _)
    · -- prefix regime: `shawSeq i ≤ ∑_{j<N} shawSeq j = P ≤ max B P`
      have hmem : i ∈ Finset.range N := Finset.mem_range.2 hi
      have h2 : shawSeq q n M i ≤ P := by
        rw [hP]
        exact Finset.single_le_sum (fun j _ => hnn j) hmem
      exact le_trans h2 (le_max_right _ _)

/-! ### Prize-side companion: `M = O(√(n·log(q/n)))` in literal Landau notation -/

/-- The `ℕ`-indexed sup-norm sequence of a prize family. -/
noncomputable def supSeq (M : ℕ → ℝ) : ℕ → ℝ := fun i => M i

/-- The `ℕ`-indexed prize-scale sequence `√(n·log(q/n))`. -/
noncomputable def scaleSeq (q n : ℕ → ℝ) : ℕ → ℝ := fun i => shawScale (q i) (n i)

/-- **Prize-side forward bridge.**  A global uniform prize-core bound `M ≤ C·scale` over the whole
`ℕ` family, with pointwise nonnegative `M`, is in particular the literal Landau prize statement
`M =O[atTop] √(n·log(q/n))`.  (The scale `√(·)` is automatically `≥ 0`, so `‖scale‖ = scale`.) -/
theorem supSeq_isBigO_scaleSeq_of_corePrizeBoundOn {q n M : ℕ → ℝ}
    (hMnn : ∀ i, 0 ≤ M i)
    (h : CorePrizeBoundOn q n M) :
    (supSeq M) =O[atTop] (scaleSeq q n) := by
  obtain ⟨C, _hC, hbound⟩ := h
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards with i
  -- `‖M i‖ = M i`, `‖scale i‖ = scale i` (both nonneg); then the global bound.
  rw [show ‖supSeq M i‖ = M i from abs_of_nonneg (hMnn i),
      show ‖scaleSeq q n i‖ = shawScale (q i) (n i) from
        abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hbound i

/-- **Prize-side backward bridge.**  Under the prize-regime guard `0 < scale` (e.g. `n_i < q_i`,
`0 < n_i`) and pointwise nonnegative `M`, the literal Landau bound `M =O[atTop] scale` upgrades to a
global uniform prize-core bound `CorePrizeBoundOn`.  Positivity of the scale makes the prefix ratios
`M i / scale i` well-defined, and the finitely many sub-threshold indices are absorbed. -/
theorem corePrizeBoundOn_of_supSeq_isBigO_scaleSeq {q n M : ℕ → ℝ}
    (hMnn : ∀ i, 0 ≤ M i)
    (hscale : ∀ i, 0 < shawScale (q i) (n i))
    (h : (supSeq M) =O[atTop] (scaleSeq q n)) :
    CorePrizeBoundOn q n M := by
  rw [isBigO_iff] at h
  obtain ⟨c, hc⟩ := h
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  classical
  -- eventual constant (made nonneg): `c' = max c 0`
  set c' : ℝ := max c 0 with hc'
  have hc'nn : 0 ≤ c' := le_max_right _ _
  -- prefix ratio budget: each `M i / scale i` for `i < N`, summed (all terms ≥ 0).
  set P : ℝ := ∑ j ∈ Finset.range N, (M j / shawScale (q j) (n j)) with hP
  have hPnn : 0 ≤ P :=
    Finset.sum_nonneg (fun j _ => div_nonneg (hMnn j) (le_of_lt (hscale j)))
  refine ⟨max c' P, le_max_of_le_left hc'nn, ?_⟩
  intro i
  rcases le_or_gt N i with hi | hi
  · -- eventual regime: `M i = ‖M i‖ ≤ c·‖scale i‖ = c·scale i ≤ c'·scale i ≤ (max c' P)·scale i`
    have hbi := hN i hi
    rw [show ‖supSeq M i‖ = M i from abs_of_nonneg (hMnn i),
        show ‖scaleSeq q n i‖ = shawScale (q i) (n i) from
          abs_of_nonneg (Real.sqrt_nonneg _)] at hbi
    have hstep : c * shawScale (q i) (n i) ≤ (max c' P) * shawScale (q i) (n i) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (hscale i))
      exact le_trans (le_max_left c 0) (le_max_left c' P)
    exact le_trans hbi hstep
  · -- prefix regime: `M i / scale i ≤ P ≤ max c' P`, so `M i ≤ (max c' P)·scale i`
    have hmem : i ∈ Finset.range N := Finset.mem_range.2 hi
    have hratio : M i / shawScale (q i) (n i) ≤ P := by
      rw [hP]
      exact Finset.single_le_sum
        (fun j _ => div_nonneg (hMnn j) (le_of_lt (hscale j))) hmem
    have hle : M i / shawScale (q i) (n i) ≤ max c' P := le_trans hratio (le_max_right _ _)
    rw [div_le_iff₀ (hscale i)] at hle
    exact hle

/-- **Prize-side Landau iff capstone.**  In the prize regime (positive scale, nonnegative sup norm),
the campaign predicate `CorePrizeBoundOn` is *literally* the Landau prize statement
`M =O[atTop] √(n·log(q/n))`. -/
theorem corePrizeBoundOn_iff_supSeq_isBigO_scaleSeq {q n M : ℕ → ℝ}
    (hMnn : ∀ i, 0 ≤ M i)
    (hscale : ∀ i, 0 < shawScale (q i) (n i)) :
    CorePrizeBoundOn q n M ↔ (supSeq M) =O[atTop] (scaleSeq q n) :=
  ⟨supSeq_isBigO_scaleSeq_of_corePrizeBoundOn hMnn,
   corePrizeBoundOn_of_supSeq_isBigO_scaleSeq hMnn hscale⟩

/-- **Landau capstone (Lane-2).**  On an `ℕ`-indexed prize family with pointwise nonnegative Shaw
value, the campaign predicate `ShawOOneOn` is *literally* Mathlib's Landau statement
`shawSeq =O[atTop] 1`.  This is the notation bridge: the prose slogan `Sh(n)=O(1)` and the campaign's
`∃`-uniform-constant predicate are the same `Asymptotics.IsBigO` object a number theorist would cite.
No new analytic bound; CORE stays OPEN. -/
theorem shawOOneOn_iff_shawSeq_isBigO_one {q n M : ℕ → ℝ}
    (hnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M i)) :
    ShawOOneOn q n M ↔ (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ)) :=
  ⟨shawSeq_isBigO_one_of_shawOOneOn hnn, shawOOneOn_of_shawSeq_isBigO_one hnn⟩

/-- Under the prize-regime guard, a nonnegative sup norm gives a nonnegative Shaw value
`shawValue = M / scale` (quotient of `M ≥ 0` by `scale > 0`). -/
theorem shawValue_nonneg_of_prizeRegime {q n M : ℝ}
    (hMnn : 0 ≤ M) (hscale : 0 < shawScale q n) : 0 ≤ shawValue q n M := by
  unfold shawValue
  exact div_nonneg hMnn (le_of_lt hscale)

/-- **HEADLINE Landau capstone (Lane-2): `prize ⇔ Sh(n)=O(1)`, entirely in Landau notation.**
In the prize regime (`0 < shawScale`, e.g. `n_i < q_i`, `0 < n_i`) with nonnegative sup norm, the
literal prize bound `M =O[atTop] √(n·log(q/n))` is equivalent to the literal `Sh(n)=O(1)` statement
`(M/√(n·log(q/n))) =O[atTop] 1`.  This is the campaign's headline reduction stated wholly in Mathlib's
`Asymptotics.IsBigO` symbol — the form a number theorist cites.  Composes the prize-side bridge, the
Shaw-side bridge, and the campaign equivalence `shawOOneOn_iff_corePrizeBoundOn`.  No new analytic
estimate; CORE stays OPEN. -/
theorem prize_isBigO_iff_shaw_isBigO_one {q n M : ℕ → ℝ}
    (hMnn : ∀ i, 0 ≤ M i)
    (hscale : ∀ i, 0 < shawScale (q i) (n i)) :
    ((supSeq M) =O[atTop] (scaleSeq q n)) ↔
      (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ)) := by
  have hShnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M i) :=
    fun i => shawValue_nonneg_of_prizeRegime (hMnn i) (hscale i)
  calc ((supSeq M) =O[atTop] (scaleSeq q n))
      ↔ CorePrizeBoundOn q n M :=
        (corePrizeBoundOn_iff_supSeq_isBigO_scaleSeq hMnn hscale).symm
    _ ↔ ShawOOneOn q n M := (shawOOneOn_iff_corePrizeBoundOn hscale).symm
    _ ↔ (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ)) :=
        shawOOneOn_iff_shawSeq_isBigO_one hShnn

/-! ### Domination transfer: a Landau prize bound passes to any dominated sup norm -/

/-- **Domination transfer of the Landau prize bound.**  If a sup-norm family `M` satisfies the literal
Landau prize bound `M =O[atTop] √(n·log(q/n))` and a second family `M'` is pointwise sandwiched
`0 ≤ M' i ≤ M i` (e.g. the actual Gauss-period sup norm dominated by an auxiliary majorant whose Landau
bound is known), then `M'` satisfies the SAME Landau prize bound.  This is the citable composition rung:
any majorant with a proven `O(√(n·log(q/n)))` bound transports it to everything it dominates.  No new
analytic estimate; CORE stays OPEN. -/
theorem supSeq_isBigO_scaleSeq_of_le {q n M M' : ℕ → ℝ}
    (hM'nn : ∀ i, 0 ≤ M' i) (hle : ∀ i, M' i ≤ M i)
    (h : (supSeq M) =O[atTop] (scaleSeq q n)) :
    (supSeq M') =O[atTop] (scaleSeq q n) := by
  rw [isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  filter_upwards [hc] with i hi
  -- `‖M' i‖ = M' i ≤ M i = ‖M i‖ ≤ c·‖scale i‖`
  rw [show ‖supSeq M' i‖ = M' i from abs_of_nonneg (hM'nn i)]
  refine le_trans (hle i) ?_
  rw [show M i = ‖supSeq M i‖ from (abs_of_nonneg (le_trans (hM'nn i) (hle i))).symm]
  exact hi

/-- **Dominated-majorant transfer into Shaw language.**  If a majorant `M` satisfies the literal
Landau prize bound and the target sup norm `M'` is pointwise sandwiched `0 ≤ M' ≤ M`, then the Shaw
value of `M'` is literally `O(1)`.  This packages the two citable rungs in one theorem: first transfer
`M = O(scale)` through domination, then use the headline `prize ⇔ Sh(n)=O(1)` Landau capstone.  No
new analytic estimate is asserted; CORE remains exactly the missing majorant bound. -/
theorem shawSeq_isBigO_one_of_le_prizeBigO {q n M M' : ℕ → ℝ}
    (hM'nn : ∀ i, 0 ≤ M' i) (hscale : ∀ i, 0 < shawScale (q i) (n i))
    (hle : ∀ i, M' i ≤ M i)
    (h : (supSeq M) =O[atTop] (scaleSeq q n)) :
    (shawSeq q n M') =O[atTop] (fun _ => (1 : ℝ)) := by
  exact (prize_isBigO_iff_shaw_isBigO_one hM'nn hscale).mp
    (supSeq_isBigO_scaleSeq_of_le hM'nn hle h)

/-- **Dominated-majorant transfer into the campaign `ShawOOneOn` predicate.**  Under the prize-regime
positive-scale guard, a Landau prize bound for any pointwise majorant `M` immediately gives the global
uniform `Sh(n)=O(1)` statement for every nonnegative dominated target `M'`.  This is normalization and
order bookkeeping only, useful for citing a future closed-form majorant without redoing the reduction. -/
theorem shawOOneOn_of_le_prizeBigO {q n M M' : ℕ → ℝ}
    (hM'nn : ∀ i, 0 ≤ M' i) (hscale : ∀ i, 0 < shawScale (q i) (n i))
    (hle : ∀ i, M' i ≤ M i)
    (h : (supSeq M) =O[atTop] (scaleSeq q n)) :
    ShawOOneOn q n M' := by
  have hShnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M' i) :=
    fun i => shawValue_nonneg_of_prizeRegime (hM'nn i) (hscale i)
  exact (shawOOneOn_iff_shawSeq_isBigO_one hShnn).mpr
    (shawSeq_isBigO_one_of_le_prizeBigO hM'nn hscale hle h)

#print axioms ProximityGap.Frontier.ShawValueCapstone.shawSeq_isBigO_one_of_le_prizeBigO
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_of_le_prizeBigO

end ProximityGap.Frontier.ShawValueCapstone
