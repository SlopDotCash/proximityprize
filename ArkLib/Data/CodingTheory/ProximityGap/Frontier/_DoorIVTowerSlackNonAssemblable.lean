/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Door-(iv) constraint: the dyadic tower's MIN-OVER-COSETS slack count is NON-ASSEMBLABLE —
  it does not lower-bound the achievable damping, so its growth re-opens nothing (#464)

This file strengthens `_DoorIVCoherenceTowerCollapse` by closing the precise loophole its banked
verdict left open.  That verdict ([door-iv-tower-collapse-quantitative], 2026-06-19) proved the
honest single-chain coherence product collapses to a fixed-width bottom (`k = O(1)` nontrivial levels),
and named the two — and only two — surviving escape hatches for any dyadic-tower attack to deliver
`log₂ n`-many damping factors:

  > "A successful door-(iv) coherence-tower attack must prove EITHER that the number of genuinely
  >  nontrivial levels GROWS with n OR that the bottom factors themselves SHRINK with n."

## The probe that motivated this lemma (and the trap it exposes)

`scripts/probes/probe_dooriv_tower_slack_count_law.py` (proper `μ_n`, `p ≫ n³`, structured primes
`p = k·n+1`, never `n = q-1`, exact complex `η`, global worst-`b` scan, `n = 16..256`) measured, per
dyadic level `j`, the **minimum** coherence `ρ_j` over **all** `2^{a-j}` cosets of `μ_{2^j}`.  That
min-over-cosets slack count `K_min(n) = #{ j : 1 − ρ_j^{min} ≥ τ }` was observed to GROW with
`a = log₂ n` (`1,2,3,5,5` for `a = 4..8`), which at face value would re-open escape-hatch (1).

`scripts/probes/probe_dooriv_tower_honest_chain_vs_minover.py` then resolved the discrepancy: along the
**actual single nested chain** that telescopes the worst-frequency period, the slack count `K_chain(n)`
does NOT grow (`0,0,2,1,1,3,1,2,2,0` over `a = 4..8` — no upward trend, `O(1)`).  The growth of
`K_min` is an **artifact of unrelated sibling cosets**: at each level the minimum is attained at a
*different* coset, and those incidental cancellations live in branches that do NOT compose into a bound
on the worst-frequency period.

## What this file formalizes (the assemblability obstruction)

The mechanism is an elementary but decisive fact about products of per-level minima.  A genuine
telescoping bound is a product along ONE chain: `chainProd = ∏_j ρ_j(C_j)` for a single nested chain
`C_a ⊃ C_{a-1} ⊃ ... ⊃ C_0`.  The "slack count" attack instead reads `minProd = ∏_j (min over all
cosets at level j)`.  We prove:

* `minProd_le_chainProd` — the min-over-cosets product is `≤` ANY single-chain product (it is dominated
  by every assignment, in particular the honest one).  So `minProd` is a LOWER bound on the chain
  product, never an upper bound: a *small* `minProd` (large `K_min`) gives NO upper bound on the period.
* `minProd_strictly_below_topcoherent_chain` — a concrete two-level witness where the min-over-cosets
  product is strictly below the product along the MAXIMAL-coherence (`ρ ≡ 1`) chain.  The honest tower
  collapse forces the realizing chain to be top-coherent at the high levels; the min-over-cosets reading
  instead picks the cancelling sibling coset at each level, a path the top-coherent chain cannot follow.
  Hence `K_min` growth is read off branches the period's own chain does not take: the slack is
  non-assemblable into a bound on the worst-frequency period.  (Note: under the abstract list model a
  degenerate all-zero chain trivially matches `minProd`; the content is precisely that the min is BELOW
  the top-coherent chain that the collapse forces, not that it beats every conceivable selection.)
* `chainProd_eq_period_ratio_no_saving` — packaged statement of WHY even the honest chain product proves
  nothing: it equals the period ratio it is meant to bound (the telescoping identity is a tautology), so
  the only real content is the per-step `|A+B| = ρ·(|A|+|B|)` recursion = the half-mass descent, already
  mapped.

VERDICT: escape-hatch (1) ("number of nontrivial levels grows") is closed adversarially.  The growing
quantity (`K_min`) is the WRONG object — it is non-assemblable into a period bound — and the RIGHT object
(`K_chain`) is `O(1)` (the already-banked collapse).  The dyadic-tower coherence-product lever stays
DEAD.  No CORE / cancellation / completion / moment / anti-concentration / capacity claim; `M(μ_n)`
remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVTowerSlackNonAssemblable

open scoped BigOperators

/-- A per-level coherence table: `cohrt j` is the *list* of coset coherences at level `j` (one entry
per coset of `μ_{2^j}`).  We model the tower as a list-of-lists, level `0` at the head. -/
abbrev CoherenceTable := List (List ℝ)

/-- `minProd` reads, at each level, the MINIMUM coherence over all cosets, and multiplies down the
tower.  This is the quantity the slack-count attack tracks. -/
def minProd (T : CoherenceTable) : ℝ :=
  (T.map (fun lvl => lvl.foldr min 1)).prod

/-- A *chain* selects one coherence per level.  `chainProd sel` is the product along the chosen chain. -/
def chainProd (sel : List ℝ) : ℝ := sel.prod

/-- **The per-level minimum is `≤` every entry at that level** (over a nonempty level list, every
member dominates the foldr-min). -/
theorem foldr_min_le_mem {l : List ℝ} {x : ℝ} (hx : x ∈ l) :
    l.foldr min 1 ≤ x := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih h)

/-- **The min-over-cosets product is `≤` any single-chain product**, provided each level's chosen
coherence is a member of that level's list and all per-level minima are nonnegative.  Hence a small
`minProd` (large slack count) gives only a LOWER bound on the chain product: it can never upper-bound
the worst-frequency period, so its growth re-opens nothing. -/
theorem minProd_le_chainProd (T : CoherenceTable) (sel : List ℝ)
    (hlen : T.length = sel.length)
    (hmem : ∀ i (hi : i < T.length),
      sel.get ⟨i, hlen ▸ hi⟩ ∈ T.get ⟨i, hi⟩)
    (hmin_nonneg : ∀ lvl ∈ T, 0 ≤ lvl.foldr min 1)
    (hsel_nonneg : ∀ x ∈ sel, 0 ≤ x) :
    minProd T ≤ chainProd sel := by
  unfold minProd chainProd
  -- both products are over lists of the same length; compare termwise.
  induction T generalizing sel with
  | nil =>
    have hsel0 : sel.length = 0 := by simpa using hlen.symm
    have : sel = [] := List.eq_nil_of_length_eq_zero hsel0
    subst this; simp
  | cons lvl T ih =>
    cases sel with
    | nil => simp at hlen
    | cons s ss =>
      simp only [List.map_cons, List.prod_cons]
      have hlen' : T.length = ss.length := by simpa using hlen
      have hs_mem : s ∈ lvl := by
        have := hmem 0 (by simp)
        simpa using this
      have hmin_le_s : lvl.foldr min 1 ≤ s := foldr_min_le_mem hs_mem
      have hmin_lvl_nonneg : 0 ≤ lvl.foldr min 1 := hmin_nonneg lvl (by simp)
      -- tail hypotheses
      have hmem' : ∀ i (hi : i < T.length),
          ss.get ⟨i, hlen' ▸ hi⟩ ∈ T.get ⟨i, hi⟩ := by
        intro i hi
        have := hmem (i+1) (by simpa using Nat.succ_lt_succ hi)
        simpa using this
      have hmin_nonneg' : ∀ l ∈ T, 0 ≤ l.foldr min 1 :=
        fun l hl => hmin_nonneg l (by simp [hl])
      have hsel_nonneg' : ∀ x ∈ ss, 0 ≤ x :=
        fun x hx => hsel_nonneg x (by simp [hx])
      have ihT := ih ss hlen' hmem' hmin_nonneg' hsel_nonneg'
      -- ihT : (T.map _).prod ≤ ss.prod
      have hss_prod_nonneg : 0 ≤ ss.prod := by
        apply List.prod_nonneg; intro x hx; exact hsel_nonneg' x hx
      have hmap_prod_nonneg : 0 ≤ (T.map (fun lvl => lvl.foldr min 1)).prod := by
        apply List.prod_nonneg
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨l, hl, rfl⟩ := hx
        exact hmin_nonneg' l hl
      calc
        lvl.foldr min 1 * (T.map (fun lvl => lvl.foldr min 1)).prod
            ≤ s * (T.map (fun lvl => lvl.foldr min 1)).prod := by
              exact mul_le_mul_of_nonneg_right hmin_le_s hmap_prod_nonneg
        _ ≤ s * ss.prod := by
              exact mul_le_mul_of_nonneg_left ihT (le_trans hmin_lvl_nonneg hmin_le_s)

/-- **Concrete non-assemblability witness (against the top-coherent chain).**  A two-level table where
each level has two cosets with a "good" (`1`) and a "cancelling" (`0`) coherence, with the cancellations
in DIFFERENT branches: level 0 cancels in coset A, level 1 cancels in coset B.  The min-over-cosets
product is `0` (it reads a cancelling coset at BOTH levels), yet the maximal-coherence chain `[1,1]`
— the chain the honest tower collapse forces the realizing path toward at the high levels — has product
`1`.  So the `minProd = 0` reading (`K_min = 2`, "slack at every level") is strictly below the
top-coherent chain: the level-wise minima are attained on sibling branches the period's own chain does
not follow, so the growing slack count cannot be assembled into a bound on the worst-frequency period.
(Honesty note: under the abstract list model a degenerate `[0,0]` selection also gives product `0`; the
claim is deliberately stated only against the top-coherent chain, NOT "below every chain".) -/
theorem minProd_strictly_below_topcoherent_chain :
    minProd [[1, 0], [0, 1]] = 0
      ∧ chainProd [1, 1] = 1
      ∧ minProd [[1, 0], [0, 1]] < chainProd [1, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [minProd]
  · simp [chainProd]
  · simp [minProd, chainProd]

/-- **The honest chain product is `≤ 1` and never amplifies** (each factor in `[0,1]`), so a chain
product cannot exceed the trivial bound; combined with `minProd_le_chainProd`, the min-over-cosets
product is squeezed in `[0, chainProd] ⊆ [0,1]` and carries no upper-bound information on the period. -/
theorem chainProd_le_one (sel : List ℝ)
    (h0 : ∀ x ∈ sel, 0 ≤ x) (h1 : ∀ x ∈ sel, x ≤ 1) :
    chainProd sel ≤ 1 := by
  unfold chainProd
  induction sel with
  | nil => simp
  | cons s ss ih =>
    simp only [List.prod_cons]
    have hs0 : 0 ≤ s := h0 s (by simp)
    have hs1 : s ≤ 1 := h1 s (by simp)
    have hss_nonneg : 0 ≤ ss.prod := by
      apply List.prod_nonneg; intro x hx; exact h0 x (by simp [hx])
    have ihss : ss.prod ≤ 1 :=
      ih (fun x hx => h0 x (by simp [hx])) (fun x hx => h1 x (by simp [hx]))
    calc s * ss.prod ≤ 1 * ss.prod := mul_le_mul_of_nonneg_right hs1 hss_nonneg
      _ = ss.prod := one_mul _
      _ ≤ 1 := ihss

/-- **Packaged tautology statement: an honest chain product that *equals* the period ratio proves
nothing new.**  If a chain product is asserted to equal the period ratio `r` it is meant to bound
(`chainProd sel = r`), then the "bound" `r ≤ chainProd sel` holds with EQUALITY — it is vacuous as an
upper bound.  This formalizes why even the correctly-assembled single-chain telescope is not an
independent saving: it restates the period.  The only nonvacuous content is the per-step half-mass
recursion `|A+B| = ρ·(|A|+|B|)`, which is the already-mapped half-mass descent. -/
theorem chainProd_eq_period_ratio_no_saving (sel : List ℝ) (r : ℝ)
    (h : chainProd sel = r) : r ≤ chainProd sel := le_of_eq h.symm

end ArkLib.ProximityGap.Frontier.DoorIVTowerSlackNonAssemblable

#print axioms ArkLib.ProximityGap.Frontier.DoorIVTowerSlackNonAssemblable.foldr_min_le_mem
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTowerSlackNonAssemblable.minProd_le_chainProd
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTowerSlackNonAssemblable.minProd_strictly_below_topcoherent_chain
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTowerSlackNonAssemblable.chainProd_le_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTowerSlackNonAssemblable.chainProd_eq_period_ratio_no_saving
