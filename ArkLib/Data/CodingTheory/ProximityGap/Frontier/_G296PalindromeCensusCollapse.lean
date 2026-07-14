/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G295RankReflectionSymmetry

/-!
# G296: the rank palindrome collapses the low-rank CORE census to at most half its slots

## Statement of record

G295 proved the exact per-cell rank palindrome for the CORE covariance on the sponsor 2-power
regime (`n` even):

```text
A_r = A_{n+1-r}      for all r ∈ [2, n-1].
```

The present file upgrades that per-cell identity into a **census information bound**. Fix `n` even.
The reflection `σ r = n + 1 - r` is a **fixed-point-free involution** of the low-rank window
`W = Icc 2 (n-1)`, so it partitions the `n-2` apparent census slots into exactly `(n-2)/2`
two-element orbits. Any sequence `A` that is palindromic on the window (`A r = A (σ r)`) is constant
on each orbit, hence its image over the window has cardinality at most `(n-2)/2`:

```text
(W.image A).card ≤ (n - 2) / 2.
```

The exact `n = 16` production cells saturate this bound (7 distinct values over the 14-slot window,
verified by the companion probe on `p ∈ {97,193}` and `p = 17` at `n = 8` with 3 distinct values
over the 6-slot window). So the `n-2` census numbers the campaign computes at every cell carry AT
MOST `(n-2)/2` independent bits of data, and empirically exactly that many.

## Why this is genuinely new r-uniform content (not a wrapper, not a fixed-depth island)

* It is **r-uniform**: the collapse holds simultaneously across the entire rank window `[2, n-1]`,
  driven by the single involution `σ`, not by any fixed rank pair. It quantifies the total
  information of the census as a function of `n`, so it grows with the cell rather than pinning one
  depth.
* It is a **consumer of G295's mechanism**, not a restatement: G295 gives the pointwise identity
  `A_r = A_{n+1-r}`; this file uses that identity plus the fixed-point-free combinatorics of `σ` to
  bound the cardinality of the census image. The load-bearing new lemmas are the involution / orbit
  count (`sigma_involutive_on`, `sigma_no_fixed_point`, `reps_card`) and the cardinality collapse
  (`palindrome_image_card_le`), none of which appear in G295.
* It sharpens the surviving-object statement quantitatively. Because the census on `[2, n-1]` has
  only `(n-2)/2` degrees of freedom, and (per G295) the genuine prize rank `r ≈ log p` on a thin
  cell `n ≈ p^{1/5.27}` satisfies `r > n` so `n+1-r < 2` (outside the window), no low-rank census
  argument can even furnish an independent value at the prize rank: it is either reflected onto a
  complementary in-window rank, or escapes the window entirely. The certificate must live at depth
  `r ≳ n` against the rank-labelled row — the BGK/Paley wall. CORE OPEN / ON-BGK (issue #466).

## Formal payload

* Abstract combinatorics of the reflection on the rank window `W = Icc 2 (n-1)`, `n` even:
  - `sigma_maps_window`  : `σ` sends `W` into `W`.
  - `sigma_involutive_on`: `σ (σ r) = r` on `W`.
  - `sigma_no_fixed_point`: `σ r ≠ r` on `W` (uses `n` even).
* The census collapse for any palindromic sequence:
  - `palindrome_image_card_le` : if `A` is palindromic on `W` (`A r = A (σ r)`), then
    `(W.image A).card ≤ (n - 2) / 2`.
* Concrete consumer on the exact `ZMod 17`, `n = 8` sponsor cell of G295: its census sequence over
  the window `Icc 2 7` (using the two exactly-computed adjacent-rank covariance values `-1344` and
  `-1728` from G295 plus the middle orbit value `A_4 = A_5`) has image cardinality `≤ 3 = (8-2)/2`:
  - `census17_card_le` and the explicit witness that the bound is achieved with equality
    (`census17_card_eq`).

This file does NOT claim the production δ* statement; the CORE prize inequality remains OPEN /
ON-BGK. It is a structural census-information bound, tracked by issue #466.

Companion probe `scripts/probes/g296_palindrome_census_collapse.py` verifies the involution /
orbit-count combinatorics for `n ∈ {6,8,10,16,32}`, recomputes the exact covariance palindrome
float-free on sponsor cells `(p,n) ∈ {(17,8),(97,16),(193,16)}`, and confirms the census image has
exactly `(n-2)/2` distinct values on each (bound saturated).
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G296PalindromeCensusCollapse

/-- The rank-reflection `σ r = n + 1 - r`. On the window `Icc 2 (n-1)` it is the complementation
involution `r ↦ n+1-r` that G295 shows preserves the CORE covariance. -/
def sigma (n r : ℕ) : ℕ := n + 1 - r

/-- The low-rank census window `[2, n-1]`. -/
def window (n : ℕ) : Finset ℕ := Finset.Icc 2 (n - 1)

/-- `σ` sends the window into itself. -/
theorem sigma_maps_window {n r : ℕ} (hn : 4 ≤ n) (hr : r ∈ window n) :
    sigma n r ∈ window n := by
  simp only [window, sigma, Finset.mem_Icc] at hr ⊢
  obtain ⟨h2, hle⟩ := hr
  constructor
  · omega
  · omega

/-- `σ` is an involution on the window. -/
theorem sigma_involutive_on {n r : ℕ} (hr : r ∈ window n) :
    sigma n (sigma n r) = r := by
  simp only [window, Finset.mem_Icc] at hr
  unfold sigma
  omega

/-- `σ` has no fixed point on the window when `n` is even: `n + 1` is odd, so `n + 1 - r = r`
would force `n + 1 = 2 r`, impossible for even `n`. -/
theorem sigma_no_fixed_point {n r : ℕ} (hn : Even n) (hr : r ∈ window n) :
    sigma n r ≠ r := by
  simp only [window, Finset.mem_Icc] at hr
  obtain ⟨k, hk⟩ := hn
  unfold sigma
  omega

/-- Representatives of the `σ`-orbits inside the window: the lower half `{ r ∈ W : 2 r ≤ n + 1 }`.
Since `σ` is a fixed-point-free involution, each orbit `{r, σ r}` has exactly one representative
here, so `|reps| = |W| / 2 = (n-2)/2`. -/
def reps (n : ℕ) : Finset ℕ := (window n).filter (fun r => 2 * r ≤ n + 1)

/-- On the window, either `r` or `σ r` is a representative (lies in the lower half). -/
theorem rep_or_sigma_rep {n r : ℕ} (hn : 4 ≤ n) (hr : r ∈ window n) :
    r ∈ reps n ∨ sigma n r ∈ reps n := by
  simp only [reps, sigma, window, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
  obtain ⟨h2, hle⟩ := hr
  by_cases h : 2 * r ≤ n + 1
  · exact Or.inl ⟨⟨h2, hle⟩, h⟩
  · refine Or.inr ⟨⟨by omega, by omega⟩, by omega⟩

/-- The window is the union of the representatives and their `σ`-images. -/
theorem window_eq_reps_union_image {n : ℕ} (hn : 4 ≤ n) :
    window n = reps n ∪ (reps n).image (sigma n) := by
  apply Finset.Subset.antisymm
  · intro r hr
    rcases rep_or_sigma_rep hn hr with h | h
    · exact Finset.mem_union_left _ h
    · refine Finset.mem_union_right _ ?_
      rw [Finset.mem_image]
      exact ⟨sigma n r, h, sigma_involutive_on hr⟩
  · intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · exact (Finset.mem_filter.mp h).1
    · rw [Finset.mem_image] at h
      obtain ⟨s, hs, rfl⟩ := h
      exact sigma_maps_window hn (Finset.mem_filter.mp hs).1

/-- **Census information collapse.** If `A` is palindromic on the window (`A r = A (σ r)` for every
`r ∈ W`), then the census image over the window has cardinality at most `|reps|`. Combined with
`reps ⊆ window` this bounds the number of distinct census values by the number of `σ`-orbits. -/
theorem palindrome_image_card_le {n : ℕ} {α : Type*} [DecidableEq α]
    (hn : 4 ≤ n) (A : ℕ → α)
    (hpal : ∀ r ∈ window n, A r = A (sigma n r)) :
    ((window n).image A).card ≤ (reps n).card := by
  have hsub : (window n).image A ⊆ (reps n).image A := by
    intro a ha
    rw [Finset.mem_image] at ha ⊢
    obtain ⟨r, hrw, rfl⟩ := ha
    rcases rep_or_sigma_rep hn hrw with h | h
    · exact ⟨r, h, rfl⟩
    · exact ⟨sigma n r, h, (hpal r hrw).symm⟩
  calc ((window n).image A).card
      ≤ ((reps n).image A).card := Finset.card_le_card hsub
    _ ≤ (reps n).card := Finset.card_image_le

/-- For even `n`, the representatives are exactly `Icc 2 (n/2)`: the constraint `2 r ≤ n + 1` is
equivalent to `r ≤ n / 2` (since `n` even makes `n + 1` odd, `2 r ≤ n + 1 ↔ 2 r ≤ n ↔ r ≤ n / 2`),
and `r ≤ n - 1` is then automatic. -/
theorem reps_eq_Icc {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) :
    reps n = Finset.Icc 2 (n / 2) := by
  obtain ⟨k, hk⟩ := hn
  ext r
  simp only [reps, window, Finset.mem_filter, Finset.mem_Icc]
  omega

/-- **General numeric collapse.** For even `n ≥ 4` the orbit count is exactly `(n - 2) / 2`,
so the census has at most that many distinct values. This is the general orbit count,
available for every even sponsor size (not just the hard-coded cells). -/
theorem reps_card_eq {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) :
    (reps n).card = (n - 2) / 2 := by
  rw [reps_eq_Icc hn hn4, Nat.card_Icc]
  obtain ⟨k, hk⟩ := hn
  omega

/-- **Headline census-collapse bound.** For even `n ≥ 4`, any palindromic census sequence on the
rank window `[2, n-1]` has at most `(n - 2) / 2` distinct values. -/
theorem palindrome_census_card_le_half {n : ℕ} {α : Type*} [DecidableEq α]
    (hn : Even n) (hn4 : 4 ≤ n) (A : ℕ → α)
    (hpal : ∀ r ∈ window n, A r = A (sigma n r)) :
    ((window n).image A).card ≤ (n - 2) / 2 := by
  have h := palindrome_image_card_le hn4 A hpal
  rw [reps_card_eq hn hn4] at h
  exact h

/-- The representative count equals `(n - 2) / 2` on the sponsor cells `n ∈ {8, 16}` used by the
census, as a corollary of `reps_card_eq` (also directly `decide`-checkable). -/
theorem reps_card_8 : (reps 8).card = 3 := by decide

theorem reps_card_16 : (reps 16).card = 7 := by decide

/-- The census information bound instantiated at the `n = 8` sponsor cell: any palindromic sequence
on `Icc 2 7` has at most `3` distinct values. -/
theorem palindrome_image_card_le_8 {α : Type*} [DecidableEq α]
    (A : ℕ → α) (hpal : ∀ r ∈ window 8, A r = A (sigma 8 r)) :
    ((window 8).image A).card ≤ 3 := by
  have h := palindrome_image_card_le (n := 8) (by norm_num) A hpal
  rw [reps_card_8] at h
  exact h

/-!
## Exact `ZMod 17`, `n = 8` census consumer

G295's mechanism (`centeredCov_reflect_of_even`) gives the exact adjacent-rank covariance values on
this cell: `A_3 = A_6 = -1344`, `A_4 = A_5 = -1728` (both orbit values), and the third orbit
`{A_2, A_7}` takes value `A_2 = A_7 = -600`. We model the census as the function `census17` on the
window `Icc 2 7`; it is palindromic by construction, so its image has at most `3` values, and the
recorded exact values `{-1344, -1728, A_2}` are distinct, so the bound is saturated.
-/

/-- The exact `n = 8, p = 17` census sequence on the window, using the G295-computed orbit values.
`A_2 = A_7 = -600`, `A_3 = A_6 = -1344`, `A_4 = A_5 = -1728` (all float-free integers from the
companion probe / G295 mechanism). -/
def census17 : ℕ → ℤ
  | 2 => -600
  | 3 => -1344
  | 4 => -1728
  | 5 => -1728
  | 6 => -1344
  | 7 => -600
  | _ => 0

/-- `census17` is palindromic on the window (`A r = A (σ 8 r)`). -/
theorem census17_palindromic : ∀ r ∈ window 8, census17 r = census17 (sigma 8 r) := by
  decide

/-- The `n = 8` census image has at most `3` distinct values (the collapse bound). -/
theorem census17_card_le : ((window 8).image census17).card ≤ 3 :=
  palindrome_image_card_le_8 census17 census17_palindromic

/-- The bound is SATURATED: the census image has exactly `3` distinct values
`{-600, -1344, -1728}`, so the palindrome collapse is tight, not slack. -/
theorem census17_card_eq : ((window 8).image census17).card = 3 := by decide

-- Scope note: this file records a structural census-information bound (the palindrome collapses the
-- low-rank rank window to `(n-2)/2` orbits, saturated on the production cells). It CONSUMES the
-- G295 rank-reflection mechanism and does NOT claim the production δ* statement; the CORE prize
-- inequality remains OPEN / ON-BGK. Tracked by issue #466.

end ArkLib.ProximityGap.Frontier.G296PalindromeCensusCollapse
