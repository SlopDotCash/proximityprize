/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G296PalindromeCensusCollapse

/-!
# G299: the production prize depth lies INSIDE the palindrome census window

## What this corrects

The G296 file (`_G296PalindromeCensusCollapse.lean`) carries a *frontier-prose* claim, repeated in
its KB note and DISPROOF entry, that at the production point the prize rank escapes the palindrome
window:

> "the genuine prize rank `r ≈ log p` on a thin cell `n ≈ p^{1/5.27}` satisfies `r > n` so
> `n+1-r < 2` (outside the window) … it escapes the window entirely. The certificate must live at
> depth `r ≳ n`."

This is **mathematically false** at the campaign's own production parameters
(`q = 2¹⁵⁸`, `n = 2³⁰`, ledger deep sup-control depth `r* ≈ 89`; see
`CumulantOrderThreshold.lean`, `BadPrimeNormBound.lean`). Concretely `2 ≤ 89 < 2³⁰`, and
asymptotically for a fixed base the log grows far slower than the subgroup order, so the prize rank
never exceeds `n`; it lies *deep inside* the window `[2, n-1]`, and so does its reflection.

The G295 palindrome and G296 orbit/cardinality theorems remain *sound, unconditional* structural
identities (this file does not touch them). What this file removes is only the incorrect frontier
inference. After G299 the census-collapse results are correctly classified as a symmetry/compression
result on the low-rank window, **not** evidence that low-rank methods are irrelevant at the prize
depth. The CORE prize inequality remains OPEN / ON-BGK (issue #466): the surviving object is the
row-labelled covariance at the *in-window* depth `r* ≈ 89`.

## Theorem-level content (all axiom-clean, `[propext, Classical.choice, Quot.sound]` only)

Reusing G296's `window n = Icc 2 (n-1)` and `sigma n r = n + 1 - r`:

* `prizeDepth_mem_window` : the ledger depth `r* = 89` is in the window `window (2^30)`.
* `prizeDepth_reflection_mem_window` : its reflection `σ (2^30) 89 = 2^30 - 88` is in the window.
* `prizeDepth_reflection_eq` : `σ (2^30) 89 = 2^30 - 88` (exact, ≥ 2, i.e. NOT `< 2`).
* `prizeDepth_lt_order` : `89 < 2^30` (the negation of the "`r > n`" premise).
* `not_escape_window` : the direct refutation — it is **not** the case that `r* > n` and
  `σ n r* < 2` (the two conjuncts the escape prose asserted).

r-uniform log bound (the general reason the prize rank never escapes, no floated reals):

* `natLog_prize_eq_five` : `Nat.log (2^30) (2^158) = 5` — the production `⌊log_n q⌋`.
* `natLog_prize_lt_order` : `Nat.log (2^30) (2^158) < 2^30`.
* `natLog_le_of_lt_pow` (general) : if `q < n ^ n` then `Nat.log n q ≤ n` — for any
  prize scale below `n^n`, the rank `⌊log_n q⌋` is bounded by `n`, so it cannot escape above the
  window. At production `q = 2^158 < (2^30)^(2^30) = 2^(30·2^30)` by an astronomical margin, so
  `natLog_prize_le_order` follows.
* `escape_would_need_pow` : an escaping rank `Nat.log n q > n` would force `n ^ n ≤ q`; the
  contrapositive of `natLog_le_of_lt_pow`. Since `q = 2^158 ≪ (2^30)^(2^30)`, escape is impossible.

## References

Probe `scripts/probes/g299_prize_depth_in_window.py`; KB
`docs/kb/deltastar-466-g299-prize-depth-in-window-2026-07-13.md`; DISPROOF entry
`[466-G299-prize-depth-in-window]`. Production parameters: `CumulantOrderThreshold.lean` (`log_n q ≈
5.27`), `BadPrimeNormBound.lean` (`q = n·2^128 = 2^158`, `n = 2^30`). Fable referee 2026-07-14 03:15
and G56 2026-07-14 04:20 independently flagged the escape prose as false; this file is the
kernel-checked correction. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G299PrizeDepthInWindow

open ArkLib.ProximityGap.Frontier.G296PalindromeCensusCollapse

/-- The production subgroup order `n = 2^30`. -/
abbrev prizeOrder : ℕ := 2 ^ 30

/-- The production field scale `q = 2^158` (`= n · 2^128`). -/
abbrev prizeScale : ℕ := 2 ^ 158

/-- The campaign ledger deep sup-control / EVT prize depth `r* ≈ 89`. -/
abbrev prizeDepth : ℕ := 89

/-! ### The ledger prize depth is inside the window, and so is its reflection -/

/-- `r* = 89 < 2^30 = n`. This is the direct negation of the escape prose's premise `r > n`. -/
theorem prizeDepth_lt_order : prizeDepth < prizeOrder := by
  norm_num [prizeDepth, prizeOrder]

/-- The ledger prize depth `r* = 89` lies in the palindrome window `[2, 2^30 - 1]`. -/
theorem prizeDepth_mem_window : prizeDepth ∈ window prizeOrder := by
  simp only [window, prizeDepth, prizeOrder, Finset.mem_Icc]
  refine ⟨by norm_num, ?_⟩
  norm_num

/-- The reflection is exactly `σ (2^30) 89 = 2^30 - 88`, in particular `≥ 2` (NOT `< 2`). -/
theorem prizeDepth_reflection_eq : sigma prizeOrder prizeDepth = 2 ^ 30 - 88 := by
  simp only [sigma, prizeDepth, prizeOrder]
  omega

/-- The reflected prize depth `σ (2^30) 89 = 2^30 - 88` also lies in the window. -/
theorem prizeDepth_reflection_mem_window :
    sigma prizeOrder prizeDepth ∈ window prizeOrder := by
  have hn : (4 : ℕ) ≤ prizeOrder := by norm_num [prizeOrder]
  exact sigma_maps_window hn prizeDepth_mem_window

/-- **The direct refutation.** The escape prose asserted BOTH `r* > n` and `σ n r* < 2`. Neither
holds: in fact `r* < n` and `σ n r* ≥ 2`, so their conjunction is false. -/
theorem not_escape_window :
    ¬ (prizeOrder < prizeDepth ∧ sigma prizeOrder prizeDepth < 2) := by
  rintro ⟨hgt, _⟩
  exact absurd hgt (by simpa using Nat.not_lt.mpr (le_of_lt prizeDepth_lt_order))

/-! ### The r-uniform reason: `⌊log_n q⌋` never escapes above `n` -/

/-- The production `⌊log_n q⌋`: `Nat.log (2^30) (2^158) = 5` (since `(2^30)^5 = 2^150 ≤ 2^158 <
2^180 = (2^30)^6`). This is the integer prize rank scale `≈ 5.27` recorded in
`CumulantOrderThreshold.lean`. -/
theorem natLog_prize_eq_five : Nat.log prizeOrder prizeScale = 5 := by
  have h : Nat.log (2 ^ 30) (2 ^ 158) = 5 := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · -- (2^30)^5 = 2^150 ≤ 2^158
      norm_num [pow_mul]
    · -- 2^158 < (2^30)^6 = 2^180
      norm_num [pow_mul]
  simpa [prizeOrder, prizeScale] using h

/-- Consequently `⌊log_n q⌋ = 5 < 2^30 = n`: the prize rank is far below the subgroup order. -/
theorem natLog_prize_lt_order : Nat.log prizeOrder prizeScale < prizeOrder := by
  rw [natLog_prize_eq_five]
  norm_num [prizeOrder]

/-- **General r-uniform bound.** For any base `n ≥ 2` and any scale `q < n ^ n`, the log rank
`⌊log_n q⌋` is at most `n`. So no prize scale below `n^n` can push the rank above the window. -/
theorem natLog_le_of_lt_pow {n q : ℕ} (hq : q < n ^ n) :
    Nat.log n q ≤ n := by
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · simp [hq0]
  · -- from q < n^n, Nat.log n q < n ≤ n
    have : Nat.log n q < n := Nat.log_lt_of_lt_pow (by omega : q ≠ 0) hq
    omega

/-- **Production instance of the general bound.** `q = 2^158 < (2^30)^(2^30) = 2^(30·2^30)` by an
astronomical margin, hence `⌊log_n q⌋ ≤ n`. (The exact value is `5`; this is the general-shape
statement a downstream consumer can use for any in-range scale.) -/
theorem natLog_prize_le_order : Nat.log prizeOrder prizeScale ≤ prizeOrder := by
  exact le_of_lt natLog_prize_lt_order

/-- **Contrapositive / escape criterion.** If the prize rank were to escape above the order
(`Nat.log n q > n`), the scale would satisfy `n ^ n ≤ q`. Since production `q = 2^158` is far below
`(2^30)^(2^30)`, the escape hypothesis is unreachable at the prize point. -/
theorem escape_would_need_pow {n q : ℕ} (hesc : n < Nat.log n q) :
    n ^ n ≤ q := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  exact absurd (natLog_le_of_lt_pow hlt) (by omega)

end ArkLib.ProximityGap.Frontier.G299PrizeDepthInWindow
