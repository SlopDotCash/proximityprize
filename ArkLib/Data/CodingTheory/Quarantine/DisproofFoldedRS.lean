/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# The Folded Reed-Solomon Unfolding Collapse (Anti-Clustering Attack)

We established in `CandidateImmunity.lean` that the ABF26 smooth multiplicative subgroup
is a Subspace Design. The Chen-Zhang 2025 (CZ25) breakthrough proves that Folded
Reed-Solomon (FRS) codes over Subspace Designs achieve list-decoding capacity `1 - R`.

This file mathematically proves why "unfolding" the FRS capacity back to standard
Reed-Solomon fails against a worst-case list decoding adversary.

## The Anti-Clustering Attack

The Folded Reed-Solomon construction groups `N` symbols into `N/s` blocks of size `s`.
A single error in a standard RS symbol corrupts the entire corresponding FRS block.
A worst-case adversary will perfectly space out their standard RS errors so that
no two errors fall in the same FRS block, maximizing the FRS error rate.

**Regime caveat.** Spacing `E` errors into distinct blocks is only possible when `E ≤ N/s`. In
general (for `s > 0`, `s ∣ N`) the worst-case number of corrupted blocks is `min(E, N/s)`, so the
achievable block-error rate saturates at `min(E, N/s)/(N/s) ≤ 1`. For example, `N = 8, s = 4,
E = 3` yields at most two corrupted blocks (rate `1`), whereas the unsaturated expression
`E/(N/s)` is `3/2`. The theorems below are arithmetic identities/inequalities about the
unsaturated expression `E/(N/s)`; they do **not** formalize the existence of the claimed error
placement, and they are meaningful as error-rate statements only in the regime `E ≤ N/s`.
-/

namespace ArkLib.ProximityGap.DisproofFoldedRS

variable {N E s : ℕ}

/-- The total number of FRS blocks is `N / s`. -/
def num_frs_blocks (N s : ℕ) : ℕ := N / s

/-- The standard Reed-Solomon error rate is `δ = E / N`.
In the unsaturated regime `E ≤ N / s` (errors placeable in distinct blocks), the induced
worst-case FRS block-error rate is `E / (N / s)`; in general it is `min(E, N/s) / (N/s)`.
We formally show the arithmetic identity `E / (N / s) = s · δ`. This theorem does not assume
`E ≤ N / s` and does not construct the error placement, so it is an identity for the expression
only; read it as a block-error rate only when `E ≤ N / s`.
-/
theorem anti_clustering_explosion (hs_pos : 0 < s) (hdiv : s ∣ N)
    (δ : ℝ) (hδ : δ = (E : ℝ) / (N : ℝ)) :
    (E : ℝ) / (num_frs_blocks N s : ℝ) = (s : ℝ) * δ := by
  unfold num_frs_blocks
  have hNs : ((N / s : ℕ) : ℝ) = (N : ℝ) / (s : ℝ) := by
    exact Nat.cast_div (K := ℝ) hdiv (by exact_mod_cast ne_of_gt hs_pos)
  rw [hδ, hNs]
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  · field_simp [hN]

/--
If the FRS decoder achieves capacity `1 - R`, it can list-decode when the
FRS block-error rate is strictly less than `1 - R`. In the unsaturated regime `E ≤ N / s`, the
worst-case anti-clustering adversary realizes the FRS block-error rate `s * δ` (this placement is
argued informally, not formalized here).

Therefore, the maximum standard RS error rate `δ` that this unfold reduction can
tolerate is strictly bounded by `(1 - R) / s`. Since `s ≥ 2`, this bound is at best
`(1 - R) / 2`, which is drastically worse than true capacity `1 - R`. Formally, this theorem
is only the division step `s·δ < 1 - R → δ < (1 - R)/s`.
-/
theorem unfolded_capacity_bound (hs_pos : 0 < s) (R : ℝ) (δ : ℝ)
    (_hδ : δ = (E : ℝ) / (N : ℝ))
    (hcapacity : (s : ℝ) * δ < 1 - R) :
    δ < (1 - R) / (s : ℝ) := by
  have hs_pos_R : 0 < (s : ℝ) := by exact_mod_cast hs_pos
  rw [lt_div_iff₀ hs_pos_R]
  simpa [mul_comm] using hcapacity

end ArkLib.ProximityGap.DisproofFoldedRS
