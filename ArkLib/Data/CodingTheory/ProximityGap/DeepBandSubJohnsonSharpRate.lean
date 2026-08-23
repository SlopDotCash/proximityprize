/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandProductionSubJohnson

/-!
# The first deep band is sub-Johnson at almost every rate (#389)

`DeepBandProductionSubJohnson.lean` proved the first deep band (`m = 0`) strictly
sub-Johnson at rate `≤ 1/2` (`2k ≤ n`).  That hypothesis is far too conservative:
the sharp threshold is essentially rate `1`.

This file pins the **sharp rate threshold** for the first band.  For `5 ≤ k`,
`(k+1)² ≤ n·(k−1)` holds as soon as `n ≥ k + 4` — i.e. at *every* rate
`ρ = k/n ≤ k/(k+4)`, which tends to `1`.  Hence the in-tree above-Johnson
discharge `subJohnsonListBound_aboveJohnson` is provably inapplicable across the
entire production rate range bar a vanishing top sliver, not merely the
low-rate half.

The threshold is tight at the boundary of its hypothesis: at `k = 5`, `n = k+4 = 9`
gives `(k+1)² = 36 = n·(k−1)` exactly, so `k + 4` cannot be lowered to `k + 3`
without failing at large `k` (`(k+1)² > (k+3)(k−1)` for all `k`).

This continues the boundary-pinning of #389: it does **not** close the open
sub-Johnson list bound — it shows the above-Johnson route cannot reach the deployed
regime at essentially any rate, so that single obligation is genuinely unavoidable.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

namespace ProximityGap.Ownership

/-- **Sharp rate threshold for the first deep band.**  For `5 ≤ k` and `k + 4 ≤ n`
(rate `ρ ≤ k/(k+4) → 1`), the first band (`m = 0`) is strictly sub-Johnson:
`(k+1)² ≤ n·(k−1)`.  (`(k+1)² ≤ (k+4)(k−1) ≤ n(k−1)`.) -/
theorem firstBand_subJohnson_sharp {n k : ℕ} (hk : 5 ≤ k) (hn : k + 4 ≤ n) :
    (k + 0 + 1) ^ 2 ≤ n * (k - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have hd : 4 ≤ d := by omega
  have hnd : d + 5 ≤ n := by omega
  have hk1 : d + 1 - 1 = d := by omega
  rw [hk1]
  have key : (d + 1 + 0 + 1) ^ 2 ≤ (d + 5) * d := by nlinarith [hd]
  calc (d + 1 + 0 + 1) ^ 2 ≤ (d + 5) * d := key
    _ ≤ n * d := by gcongr

/-- **The above-Johnson discharge is vacuous at almost every rate.**  For `5 ≤ k`
and `k + 4 ≤ n`, the hypothesis of `subJohnsonListBound_aboveJohnson` is false; the
in-tree above-Johnson route provably cannot discharge #389's core anywhere below
rate `k/(k+4)`. -/
theorem firstBand_aboveJohnson_vacuous_sharp {n k : ℕ} (hk : 5 ≤ k) (hn : k + 4 ≤ n) :
    ¬ n * (k - 1) < (k + 0 + 1) ^ 2 := by
  have h := firstBand_subJohnson_sharp hk hn
  exact aboveJohnson_hyp_false_of_subJohnson (n := n) (k := k) (m := 0) h

/-- High-rate instance `(n, k, m) = (104, 100, 0)`, rate `100/104 ≈ 0.96`: the
above-Johnson discharge is still vacuous — far above the rate-`1/2` regime. -/
example : ¬ (104 : ℕ) * (100 - 1) < (100 + 0 + 1) ^ 2 :=
  firstBand_aboveJohnson_vacuous_sharp (by norm_num) (by norm_num)

end ProximityGap.Ownership
