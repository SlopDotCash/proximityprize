/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandProductionSubJohnson

/-!
# Production band strictly sub-Johnson at every multiplicity (#389)

`DeepBandProductionSubJohnson.lean` pinned the *first* deep band (`m = 0`) at rate
`≤ 1/2` as strictly sub-Johnson, hence outside the in-tree above-Johnson discharge.
This file lifts that to **every multiplicity `m`**: at rate `≤ 1/2` (`2k ≤ n`), any
band whose threshold satisfies the rate-`1/2` Johnson budget `(k+m+1)² ≤ 2k(k−1)`
is strictly sub-Johnson, so the above-Johnson discharge `subJohnsonListBound_aboveJohnson`
is provably inapplicable there.  `firstBand_subJohnson` (`m = 0`) is recovered as a
corollary, and a non-trivial multiplicity instance (`m = 39`, `k = 100`, `n = 200`)
is exhibited.

This continues the boundary-pinning of #389: it does **not** close the open
sub-Johnson list bound — it shows the in-tree above-Johnson route cannot reach the
deployed regime at any multiplicity, so that single obligation is genuinely
unavoidable across the whole production band.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

namespace ProximityGap.Ownership

/-- **Production sub-Johnson, general multiplicity.**  At rate `≤ 1/2` (`2k ≤ n`),
any band whose threshold meets the rate-`1/2` Johnson budget `(k+m+1)² ≤ 2k(k−1)`
is strictly sub-Johnson: `(k+m+1)² ≤ n·(k−1)`.  (`(k+m+1)² ≤ 2k(k−1) ≤ n(k−1)`.) -/
theorem production_subJohnson {n k m : ℕ} (hn : 2 * k ≤ n)
    (hm : (k + m + 1) ^ 2 ≤ 2 * k * (k - 1)) :
    (k + m + 1) ^ 2 ≤ n * (k - 1) :=
  hm.trans (by gcongr)

/-- **The above-Johnson discharge is vacuous across the whole production band.**  At
rate `≤ 1/2`, for any multiplicity meeting the rate-`1/2` Johnson budget, the
hypothesis of `subJohnsonListBound_aboveJohnson` is false. -/
theorem production_aboveJohnson_vacuous {n k m : ℕ} (hn : 2 * k ≤ n)
    (hm : (k + m + 1) ^ 2 ≤ 2 * k * (k - 1)) :
    ¬ n * (k - 1) < (k + m + 1) ^ 2 :=
  aboveJohnson_hyp_false_of_subJohnson (production_subJohnson hn hm)

/-- The first deep band (`m = 0`, `5 ≤ k`) recovered from the general criterion. -/
theorem firstBand_subJohnson_general {n k : ℕ} (hk : 5 ≤ k) (hn : 2 * k ≤ n) :
    (k + 0 + 1) ^ 2 ≤ n * (k - 1) := by
  refine production_subJohnson (m := 0) hn ?_
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have hd : 4 ≤ d := by omega
  have : d + 1 - 1 = d := by omega
  rw [this]
  nlinarith [hd]

/-- A non-trivial multiplicity is sub-Johnson: `(n,k,m) = (200, 100, 39)`, rate `1/2`,
multiplicity `39` — the above-Johnson discharge is vacuous, so #389's open core is the
only remaining obligation even at high multiplicity. -/
example : ¬ (200 : ℕ) * (100 - 1) < (100 + 39 + 1) ^ 2 :=
  production_aboveJohnson_vacuous (by norm_num) (by norm_num)

end ProximityGap.Ownership
