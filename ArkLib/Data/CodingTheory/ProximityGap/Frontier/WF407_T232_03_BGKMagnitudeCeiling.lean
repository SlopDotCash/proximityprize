/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyKernel

/-!
# WF407 / T232-03 — the exact ceiling of the BGK magnitude `M = |μ_n ∩ −(1+μ_n)|`

The open BGK core (#232, `AdditiveEnergyKernel.lean`) is the *magnitude* of
`M = bgkCount n = #{u ∈ μ_n : −(1+u) ∈ μ_n}`, the additive-energy / `μ_n ∩ (μ_n − 1)`
count of the smooth multiplicative subgroup. `M = 0` in char 0 (coprimality), `M ≥ 1`
iff `char ∣ 2ⁿ − 1` (Mersenne/Fermat obstruction), `6 ∣ M` generically (S₃). The
*upper* magnitude was the open Bourgain/sum-product piece.

This file pins the **exact unconditional ceiling**:

* `bgkCount_le` — `M ≤ n` trivially (`M` is a `Finset.filter` of `μ_n`).
* `neg_one_not_mem_bgk` — `u = −1` is **never** a BGK solution (it forces `−(1 + (−1)) = 0 ∉ μ_n`,
  as `0 ∉ μ_n`). So the BGK set omits the antipodal generator `−1 ∈ μ_n` (even `n`).
* `bgkCount_le_card_sub_one` — hence **`M ≤ n − 1`** whenever `−1 ∈ μ_n` (even `n`, char ≠ 2).
  This is *sharp*: at `p = n + 1` prime (so `μ_n = F_p^×`) every `u ≠ 0, −1` is a solution, giving
  `M = n − 1` (the densest realizable instance, e.g. `n = 16, p = 17`).

**Numerical context (exact probes `scripts/probes/wf407_T232-03-bgk_*.py`).**
`M = deg gcd(Xⁿ−1, (X+1)ⁿ−1)` over `F_p` (separable, `p` odd), `= #{(x,y)∈μ_n² : x+y = c}`
for any `c ≠ 0` (Fermat-curve fiber count). The bad primes are *exactly* the prime divisors of
`Res(Xⁿ−1,(X+1)ⁿ−1)`; for the deployable density `n ∣ p−1` they are all *small* (`p ≲ n·2^O(1)`),
and at genuine prize scale `p ≈ n·2^128` every tested instance gives `M = 0`. The magnitude is thus
trapped in `[0, n−1]` with the worst case at maximal density `p = n + 1`; it carries **no analytic
√-cancellation content** — it is a pure arithmetic gcd/resultant divisibility (the
Mersenne/Fermat/cyclotomic-factor wall), not the Paley/Gauss-period wall.

This ceiling is a clean magnitude bound, not a closure of the prize: it bounds `M` two-sidedly
`0 ≤ M ≤ n−1` but the prize core lives in the *Gauss-period / list* face, not in `M` (the additive-
energy route is √n-deficient, W2). Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- `0 ∉ μ_n` for `0 < n`: a root of unity is a unit. -/
theorem zero_not_mem_nthRoots {n : ℕ} (hn : 0 < n) :
    (0 : F) ∉ nthRootsFinset n (1 : F) := by
  intro h
  rw [mem_nthRootsFinset hn] at h
  rw [zero_pow hn.ne'] at h
  exact zero_ne_one h

/-- **Trivial ceiling.** `M ≤ n` because `bgkCount` is a filtered sub-`Finset` of `μ_n`,
which has exactly `n` elements once `μ_n` is the full root set (or fewer). -/
theorem bgkCount_le (n : ℕ) :
    bgkCount (F := F) n ≤ (nthRootsFinset n (1 : F)).card :=
  Finset.card_filter_le _ _

/-- **`u = −1` is never a BGK solution.** If `u = −1` then `−(1 + u) = 0`, and `0 ∉ μ_n`,
so `u = −1` fails the membership condition `−(1+u) ∈ μ_n`. -/
theorem neg_one_not_mem_bgk {n : ℕ} (hn : 0 < n) :
    (-1 : F) ∉ (nthRootsFinset n (1 : F)).filter
      (fun u => -(1 + u) ∈ nthRootsFinset n (1 : F)) := by
  intro h
  rw [Finset.mem_filter] at h
  have : -(1 + (-1 : F)) = 0 := by ring
  rw [this] at h
  exact zero_not_mem_nthRoots hn h.2

/-- **The exact ceiling `M ≤ n − 1`.** When `−1 ∈ μ_n` (even `n`, char ≠ 2) the BGK solution set is
contained in `μ_n \ {−1}` (since `u = −1` is excluded by `neg_one_not_mem_bgk`), so its cardinality
is at most `|μ_n| − 1`. This is *sharp*: at `p = n + 1` prime (`μ_n = F_p^×`) every `u ∉ {0, −1}`
solves, realizing `M = n − 1` — the absolute worst case of the open magnitude. -/
theorem bgkCount_le_card_sub_one {n : ℕ} (hn : 0 < n)
    (hneg : (-1 : F) ∈ nthRootsFinset n (1 : F)) :
    bgkCount (F := F) n ≤ (nthRootsFinset n (1 : F)).card - 1 := by
  classical
  -- the BGK filter set sits inside μ_n.erase (-1)
  have hsub : (nthRootsFinset n (1 : F)).filter
      (fun u => -(1 + u) ∈ nthRootsFinset n (1 : F))
      ⊆ (nthRootsFinset n (1 : F)).erase (-1) := by
    intro u hu
    rw [Finset.mem_erase]
    refine ⟨?_, (Finset.mem_filter.mp hu).1⟩
    rintro rfl
    exact neg_one_not_mem_bgk hn hu
  calc bgkCount (F := F) n
      = ((nthRootsFinset n (1 : F)).filter
          (fun u => -(1 + u) ∈ nthRootsFinset n (1 : F))).card := rfl
    _ ≤ ((nthRootsFinset n (1 : F)).erase (-1)).card := Finset.card_le_card hsub
    _ = (nthRootsFinset n (1 : F)).card - 1 := Finset.card_erase_of_mem hneg

/-- **Corollary at the smooth domain.** For `n = 2^k` (`k ≥ 1`) over a field with `−1 ∈ μ_n` and
`|μ_n| = n` (the deployed case `n ∣ q − 1`), the magnitude is trapped `M ≤ 2^k − 1`. Combined with
`AdditiveEnergyKernel.bgkCount_eq_zero_of_coprime` (`M = 0` off the bad primes) and
`AdditiveEnergySixDvd.six_dvd_bgkCount` (`6 ∣ M` generically), the open BGK count `M` lies in
`{0} ∪ {6, 12, …} ∩ [0, n−1]` — a *finite arithmetic* range with no analytic √-cancellation content,
realized at maximal density `p = n + 1`. -/
theorem bgkCount_two_pow_le {k : ℕ}
    (hcard : (nthRootsFinset (2 ^ k) (1 : F)).card = 2 ^ k)
    (hneg : (-1 : F) ∈ nthRootsFinset (2 ^ k) (1 : F)) :
    bgkCount (F := F) (2 ^ k) ≤ 2 ^ k - 1 := by
  have h := bgkCount_le_card_sub_one (n := 2 ^ k) (Nat.two_pow_pos k) hneg
  rwa [hcard] at h

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount_le_card_sub_one
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.neg_one_not_mem_bgk
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount_two_pow_le
