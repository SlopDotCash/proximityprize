/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# The packing bad-scalar bound provably misses the deep band (#389/#371)

The q-independent packing bound `mca_badscalar_packing` (`SinglePencilQIndependence.lean`) gives
`#bad ≤ C(n, k+1)/C(a, k+1)`, which at the deep band (`a = r+1`, `k+1 = r`, `n = 2m`, `r = m = n/2`)
reads `#bad ≤ C(2m, m)/(m+1)`.  The KKH26 supply budget there is `2^r·C(n/2, r) = 2^m`.  This file
machine-checks that the packing **upper bound strictly exceeds** that supply budget at the deep band:

> **`packing_exceeds_budget_deep_band`** — for `m ≥ 5`, `(m+1)·2^m < C(2m, m)`.

So the packing route cannot establish `CensusDomination` (`#bad ≤ supply`) at `r = n/2`.  This is the
machine-checked counterpart of `probe_packing_crossover.py`: the elementary q-independent route
covers only up to `r = Θ(√(n log n))` (the moment-method / window `1/log n` scale), and the deep band
`r ~ n/2` — the deployed prize window — is provably beyond it, i.e. the genuinely open core.

(The proven `mca_badscalar_packing` is correct and unaffected; this only delimits the radius range
its bound is strong enough to pin, correcting the `~3n/8` prose extrapolation to `Θ(√(n log n))`.)
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

namespace ArkLib.ProximityGap.PackingDeepBandMiss

/-- `m² + m ≤ 2^m` for `m ≥ 5` (quadratic-beats-exponential, by `Nat.le_induction`). -/
theorem two_pow_ge_sq_add {m : ℕ} (hm : 5 ≤ m) : m ^ 2 + m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h2k : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    nlinarith [ih, h2k, hk]

/-- **The packing bound exceeds the supply budget at the deep band.** For `m ≥ 5`, the central
binomial `C(2m, m)` exceeds `(m+1)·2^m`, i.e. the packing upper bound `C(2m,m)/(m+1)` on the
bad-scalar count is strictly larger than the deep-band supply budget `2^m`.  Hence the elementary
`mca_badscalar_packing` route cannot establish `CensusDomination` at `r = n/2`, and the deep band
(the deployed prize window) is beyond its reach — the open core. -/
theorem packing_exceeds_budget_deep_band {m : ℕ} (hm : 5 ≤ m) :
    (m + 1) * 2 ^ m < (2 * m).choose m := by
  -- central binomial lower bound: `4^m < m · C(2m, m)`
  have h4 : 4 ^ m < m * (2 * m).choose m := by
    have := Nat.four_pow_lt_mul_centralBinom m (by omega)
    rwa [Nat.centralBinom_eq_two_mul_choose] at this
  -- `m·(m+1) ≤ 2^m`
  have hpoly : m * (m + 1) ≤ 2 ^ m := by nlinarith [two_pow_ge_sq_add hm]
  -- `4^m = 2^m · 2^m`
  have h44 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
  -- chain and cancel the positive factor `m`
  have key : m * ((m + 1) * 2 ^ m) < m * (2 * m).choose m := by
    calc m * ((m + 1) * 2 ^ m) = (m * (m + 1)) * 2 ^ m := by ring
      _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ hpoly
      _ = 4 ^ m := h44.symm
      _ < m * (2 * m).choose m := h4
  exact Nat.lt_of_mul_lt_mul_left key

/-- **Positive coverage of the packing route below `√n`.** If `j·(j+3) ≤ 2N` for every `j < r`
(i.e. `r ≲ √(2N)`), the packing upper bound `C(2N,r)/(r+1)` is at most the supply budget
`2^r·C(N,r)`: precisely, `C(2N,r) ≤ (r+1)·2^r·C(N,r)`.  So the q-independent packing route proves
`CensusDomination` for `r` up to `Θ(√n)`.  Together with `packing_exceeds_budget_deep_band` (which
fails it at `r = n/2`), this **sandwiches** the elementary route's reach: covered for `r ≲ √n`,
missed at the deep band — the open core is exactly the band in between (`Θ(√(n log n))` ↔ `n/2`). -/
theorem packing_covers (N : ℕ) :
    ∀ r, (∀ j, j < r → j * (j + 3) ≤ 2 * N) →
      (2 * N).choose r ≤ (r + 1) * 2 ^ r * N.choose r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hcond
    have hr : r * (r + 3) ≤ 2 * N := hcond r (Nat.lt_succ_self r)
    have hP : (2 * N).choose r ≤ (r + 1) * 2 ^ r * N.choose r :=
      ih (fun j hj => hcond j (Nat.lt_succ_of_lt hj))
    have hrN : r ≤ N := by nlinarith [hr]
    have e1 : (2 * N).choose (r + 1) * (r + 1) = (2 * N).choose r * (2 * N - r) :=
      Nat.choose_succ_right_eq (2 * N) r
    have e2 : N.choose (r + 1) * (r + 1) = N.choose r * (N - r) :=
      Nat.choose_succ_right_eq N r
    obtain ⟨a, ha⟩ : ∃ a, N = r + a := ⟨N - r, by omega⟩
    have hsub2 : 2 * N - r = r + 2 * a := by omega
    have hsubN : N - r = a := by omega
    have hnum : (r + 1) * (2 * N - r) ≤ 2 * (r + 2) * (N - r) := by
      rw [hsub2, hsubN]
      have hra : r * r + r ≤ 2 * a := by nlinarith [hr, ha]
      nlinarith [hra]
    have hstep : (2 * N).choose (r + 1) * (r + 1)
        ≤ ((r + 1 + 1) * 2 ^ (r + 1) * N.choose (r + 1)) * (r + 1) := by
      calc (2 * N).choose (r + 1) * (r + 1)
          = (2 * N).choose r * (2 * N - r) := e1
        _ ≤ ((r + 1) * 2 ^ r * N.choose r) * (2 * N - r) := Nat.mul_le_mul_right _ hP
        _ = (2 ^ r * N.choose r) * ((r + 1) * (2 * N - r)) := by ring
        _ ≤ (2 ^ r * N.choose r) * (2 * (r + 2) * (N - r)) := Nat.mul_le_mul_left _ hnum
        _ = ((r + 1 + 1) * 2 ^ (r + 1) * N.choose r) * (N - r) := by ring
        _ = ((r + 1 + 1) * 2 ^ (r + 1)) * (N.choose r * (N - r)) := by ring
        _ = ((r + 1 + 1) * 2 ^ (r + 1)) * (N.choose (r + 1) * (r + 1)) := by rw [e2]
        _ = ((r + 1 + 1) * 2 ^ (r + 1) * N.choose (r + 1)) * (r + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hstep (Nat.succ_pos r)

/-- Clean `√n` form of `packing_covers`: `r² ≤ N ⟹ C(2N,r) ≤ (r+1)·2^r·C(N,r)`.  The packing route
proves `CensusDomination` for every radius up to `r ≤ ⌊√N⌋`. -/
theorem packing_covers_sqrt {N r : ℕ} (h : r * r ≤ N) :
    (2 * N).choose r ≤ (r + 1) * 2 ^ r * N.choose r := by
  apply packing_covers N r
  intro j hj
  nlinarith [hj, h, Nat.zero_le j]

end ArkLib.ProximityGap.PackingDeepBandMiss

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.PackingDeepBandMiss.two_pow_ge_sq_add
#print axioms ArkLib.ProximityGap.PackingDeepBandMiss.packing_exceeds_budget_deep_band
#print axioms ArkLib.ProximityGap.PackingDeepBandMiss.packing_covers
#print axioms ArkLib.ProximityGap.PackingDeepBandMiss.packing_covers_sqrt
