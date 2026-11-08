/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The char-0 subset-sum spectrum of the 2-power subgroup: exact closed form (#444)

For the 2-power subgroup `μ_n` (`n = 2^μ`, the `n`-th roots of unity), the **depth-`r` subset-sum spectrum
cardinality** is `N_r(ℂ) = |{ Σ_{z∈S} z : S ⊆ μ_n, |S| = r }|` (distinct complex subset sums). By the
in-tree `DeepBandSubsetSumSpectrum.witness_pin` (each deep-band bad scalar is `γ_S = −Σ_{z∈S} z`), this is
exactly the **deep-band bad-scalar count `#bad_r`** whose growth law is the master open δ\* question.

**Exact closed form (this session, verified exact at `n = 8, 16` against the spectrum probe).** Via the
antipodal cross-polytope reduction (`ζ^a ↦ ±e_{a mod m}`, `m = n/2`; the only relation among `2^μ`-th roots
is `ζ^{a+m} = −ζ^a`), a size-`r` subset's sum is determined by its net vector `v ∈ {−1,0,1}^m`: a vector
with `k` nonzero entries uses `k` elements (the `±1`'s) plus pairs (each absorbing 2 elements with net 0),
so `|S| = r` is achievable iff `k ≡ r (mod 2)` and `k ≤ min(r, 2m−r)`, and there are `C(m,k)·2^k` such
vectors. Hence
```
N_r(ℂ) = Σ_{k ≡ r (mod 2),  0 ≤ k ≤ min(r, 2m−r)}  C(m, k) · 2^k.
```
This **matches 0xSolace's `spectsym` probe exactly** — `n=8`: `[1,8,25,40,41,40,25,8,1]`; `n=16`: the
palindrome up to `3281`. It extends `spectsym` from the *symmetry* `N_r = N_{n−r}` (proven there
structurally) to the *exact count*.

This file defines the closed-form count and proves:
- `spectrumCountRaw m r` — the **canonical raw coefficient helper** (the filtered binomial/power sum).
  Contract: it is the intended count only on the feasible domain `r ≤ 2m`; for even `r > 2m` the
  truncated subtraction `2m − r = 0` leaves the `k = 0` term, e.g. `spectrumCountRaw 4 10 = 1`
  although no `10`-subset of an `8`-element set exists (`spectrumCountRaw_oversized_example`);
- `spectrumCount m r` — the guarded count interface, **`0` outside the feasible range `r > 2m`**
  (audit R-138), equal to the raw helper on `r ≤ 2m`;
- the **palindrome** `N_r = N_{2m − r}` (`0xSolace`'s `spectsym`, here for the closed form — nearly
  definitional: `min(r,2m−r)` and the parity class are both `r ↔ 2m−r` symmetric), proved once for the
  raw helper (`spectrumCountRaw_palindrome`) and reused (also by `SpectrumGFCoeffPalindrome`);
- the verified small values (`m = 4`: `1,8,25,40,41,…`).

**HONESTY.** No theorem here identifies `spectrumCount` with an actual subset-sum spectrum: the
cross-polytope enumeration `N_r(ℂ) = spectrumCount` is the cited antipodal/cyclotomic result (same status as
`_CharZeroEnergyClosedForm`) plus the small numeric checks below. The characteristic-`p` transfer
`N_r(F_p) = N_r(ℂ)` is a separate, **unproved** step: having fewer char-0 values than `p` (the "dilute"
heuristic `N_r(ℂ) ≪ p`) does not by itself make their reductions distinct; the actual condition is that no
difference of two distinct char-0 subset sums lies in the chosen prime ideal above `p` (a norm/resultant
non-divisibility condition, cf. audit R-093). At the prize-binding depth `r = ρn+1` the char-0 count is
exponential, `≫ p`, so the `F_p` spectrum is collision-saturated and `p`-dependent (the BGK/BCHKS wall).
Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.SubsetSumSpectrum

/-- **Canonical raw closed-form coefficient.**
`spectrumCountRaw m r = Σ_{k≡r(2), k≤min(r,2m−r)} C(m,k)·2^k` (`m = n/2`), with truncated `ℕ`
subtraction.  Contract: meaningful only for `r ≤ 2m` (see `spectrumCountRaw_oversized_example`). -/
def spectrumCountRaw (m r : ℕ) : ℕ :=
  ∑ k ∈ (range (min r (2 * m - r) + 1)).filter (fun k => k % 2 = r % 2), m.choose k * 2 ^ k

/-- **The char-0 subset-sum spectrum closed form (guarded count interface).**  Equal to the raw
closed form on the feasible domain `r ≤ 2m`, and `0` for `r > 2m`, where no `r`-subset of the
`2m`-element set exists. -/
def spectrumCount (m r : ℕ) : ℕ :=
  if r ≤ 2 * m then spectrumCountRaw m r else 0

/-- On the feasible domain the guarded count is the raw closed form. -/
theorem spectrumCount_eq_raw {m r : ℕ} (hr : r ≤ 2 * m) :
    spectrumCount m r = spectrumCountRaw m r := if_pos hr

/-- Outside the feasible domain the guarded count is `0`. -/
theorem spectrumCount_of_lt {m r : ℕ} (hr : 2 * m < r) : spectrumCount m r = 0 :=
  if_neg (by omega)

/-- **Boundary of the raw formula (audit R-138).**  The raw closed form returns `1` for the
impossible `10`-subsets of an `8`-element set, while the guarded count returns `0`. -/
theorem spectrumCountRaw_oversized_example :
    spectrumCountRaw 4 10 = 1 ∧ spectrumCount 4 10 = 0 := by
  refine ⟨?_, spectrumCount_of_lt (by norm_num)⟩
  unfold spectrumCountRaw
  decide

/-- **The raw palindrome (proved once; `spectsym`, for the closed form).** `N_r = N_{2m−r}`, i.e.
`N_r = N_{n−r}`. Both the range bound `min(r, 2m−r)` and the parity class `k ≡ r (mod 2)` are
invariant under `r ↦ 2m−r` (since `2m` is even), so the two sums are over the *same* index set. -/
theorem spectrumCountRaw_palindrome (m r : ℕ) (hr : r ≤ 2 * m) :
    spectrumCountRaw m r = spectrumCountRaw m (2 * m - r) := by
  unfold spectrumCountRaw
  have hmin : min r (2 * m - r) = min (2 * m - r) (2 * m - (2 * m - r)) := by omega
  have hpar : ∀ k, (k % 2 = r % 2) = (k % 2 = (2 * m - r) % 2) := by
    intro k; have : r % 2 = (2 * m - r) % 2 := by omega
    rw [this]
  rw [hmin]
  apply Finset.sum_congr
  · congr 1; ext k; simp only [mem_filter, hpar k]
  · intro k _; rfl

/-- **The palindrome for the guarded count.** `N_r = N_{2m−r}` for `r ≤ 2m`. -/
theorem spectrumCount_palindrome (m r : ℕ) (hr : r ≤ 2 * m) :
    spectrumCount m r = spectrumCount m (2 * m - r) := by
  rw [spectrumCount_eq_raw hr, spectrumCount_eq_raw (by omega : 2 * m - r ≤ 2 * m),
    spectrumCountRaw_palindrome m r hr]

/-- Verified small values (`m = 4`, i.e. `n = 8`): the spectrum sequence `1, 8, 25, 40, 41` for `r = 0..4`
(palindromic continuation `40, 25, 8, 1`), matching the `spectsym` probe `[1,8,25,40,41,40,25,8,1]`. -/
theorem spectrumCount_m4_values :
    spectrumCount 4 0 = 1 ∧ spectrumCount 4 1 = 8 ∧ spectrumCount 4 2 = 25 ∧
    spectrumCount 4 3 = 40 ∧ spectrumCount 4 4 = 41 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold spectrumCount spectrumCountRaw; decide)

/-- `n = 16` (`m = 8`) central values, matching the probe palindrome peak `3280, 3281`. -/
theorem spectrumCount_m8_peak :
    spectrumCount 8 7 = 3280 ∧ spectrumCount 8 8 = 3281 := by
  refine ⟨?_, ?_⟩ <;> (unfold spectrumCount spectrumCountRaw; decide)

/-- **Endpoint non-vacuity** (`spectsym`'s `spectrum_zero_card_one`): `N_0 = 1`. -/
theorem spectrumCount_zero (m : ℕ) : spectrumCount m 0 = 1 := by
  rw [spectrumCount_eq_raw (Nat.zero_le _)]
  unfold spectrumCountRaw
  have h : (range (min 0 (2 * m - 0) + 1)).filter (fun k => k % 2 = 0 % 2) = {0} := by
    ext k; simp only [mem_filter, mem_range, mem_singleton]; omega
  rw [h]; simp

/-- **Depth 1**: `N_1 = n = 2m` (the `n` singletons are distinct in char 0). -/
theorem spectrumCount_one (m : ℕ) (hm : 1 ≤ m) : spectrumCount m 1 = 2 * m := by
  rw [spectrumCount_eq_raw (by omega)]
  unfold spectrumCountRaw
  have h : (range (min 1 (2 * m - 1) + 1)).filter (fun k => k % 2 = 1 % 2) = {1} := by
    ext k; simp only [mem_filter, mem_range, mem_singleton]; omega
  rw [h]; simp only [Finset.sum_singleton, Nat.choose_one_right, pow_one]; ring

end ProximityGap.Frontier.SubsetSumSpectrum

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCount_palindrome
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCountRaw_palindrome
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCountRaw_oversized_example
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCount_m4_values
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCount_one
