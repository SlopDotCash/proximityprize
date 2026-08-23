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

This file defines the closed-form `spectrumCount m r` and proves:
- the **palindrome** `spectrumCount m r = spectrumCount m (2m − r)` (`0xSolace`'s `spectsym`, here for the
  closed form — nearly definitional: `min(r,2m−r)` and the parity class are both `r ↔ 2m−r` symmetric);
- the verified small values (`m = 4`: `1,8,25,40,41,…`).

**HONESTY.** `N_r(F_p) = N_r(ℂ) = spectrumCount` holds only in the **dilute** regime `N_r(ℂ) ≪ p`. At the
prize-binding depth `r = ρn+1` the char-0 count is exponential, `≫ p`, so the `F_p` spectrum is
collision-saturated and `p`-dependent (the BGK/BCHKS wall). The bridge `N_r(ℂ) = spectrumCount` is the cited
antipodal/cyclotomic result (same status as `_CharZeroEnergyClosedForm`). Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.SubsetSumSpectrum

/-- **The char-0 subset-sum spectrum closed form.** `spectrumCount m r = Σ_{k≡r(2), k≤min(r,2m−r)} C(m,k)·2^k`
(`m = n/2`). The sum ranges over `k ∈ {0,…,min(r,2m−r)}` with `k ≡ r (mod 2)`. -/
def spectrumCount (m r : ℕ) : ℕ :=
  ∑ k ∈ (range (min r (2 * m - r) + 1)).filter (fun k => k % 2 = r % 2), m.choose k * 2 ^ k

/-- **The palindrome (`spectsym`, for the closed form).** `N_r = N_{2m−r}`, i.e. `N_r = N_{n−r}`. Both the
range bound `min(r, 2m−r)` and the parity class `k ≡ r (mod 2)` are invariant under `r ↦ 2m−r` (since `2m`
is even), so the two sums are over the *same* index set. -/
theorem spectrumCount_palindrome (m r : ℕ) (hr : r ≤ 2 * m) :
    spectrumCount m r = spectrumCount m (2 * m - r) := by
  unfold spectrumCount
  have hmin : min r (2 * m - r) = min (2 * m - r) (2 * m - (2 * m - r)) := by omega
  have hpar : ∀ k, (k % 2 = r % 2) = (k % 2 = (2 * m - r) % 2) := by
    intro k; have : r % 2 = (2 * m - r) % 2 := by omega
    rw [this]
  rw [hmin]
  apply Finset.sum_congr
  · congr 1; ext k; simp only [mem_filter, hpar k]
  · intro k _; rfl

/-- Verified small values (`m = 4`, i.e. `n = 8`): the spectrum sequence `1, 8, 25, 40, 41` for `r = 0..4`
(palindromic continuation `40, 25, 8, 1`), matching the `spectsym` probe `[1,8,25,40,41,40,25,8,1]`. -/
theorem spectrumCount_m4_values :
    spectrumCount 4 0 = 1 ∧ spectrumCount 4 1 = 8 ∧ spectrumCount 4 2 = 25 ∧
    spectrumCount 4 3 = 40 ∧ spectrumCount 4 4 = 41 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold spectrumCount; decide)

/-- `n = 16` (`m = 8`) central values, matching the probe palindrome peak `3280, 3281`. -/
theorem spectrumCount_m8_peak :
    spectrumCount 8 7 = 3280 ∧ spectrumCount 8 8 = 3281 := by
  refine ⟨?_, ?_⟩ <;> (unfold spectrumCount; decide)

/-- **Endpoint non-vacuity** (`spectsym`'s `spectrum_zero_card_one`): `N_0 = 1`. -/
theorem spectrumCount_zero (m : ℕ) : spectrumCount m 0 = 1 := by
  unfold spectrumCount
  have h : (range (min 0 (2 * m - 0) + 1)).filter (fun k => k % 2 = 0 % 2) = {0} := by
    ext k; simp only [mem_filter, mem_range, mem_singleton]; omega
  rw [h]; simp

/-- **Depth 1**: `N_1 = n = 2m` (the `n` singletons are distinct in char 0). -/
theorem spectrumCount_one (m : ℕ) (hm : 1 ≤ m) : spectrumCount m 1 = 2 * m := by
  unfold spectrumCount
  have h : (range (min 1 (2 * m - 1) + 1)).filter (fun k => k % 2 = 1 % 2) = {1} := by
    ext k; simp only [mem_filter, mem_range, mem_singleton]; omega
  rw [h]; simp only [Finset.sum_singleton, Nat.choose_one_right, pow_one]; ring

end ProximityGap.Frontier.SubsetSumSpectrum

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCount_palindrome
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCount_m4_values
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumCount_one
