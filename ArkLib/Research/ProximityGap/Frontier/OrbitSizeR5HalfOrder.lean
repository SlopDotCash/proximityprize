/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR5Bound

/-!
# The `r = 5` deep-band ORBIT SIZE is `n/2` — the half-order resonance factor (#444)

`DeepBandR5Bound` (O181) records the `r = 5` deep-band `#bad`-scalar decomposition
`#bad₅ = 1 + (n/2)·full_orb` (B2 equivariance), where the `n/2` is the **orbit SIZE** of the B2
dilation `γ ↦ g^{e−f}·γ` for the measured `r = 5` maximizer line `(e, f) = (n/2 + 1, n − 1)`.  The
file derives `d = n/gcd(n, e−f) = n/2` **in prose** (`since gcd(n, n/2 + 2) = 2 …`) but does not
prove the orbit-size factor as a theorem.  This is the SAME prose-vs-theorem gap that O197
(`_OrbitSizeEqN`) closed for the `r = 3, 4` ORDER-2 rungs (where the orbit size is `n`); here the
`r = 5` maximizer is the **HALF-ORDER** `d = n/2` resonance (NOT the full order `n`), so the factor
is genuinely different and uncontested.

This file supplies the arithmetic heart of the half-order orbit-size factor:

> **`gcd(2^k, 2^{k-1} + 2) = 2`** for `k ≥ 3`, hence the orbit period
> **`d = 2^k / gcd(2^k, n/2 + 2) = 2^{k-1} = n/2`**.

## Mechanism (pure-ℕ, NOT a moment / character method)

The B2 shift is `e − f = (n/2 + 1) − (n − 1) = −(n/2 − 2) ≡ n/2 + 2 (mod n)`.  Write `n = 2^k`.
Then `n/2 + 2 = 2^{k-1} + 2 = 2·(2^{k-2} + 1)` with `2^{k-2} + 1` **odd** (`k ≥ 3`), so the only
common factor of `2 (2^{k-2}+1)` with `2^k` is the single `2`: `gcd(2^k, 2^{k-1}+2) = 2`.  The orbit
period of an order-`n` root of unity under the dilation by the `(e−f)`-th power is
`n / gcd(n, e−f) = 2^k / 2 = 2^{k-1} = n/2`.  Combined with `#bad₅ = 1 + (n/2)·full_orb`
(`DeepBandR5Bound` + the general-`g` orbit-count normal form `OrbitCount5GeneralNormalForm`), this
pins BOTH factors of the `r = 5` decomposition: orbit SIZE `= n/2`, orbit COUNT `= full_orb(g)`.

## Honest scope

A pure-ℕ structural cardinality fact (the half-order orbit-size factor of the `r = 5` rung),
parallel to O197's `n` for the order-2 rungs.  It does **NOT** close CORE
`M(μ_n) ≤ C·√(n·log(p/n))`: the `r = 5` rung is already strictly sub-budget; the prize binds the
deep rung `r ≈ log n` (= the BGK/BCHKS wall), untouched.  Character-sum-free, char-agnostic.

Probe: `scripts/probes/probe_orbit_size_r5_halforder.py` (orbit size `= n/gcd(n, n/2+2) = n/2` on
prize tower `n = 2^k`, `k = 4..16`; never `n = q − 1`).
-/

namespace ArkLib.ProximityGap.OrbitSizeR5HalfOrder

/-- **The half-order gcd fact.**  For `k ≥ 3`, `gcd(2^k, 2^{k-1} + 2) = 2`.  (The B2 shift
`n/2 + 2 = 2^{k-1} + 2 = 2·(2^{k-2}+1)` has odd cofactor, so its only common factor with `2^k` is
`2`.) -/
theorem gcd_pow_half_shift (k : ℕ) (hk : 3 ≤ k) :
    Nat.gcd (2 ^ k) (2 ^ (k - 1) + 2) = 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have h1 : (2 : ℕ) ^ (j + 3) = 4 * 2 ^ (j + 1) := by ring
  have h2 : (2 : ℕ) ^ (j + 3 - 1) + 2 = 2 * (2 ^ (j + 1) + 1) := by
    have he : j + 3 - 1 = j + 2 := by omega
    rw [he]; ring
  rw [h1, h2, show (4 * 2 ^ (j + 1)) = 2 * (2 * 2 ^ (j + 1)) by ring, Nat.gcd_mul_left]
  have heven : Even (2 ^ (j + 1)) := by
    rw [pow_succ]; exact (even_two).mul_left _
  have hodd : Odd (2 ^ (j + 1) + 1) := Even.add_one heven
  have hc2 : Nat.Coprime 2 (2 ^ (j + 1) + 1) := (Nat.coprime_two_left).mpr hodd
  have hc1 : Nat.Coprime (2 ^ (j + 1)) (2 ^ (j + 1) + 1) := by
    simp [Nat.Coprime, Nat.gcd_self_add_right]
  have hg : Nat.gcd (2 * 2 ^ (j + 1)) (2 ^ (j + 1) + 1) = 1 :=
    Nat.Coprime.mul_left hc2 hc1
  rw [hg]

/-- **The `r = 5` orbit SIZE is `n/2`.**  For the prize tower `n = 2^k` (`k ≥ 3`), the B2 dilation
orbit period for the measured `r = 5` maximizer `(e, f) = (n/2+1, n−1)` (shift `n/2 + 2`) is
`d = n / gcd(n, n/2 + 2) = 2^{k-1} = n/2`.  This is the half-order resonance factor (NOT the full
order `n` of the order-2 `r = 3, 4` rungs, cf. O197). -/
theorem orbit_size_r5_eq_half (k : ℕ) (hk : 3 ≤ k) :
    2 ^ k / Nat.gcd (2 ^ k) (2 ^ (k - 1) + 2) = 2 ^ (k - 1) := by
  rw [gcd_pow_half_shift k hk]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have he : j + 3 - 1 = j + 2 := by omega
  rw [he, show (2 : ℕ) ^ (j + 3) = 2 * 2 ^ (j + 2) by rw [pow_succ]; ac_rfl,
    Nat.mul_div_cancel_left _ (by norm_num)]

/-- The orbit size strictly halves the group: `n/2 < n` (the half-order resonance is a PROPER
sub-period), so the `r = 5` orbits are genuinely smaller than the order-2 (`r = 3, 4`) orbits of
size `n`.  (`2^{k-1} < 2^k` for `k ≥ 1`.) -/
theorem orbit_size_r5_lt_n (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (k - 1) < 2 ^ k := by
  have hlt : k - 1 < k := by omega
  exact Nat.pow_lt_pow_right (a := 2) (by norm_num) hlt

/-- Anchor sanity: the orbit-size factor reproduces the kernel-measured `d` at `n = 16, 32, 64, 128`
(matching `DeepBandR5Bound`'s `n=16: d=8`, `n=32: d=16`, `n=64: d=32`, `n=128: d=64`). -/
theorem orbit_size_anchors :
    2 ^ 4 / Nat.gcd (2 ^ 4) (2 ^ 3 + 2) = 8 ∧
    2 ^ 5 / Nat.gcd (2 ^ 5) (2 ^ 4 + 2) = 16 ∧
    2 ^ 6 / Nat.gcd (2 ^ 6) (2 ^ 5 + 2) = 32 ∧
    2 ^ 7 / Nat.gcd (2 ^ 7) (2 ^ 6 + 2) = 64 :=
  ⟨by decide, by decide, by decide, by decide⟩

end ArkLib.ProximityGap.OrbitSizeR5HalfOrder
