/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Bridge B44 — `fhat` odd-vanishing as a character sum over `μ_{2n}` (target E6, #444)

**Spec (B44).** *`fhat` odd-vanishing as a character sum over `μ_{2n}` identically `0`, via
orthogonality of characters / geometric sum.*

## Context — the odd half of the EXACT FFT-graded recursion E6

The odd half of E6 (`#bad_{2n}(k, odd) = 0`, see
`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`) rests on the vanishing of
the degree-`d` *graded character moment*

  `fhat d := ∑_{x ∈ μ_{2n}} x^d`

whenever the graded degree `d` is **not** a multiple of the group order `2n` — in particular for
every **odd** `d` (since `2n` is even, `2n ∤ d`). The companion brick
`_BridgeB35`/`_Bridge05` proves the same vanishing by the **antipodal `−1` involution**; this file
gives the **complementary, sharper proof by the multiplicative-shift / orthogonality argument**
(the discrete-Fourier "geometric sum" route), which covers *every* `d` with `2n ∤ d`, not only odd
`d`.

## The argument (multiplicative shift = orthogonality of characters)

Let `ζ` be a primitive `N`-th root of unity (`N = 2n`), so `μ_N = nthRootsFinset N 1`. The map
`x ↦ ζ · x` is a bijection of `μ_N` onto itself. Reindexing the sum `S = ∑_{x∈μ_N} x^d` by this
bijection multiplies it by `ζ^d`:

  `S = ∑_{x∈μ_N} (ζ x)^d = ζ^d · ∑_{x∈μ_N} x^d = ζ^d · S`,

so `(ζ^d − 1) · S = 0`. When `N ∤ d` the character `x ↦ x^d` is **non-trivial**, i.e.
`ζ^d ≠ 1` (primitivity), hence `ζ^d − 1` is a nonzero element of the integral domain and `S = 0`.
This is exactly orthogonality of the non-trivial multiplicative character `χ_d : x ↦ x^d` against
the trivial one.

## What this file proves (LANDED, axiom-clean)

* `mul_mem_nthRootsFinset`       — `μ_N` is closed under multiplication by a root of unity;
* `shift_bij_sum`                — the multiplicative-shift reindexing `S = ζ^d · S`;
* **`charSum_nthRootsFinset_eq_zero`** — `∑_{x∈μ_N} x^d = 0` whenever `¬ N ∣ d` (the character
  sum / geometric-sum vanishing, target B44);
* `odd_charSum_eq_zero`          — the odd-`d` specialization over `μ_{2n}` (the E6 odd half);
* `Complex.odd_charSum_eq_zero`  — the prize-regime statement over `ℂ`.

All are characteristic-free identities over an integral domain; no char-`p` transfer is needed.

Issue #444.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.BridgeB44

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **`μ_N` is closed under multiplication by a root of unity.** If `ζ^N = 1` and `x ∈ μ_N` then
`ζ·x ∈ μ_N`, because `(ζ·x)^N = ζ^N · x^N = 1·1 = 1`. -/
theorem mul_mem_nthRootsFinset {N : ℕ} (hN : 0 < N) {ζ x : R}
    (hζ : ζ ^ N = 1) (hx : x ∈ nthRootsFinset N (1 : R)) :
    ζ * x ∈ nthRootsFinset N (1 : R) := by
  rw [mem_nthRootsFinset hN 1] at hx ⊢
  rw [mul_pow, hζ, hx, mul_one]

/-- **Multiplicative-shift reindexing (orthogonality identity).** For a root of unity `ζ` (`ζ^N=1`),
reindexing the character sum `S = ∑_{x∈μ_N} x^d` along the bijection `x ↦ ζ·x` of `μ_N` multiplies
it by `ζ^d`:

  `ζ^d · ∑_{x∈μ_N} x^d = ∑_{x∈μ_N} x^d`.

This is the single algebraic input behind orthogonality of the multiplicative character
`x ↦ x^d` against the trivial character. -/
theorem shift_bij_sum {N : ℕ} (hN : 0 < N) {ζ : R} (hζ : ζ ^ N = 1) (d : ℕ) :
    ζ ^ d * ∑ x ∈ nthRootsFinset N (1 : R), x ^ d
      = ∑ x ∈ nthRootsFinset N (1 : R), x ^ d := by
  rw [Finset.mul_sum]
  -- inverse of `x ↦ ζ·x` is `x ↦ ζ^{N-1}·x`, since `ζ·ζ^{N-1} = ζ^N = 1`.
  have hinv' : ζ ^ (N - 1) * ζ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hN, hζ]
  have hinv : ζ * ζ ^ (N - 1) = 1 := by rw [mul_comm]; exact hinv'
  have hζN1 : (ζ ^ (N - 1)) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine Finset.sum_nbij' (fun x => ζ * x) (fun x => ζ ^ (N - 1) * x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact mul_mem_nthRootsFinset hN hζ hx
  · intro x hx; exact mul_mem_nthRootsFinset hN hζN1 hx
  · -- left_inv: ζ^{N-1} * (ζ * x) = x
    intro x _; simp only [← mul_assoc, hinv', one_mul]
  · -- right_inv: ζ * (ζ^{N-1} * x) = x
    intro x _; simp only [← mul_assoc, hinv, one_mul]
  · -- h: x^d = (ζ * x)^d evaluated as g(i x) = ζ^d * x^d... target is `x^d = ζ^d * (ζ*x)^d`? no:
    -- goal is `f x = g (i x)` with f x = ζ^d * x^d (LHS summand) and g (i x) = (ζ*x)^d.
    intro x _; rw [mul_pow]

/-- **Character sum vanishes (target B44).** Over an integral domain, for any primitive `N`-th root
of unity `ζ` and any graded degree `d` with `¬ N ∣ d`, the degree-`d` character sum over `μ_N`
vanishes:

  `∑_{x ∈ μ_N} x^d = 0`.

Proof: `shift_bij_sum` gives `ζ^d · S = S`, i.e. `(ζ^d − 1)·S = 0`; primitivity and `N ∤ d` give
`ζ^d ≠ 1`, so `ζ^d − 1 ≠ 0`, and a domain has no zero divisors, hence `S = 0`. This is exactly
orthogonality of the non-trivial multiplicative character `x ↦ x^d` against the trivial one. -/
theorem charSum_nthRootsFinset_eq_zero {N : ℕ} (hN : 0 < N) {ζ : R}
    (hζ : IsPrimitiveRoot ζ N) {d : ℕ} (hd : ¬ N ∣ d) :
    ∑ x ∈ nthRootsFinset N (1 : R), x ^ d = 0 := by
  have hshift := shift_bij_sum (R := R) hN hζ.pow_eq_one d
  have hne : ζ ^ d - 1 ≠ 0 := by
    intro h
    have : ζ ^ d = 1 := by linear_combination h
    exact hd ((hζ.pow_eq_one_iff_dvd d).mp this)
  have : (ζ ^ d - 1) * ∑ x ∈ nthRootsFinset N (1 : R), x ^ d = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hne
  · exact h

/-- **Odd graded character moment vanishes over `μ_{2n}` (E6 odd half).** For a primitive `2n`-th
root of unity and any **odd** degree `d`, the character sum over `μ_{2n}` is `0`. Special case of
`charSum_nthRootsFinset_eq_zero`: an odd `d` is never divisible by the even modulus `2n`. -/
theorem odd_charSum_eq_zero {n : ℕ} (hn : 0 < n) {ζ : R}
    (hζ : IsPrimitiveRoot ζ (2 * n)) {d : ℕ} (hd : Odd d) :
    ∑ x ∈ nthRootsFinset (2 * n) (1 : R), x ^ d = 0 := by
  refine charSum_nthRootsFinset_eq_zero (by positivity) hζ ?_
  intro hdvd
  have : Even d := even_iff_two_dvd.mpr (dvd_trans ⟨n, rfl⟩ hdvd)
  exact (Nat.not_even_iff_odd.mpr hd) this

end ArkLib.ProximityGap.BridgeB44

namespace ArkLib.ProximityGap.BridgeB44.Complex

open ArkLib.ProximityGap.BridgeB44

/-- **Prize-regime statement over `ℂ`.** The odd graded character moment over the complex
`2n`-th roots of unity vanishes, for any primitive `2n`-th root `ζ` and odd `d`. -/
theorem odd_charSum_eq_zero {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) {d : ℕ} (hd : Odd d) :
    ∑ x ∈ nthRootsFinset (2 * n) (1 : ℂ), x ^ d = 0 :=
  ArkLib.ProximityGap.BridgeB44.odd_charSum_eq_zero hn hζ hd

end ArkLib.ProximityGap.BridgeB44.Complex

#print axioms ArkLib.ProximityGap.BridgeB44.charSum_nthRootsFinset_eq_zero
#print axioms ArkLib.ProximityGap.BridgeB44.odd_charSum_eq_zero
#print axioms ArkLib.ProximityGap.BridgeB44.Complex.odd_charSum_eq_zero
