/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DyadicOddMomentVanishing
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

/-!
# Every ODD-order zero-sum count of `μ_{2^k} ⊆ ℂ` VANISHES in char 0 (#444, #407)

The signed period-power identity (`SignedPeriodZeroSumBridge`) puts the located thinness-essential
prize object into the form `∑_{ψ≠0} η_ψ^r = q·zeroSumCount S r − |S|^r` (over a finite field `F_q`).
The `ℕ`-valued `zeroSumCount S r` factor carries the thin signal; recent bricks constrain it (it is
EVEN, `SignedZeroSumCountEven.two_dvd_zeroSumCount`; `|S|`-divisible for a subgroup;
`zeroSumCount(μ_n,3) = 0` over ℂ when `3 ∤ n`, `CubeZeroSumCountVanishCharZero`).

This file pins **every ODD-order value at once** over the dyadic prize subgroup `μ_{2^k} ⊆ ℂ`:

>   for every ODD `r`,   `zeroSumCount (μ_{2^k} : Finset ℂ) r = 0`.

It is the general odd-order companion of the order-3 vanishing — it subsumes `r = 3` (which needs
`3 ∤ n`, automatic for `n = 2^k`) and `r = 5, 7, …` in one theorem, in the canonical
`NegationClosedWalk.zeroSumCount` tuple vocabulary.

## Mechanism

A zero-sum `r`-tuple `c : Fin r → ℂ` of `2^k`-th roots of unity gives a multiset
`M = (Finset.univ.val).map c` of `2^k`-th roots with `M.card = r` and `M.sum = ∑ i, c i = 0`.
The in-tree Lam–Leung-at-the-prime-2 theorem
`DyadicOddMoment.even_card_of_vanishing_dyadic_multiset` forces `M.card` to be **even**.  So `r`
even is necessary — for ODD `r` no zero-sum tuple exists and the count is `0`.

## Why this is prize-relevant (honest scope)

The whole ODD-order `zeroSumCount` is EXACTLY `0` over ℂ: NO odd-order zero-sum-residual
in char 0 (the entire odd-grade content is the diagonal). So the signed odd-period-power sums
`∑_{ψ≠0} η_ψ^r = q·0 − n^r = −n^r` are pinned to their diagonal value over ℂ, and the nontrivial
signed cancellation that is the open BGK wall appears ONLY at the deep orders `r ≈ log q` over the
*finite field* `F_q`, where the `F_q`-reduction creates the zero-sum coincidences char 0 forbids.
This LOCATES the entire odd-order prize content squarely in the finite-field reduction.

NON-MOMENT (an exact additive-tuple count over ℂ; no `|·|`), an EXTEND that bridges the in-tree
dyadic odd-moment law into the `zeroSumCount` tuple vocabulary. NOT a CORE bound — `CORE M(μ_n) ≤
C·√(n·log(q/n))` lives at the deep `F_q` even-ish orders. `CORE OPEN.`

Probe `probe_odd_zerosum_charzero.py`: `zeroSumCount(μ_{2^k}, r) = 0` over ℂ for `r ∈ {3,5,7,9}` and
`n = 2,4,8` (ALL ordered tuples with repeats); `probe_quintic_zerosum_charzero.py` for `r = 5`.

Issues #444, #407.
-/

set_option linter.unusedDecidableInType false


open scoped BigOperators

namespace ArkLib.ProximityGap.OddZeroSumCountVanish

open Finset

/-- **Every odd-order zero-sum count of `μ_{2^k} ⊆ ℂ` vanishes.**
A zero-sum `r`-tuple of `2^k`-th roots of unity (`r` odd) would give an odd-cardinality multiset of
`2^k`-th roots with vanishing sum, contradicting the dyadic odd-moment law
(`even_card_of_vanishing_dyadic_multiset`). So the zero-sum `r`-tuple set is empty. -/
theorem zeroSumCount_odd_dyadicRoots_eq_zero {k r : ℕ} (hr : Odd r) :
    ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount
      (Polynomial.nthRootsFinset (2 ^ k) (1 : ℂ)) r = 0 := by
  classical
  rw [ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro c hc hsum
  rw [Fintype.mem_piFinset] at hc
  -- each coordinate is a `2^k`-th root of unity
  have hpos : 0 < 2 ^ k := by positivity
  have hroot : ∀ i, (c i) ^ (2 ^ k) = 1 := fun i =>
    (Polynomial.mem_nthRootsFinset hpos (1 : ℂ)).mp (hc i)
  -- the multiset of coordinate values
  set M : Multiset ℂ := (Finset.univ.val : Multiset (Fin r)).map c with hM
  have hMmem : ∀ z ∈ M, z ^ (2 ^ k) = 1 := by
    intro z hz
    rw [hM, Multiset.mem_map] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact hroot i
  have hMcard : Multiset.card M = r := by
    rw [hM, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hMsum : M.sum = 0 := by
    have : M.sum = ∑ i, c i := by
      rw [hM]; rfl
    rw [this, hsum]
  -- the dyadic odd-moment law forces even cardinality; contradiction with `r` odd
  have heven : Even (Multiset.card M) :=
    DyadicOddMomentVanishing.even_card_of_vanishing_dyadic_multiset hMmem hMsum
  rw [hMcard] at heven
  exact (Nat.not_even_iff_odd.mpr hr) heven

end ArkLib.ProximityGap.OddZeroSumCountVanish

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.OddZeroSumCountVanish.zeroSumCount_odd_dyadicRoots_eq_zero
