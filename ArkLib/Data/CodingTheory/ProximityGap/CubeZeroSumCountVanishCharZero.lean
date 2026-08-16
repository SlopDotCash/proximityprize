/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreeRootsSumZeroCharZero
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

/-!
# The order-3 zero-sum count of `μ_n ⊆ ℂ` VANISHES in char 0 when `3 ∤ n` (#444, #407)

The signed period-power identity (`SignedPeriodZeroSumBridge`) puts the located thinness-essential
prize object into the form `∑_{ψ≠0} η_ψ^r = q·zeroSumCount S r − |S|^r` (over a *finite* field `F_q`).
The `ℕ`-valued `zeroSumCount S r` factor is the object that carries the thin signal; recent bricks
constrain it (it is EVEN, `SignedZeroSumCountEven.two_dvd_zeroSumCount`; divisible by `|S|` for a
subgroup). This file pins its **exact value at the first nontrivial ODD order `r = 3`** over the prize
subgroup `μ_n ⊆ ℂ` (char 0): when `3 ∤ n` — in particular for every prize-regime `n = 2^a` —

>   `zeroSumCount (μ_n : Finset ℂ) 3 = 0`.

## Mechanism

A zero-sum triple `(a,b,c)` of `n`-th roots of unity in `ℂ` with `a + b + c = 0` is *impossible*
when `3 ∤ n` (Mann rigidity, `ThreeRoots.no_three_roots_sum_zero` — which needs **no** distinctness:
repeats `2a + c = 0` fail by magnitude `|2a| = 2 ≠ 1`, and the genuinely-distinct case fails by
`3 ∤ n`). So the zero-sum triple set is empty and `zeroSumCount μ_n 3 = 0`.

## Why this is prize-relevant (honest scope)

The cube-order `zeroSumCount` is EXACTLY `0` over ℂ, so there is **no** cube-order zero-sum residual in
char 0: the whole order-3 content is the diagonal. The nontrivial signed cancellation that is the
open BGK wall therefore first appears at the deep orders `r ≈ log q` over the *finite field* `F_q`,
where the `F_q`-reduction creates the zero-sum coincidences that char 0 forbids — cf. the probe that
`zeroSumCount(μ_n, 3)` over `F_p` is `0` in the deep Sidon regime `p > n³` but becomes nonzero only
at small `p` and structured Fermat primes. This LOCATES the cube-order prize content squarely in the
finite-field reduction, not in any char-0 / archimedean obstruction.

NON-MOMENT (an exact additive-tuple count over ℂ; no `|·|`), an EXTEND that sits on the in-tree
Mann-rigidity lemma. NOT a CORE bound — `CORE M(μ_n) ≤ C·√(n·log(q/n))` lives at the deep `F_q`
orders. `CORE OPEN.`

Probe `probe_zsc3_char0.py`: `zeroSumCount(μ_n, 3) = 0` over ℂ for `n = 4,8,16,32,64` (ALL ordered
triples with repeats).

Issues #444, #407.
-/

set_option linter.unusedDecidableInType false


open scoped BigOperators

namespace ArkLib.ProximityGap.CubeZeroSumCountVanish

open Finset Polynomial

/-- **The order-3 zero-sum count of `μ_n ⊆ ℂ` vanishes when `3 ∤ n`.**
No triple of `n`-th roots of unity (with repeats allowed) sums to `0` in char 0 unless `3 ∣ n`
(Mann rigidity, `no_three_roots_sum_zero`), so the zero-sum triple set is empty. -/
theorem zeroSumCount_three_nthRoots_eq_zero {n : ℕ} (hn : n ≠ 0) (h3 : ¬ (3 ∣ n)) :
    ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount
      (Polynomial.nthRootsFinset n (1 : ℂ)) 3 = 0 := by
  classical
  rw [ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro c hc hsum
  rw [Fintype.mem_piFinset] at hc
  -- the three coordinates are `n`-th roots of unity
  have h0 : (c 0) ^ n = 1 :=
    (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) (1 : ℂ)).mp (hc 0)
  have h1 : (c 1) ^ n = 1 :=
    (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) (1 : ℂ)).mp (hc 1)
  have h2 : (c 2) ^ n = 1 :=
    (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) (1 : ℂ)).mp (hc 2)
  -- the zero-sum condition `∑ i, c i = 0` is `c 0 + c 1 + c 2 = 0`
  have hsum3 : c 0 + c 1 + c 2 = 0 := by
    rw [Fin.sum_univ_three] at hsum; exact hsum
  exact ProximityGap.ThreeRoots.no_three_roots_sum_zero hn h3 h0 h1 h2 hsum3

end ArkLib.ProximityGap.CubeZeroSumCountVanish

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CubeZeroSumCountVanish.zeroSumCount_three_nthRoots_eq_zero
