/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The char-p transfer, weight-4 face: an EXACT decidable form `ord_p(−4) = n` (#444)

**Context.** The prize `M(μ_n) ≤ C√(n log q)` reduces to controlling the **char-p additive-energy excess**
`W_r = E_r(F_p) − E_r(ℂ) ≥ 0` (the failure of the proven char-0 energy bound to *transfer* to char-p). `W_r > 0`
exactly when a weight-`2r` relation among `n`-th roots of unity (`n = 2^μ`) — a true equality over `ℂ` of two
`r`-term root sums — acquires an *extra* solution mod `p`. The smallest such (the weight-4 / `r=4` face) is governed
by the relation `4·ζ⁰ = 3·ζ³ + ζ⁶`, i.e. `4 − 3ζ³ − ζ⁶ = 0`.

**The exact form (this file).** The relation polynomial **factors**:
```
4 − 3X³ − X⁶ = (1 − X³)·(4 + X³).
```
So for a root of unity `g` of order `n = 2^μ ≥ 8` (hence `g³ ≠ 1`, as `3 ∤ n`), the char-p collision
`4 − 3g³ − g⁶ = 0` happens **iff `g³ = −4`** (the `1 − g³` factor is a unit). Since cubing permutes the primitive
`n`-th roots (`gcd(3,n)=1`), such a `g` exists iff `−4` is itself a primitive `n`-th root, i.e.
```
        p is W₄-bad (via this relation family)   ⟺   ord_p(−4) = n.
```
This is an **exact, decidable, p-by-p arithmetic criterion** for the char-p transfer obstruction — replacing the
opaque "char-p excess" with a multiplicative-order condition on a single element `−4`. It explains the long-observed
special role of the Fermat prime `p = 65537 = 2¹⁶ + 1` at `n = 16`: there `ord(2) = 32`, so `−4 = 2¹⁸` has order
`32/gcd(18,32) = 16 = n` — exactly the bad condition. (Exact-verified: `ord_p(−4) = n` at `p = 65537 (n=16)`,
`p = 641, 6700417 (n=32)` — the Fermat-number factors — and `≠ n` at the non-Fermat primes, which are bad via
*other* relation families. The relation norm is `Res(Φ_n, 4−3X³−X⁶) = 2·(2ⁿ+1) = 2·F_μ`, the μ-th Fermat number.)

**Significance.** This does **not** close the prize: the full `W_r` is the union over *all* weight-`2r` relation
families, each with its own such criterion, and at the prize budget `p ≈ n^4` the bad set is dense by `r > 4`
(good-prime route closed). But it gives the char-p transfer an exact, computable, arithmetic skeleton (each relation
family ⟺ an explicit order/cyclotomic condition), and pins the weight-4 face to Fermat-number arithmetic.

**What this file proves (axiom-clean).** `weight4_factor` (the ring identity), `collision_iff_cube_neg_four` (the
collision ⟺ `g³ = −4`), and `order_neg_four_of_cube` (if `g` has order `n`, `gcd(3,n)=1`, and `g³ = −4`, then
`ord(−4) = n`) — the exact-form criterion. Issue #444.
-/

namespace ProximityGap.Frontier.CharPTransferW4

/-- **The weight-4 relation polynomial factors:** `4 − 3X³ − X⁶ = (1 − X³)(4 + X³)` over any commutative ring. -/
theorem weight4_factor {R : Type*} [CommRing R] (x : R) :
    (4 : R) - 3 * x ^ 3 - x ^ 6 = (1 - x ^ 3) * (4 + x ^ 3) := by ring

/-- **The char-p collision criterion.** In a field, for `g` with `g³ ≠ 1` (e.g. any root of unity of order
`n = 2^μ ≥ 8`, since `3 ∤ n`), the weight-4 char-p collision `4 − 3g³ − g⁶ = 0` holds **iff `g³ = −4`**. The
`(1 − g³)` factor is a unit, so the whole excess is carried by the single equation `g³ = −4`. -/
theorem collision_iff_cube_neg_four {F : Type*} [Field F] (g : F) (hg : g ^ 3 ≠ 1) :
    (4 : F) - 3 * g ^ 3 - g ^ 6 = 0 ↔ g ^ 3 = -4 := by
  rw [weight4_factor g, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd (sub_eq_zero.mp h).symm hg
    · linear_combination h
  · intro h; right; rw [h]; ring

/-- **The exact order form.** If `g` has order `n` with `gcd(3,n) = 1` (true for `n = 2^μ`) and `g³ = −4`, then
`−4` has order exactly `n`. Combined with `collision_iff_cube_neg_four` (and cubing permuting the primitive `n`-th
roots), this gives the criterion `p` is W₄-bad (this relation family) `⟺ ord_p(−4) = n`. -/
theorem order_neg_four_of_cube {F : Type*} [Field F] (g : F) (n : ℕ)
    (hord : orderOf g = n) (hcop : Nat.Coprime 3 n) (h : g ^ 3 = -4) :
    orderOf (-4 : F) = n := by
  have hcg : (orderOf g).Coprime 3 := by rw [hord]; exact hcop.symm
  rw [← h, hcg.orderOf_pow, hord]

end ProximityGap.Frontier.CharPTransferW4

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharPTransferW4.weight4_factor
#print axioms ProximityGap.Frontier.CharPTransferW4.collision_iff_cube_neg_four
#print axioms ProximityGap.Frontier.CharPTransferW4.order_neg_four_of_cube
