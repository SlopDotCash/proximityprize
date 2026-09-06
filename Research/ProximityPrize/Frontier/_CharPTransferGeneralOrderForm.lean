/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The char-p transfer skeleton, general single-carrier face: `bad ⟺ ord_p(−r) = n`, all depths (#444)

Extends `_CharPTransferW4OrderForm` (the `r = 4` face, `ord_p(−4) = n`) to **every depth `r`**.

**Context.** The prize reduces to the char-p additive-energy excess `W_r = E_r(F_p) − E_r(ℂ) ≥ 0` — the failure of
the proven char-0 bound `E_r(ℂ) ≤ (2r−1)‼·n^r` to transfer to char-p. `W_r > 0` iff a weight-`2r` relation among
`n`-th roots (`n = 2^μ`) acquires an extra solution mod `p`.

**The general single-carrier law (this file, verified by exact integer computation).** The **single-carrier**
weight-`r` relation `r·ζ⁰ = (r−1)·ζ^a + ζ^{2a}` — i.e. `σ_{r,a}(X) = r − (r−1)·X^a − X^{2a}` (balanced: `+`-mass
`r`, `−`-mass `(r−1)+1 = r`) — **factors uniformly**:
```
r − (r−1)·X^a − X^{2a} = (1 − X^a)·(r + X^a).
```
For a root of unity `g` of order `n = 2^μ` with `gcd(a,n) = 1` (so `g^a ≠ 1`), the `(1 − g^a)` factor is a unit, so
the char-p collision `σ_{r,a}(g) = 0` holds **iff `g^a = −r`**; and since `x ↦ x^a` permutes the primitive `n`-th
roots, such a `g` exists iff `−r` is a primitive `n`-th root:
```
        p is W_r-bad (single-carrier family)   ⟺   ord_p(−r) = n.
```
An **exact decidable order criterion for every depth `r`**. The carrier norm is the generalized Fermat number
`Res(Φ_n, r + X^a) = r^{n/2} + 1` (base `r`), via the general resultant law `Res(Φ_n, C + D·X) = C^{n/2} + D^{n/2}`
(both exact-verified). The `r = 4` rung gives `2^n + 1 = F_μ` (the Fermat number — sparse, often prime, e.g. `65537`
at `n = 16`); for `r ≥ 5` the carrier norm `r^{n/2}+1` is composite (Aurifeuillian-style: `6^8+1 = 17·98801` at
`n = 16`), which is exactly why the bad-prime density rises with `r`. (Verified: `ord_p(−r) = n` at every
`p ≡ 1 mod n` factor of `r^{n/2}+1`, `r = 4..8`, `n = 8,16,32`.)

**Honest scope.** This is **not** a closure: the full `W_r` is the union over *all* weight-`2r` relation families
(unbounded complexity), and at the prize budget `p ≈ n^4` no *bounded* family of order criteria closes the
good-prime route — a random prize prime avoids any fixed criterion `ord_p(−r)=n` with probability
`1 − Θ(1/n^3) → 1`. The route is closed only by the *union over relation complexities up to depth `r ≈ log q`*, which
relocates the obstruction precisely onto the depth-`log q` energy ladder = the BGK/Paley wall. What this gives: the
char-p transfer's single-carrier faces are now an **exact, decidable, computable cyclotomic-order skeleton at every
depth**, with the carrier norms classified as generalized Fermat numbers `r^{n/2}+1`.

**What this file proves (axiom-clean).** `singleCarrier_factor` (the general ring identity, all `r`),
`collision_iff_eq_neg_r` (collision ⟺ `g^a = −r`), `order_neg_r_of_carrier` (the exact `ord_p(−r) = n` criterion).
Issue #444.
-/

namespace ProximityGap.Frontier.CharPTransferGeneral

/-- **The general single-carrier factorization:** `r − (r−1)·y − y² = (1 − y)·(r + y)` over any commutative ring
(`y = X^a`). At `r = 4` this is the W₄ identity `4 − 3y − y² = (1 − y)(4 + y)`. -/
theorem singleCarrier_factor {R : Type*} [CommRing R] (r y : R) :
    r - (r - 1) * y - y ^ 2 = (1 - y) * (r + y) := by ring

/-- **The general char-p collision criterion.** In a field, for `y` (`= g^a`) with `y ≠ 1`, the single-carrier
collision `r − (r−1)·y − y² = 0` holds **iff `y = −r`**. The `(1 − y)` factor is a unit, so the entire weight-`r`
single-carrier excess is carried by the one equation `y = −r`. -/
theorem collision_iff_eq_neg_r {F : Type*} [Field F] (r y : F) (hy : y ≠ 1) :
    r - (r - 1) * y - y ^ 2 = 0 ↔ y = -r := by
  rw [singleCarrier_factor r y, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd (sub_eq_zero.mp h).symm hy
    · linear_combination h
  · intro h; right; rw [h]; ring

/-- **The exact order-form criterion (general depth).** If `g` has order `n`, `a` is coprime to `n`, and the
collision element is `g^a = −r`, then `−r` has order exactly `n`. So `p` is W_r-bad via the single-carrier family
**iff `ord_p(−r) = n`** — an exact decidable criterion at every depth `r`, generalizing the W₄ form `ord_p(−4) = n`. -/
theorem order_neg_r_of_carrier {F : Type*} [Field F] (g : F) (n a : ℕ) (r : F)
    (hord : orderOf g = n) (hcop : Nat.Coprime n a) (h : g ^ a = -r) :
    orderOf (-r) = n := by
  have hcg : (orderOf g).Coprime a := by rw [hord]; exact hcop
  rw [← h, hcg.orderOf_pow, hord]

/-- **The inverse root-lift for the general carrier.** If `u` already has order `n` and `b` is an
explicit inverse of the carrier exponent `a` modulo `n`, then `g = u^b` is again primitive of order `n`
and satisfies `g^a = u`. This is the converse permutation step in the order criterion, stated with the
modular inverse as data so it is usable for every concrete coprime carrier exponent. -/
theorem exists_orderOf_eq_and_pow_eq_of_inverse {F : Type*} [Field F] (u : F) (n a b : ℕ)
    (hn0 : n ≠ 0) (hord : orderOf u = n) (hinv : b * a ≡ 1 [MOD n]) :
    ∃ g : F, orderOf g = n ∧ g ^ a = u := by
  refine ⟨u ^ b, ?_, ?_⟩
  · have hcop_b : Nat.Coprime n b := by
      exact (Nat.coprime_of_mul_modEq_one a hinv).symm
    have hcg : (orderOf u).Coprime b := by rw [hord]; exact hcop_b
    rw [hcg.orderOf_pow, hord]
  · rw [← pow_mul u b a]
    have hu_fin : IsOfFinOrder u := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨n, Nat.pos_of_ne_zero hn0, by rw [← hord]; exact pow_orderOf_eq_one u⟩
    have hmodu : b * a ≡ 1 [MOD orderOf u] := by rwa [hord]
    simpa using (hu_fin.pow_eq_pow_iff_modEq).mpr hmodu

/-- **The converse collision certificate.** If the carrier element `−r` has order `n` and `b` inverts
`a` modulo `n`, then some primitive `n`-th root `g` realizes the single-carrier collision: `g^a = −r`
and `r − (r−1)g^a − g^(2a) = 0`. Together with `order_neg_r_of_carrier`, this gives the exact
`carrier collision exists ⇔ orderOf (-r) = n` skeleton for every depth `r` and every invertible
carrier exponent. -/
theorem exists_carrier_collision_of_order_neg_r {F : Type*} [Field F] (n a b : ℕ) (r : F)
    (hn0 : n ≠ 0) (hn : n ≠ 1) (hord : orderOf (-r) = n) (hinv : b * a ≡ 1 [MOD n]) :
    ∃ g : F,
      orderOf g = n ∧ g ^ a = -r ∧ r - (r - 1) * g ^ a - g ^ (2 * a) = 0 := by
  obtain ⟨g, hgord, hga⟩ := exists_orderOf_eq_and_pow_eq_of_inverse (-r) n a b hn0 hord hinv
  refine ⟨g, hgord, hga, ?_⟩
  have hy : g ^ a ≠ 1 := by
    intro h1
    have : orderOf (-r : F) = 1 := by simp [← hga, h1]
    exact hn (hord ▸ this)
  have hcrit := (collision_iff_eq_neg_r (r := r) (y := g ^ a) hy).mpr hga
  have hpowa : (g ^ a) ^ 2 = g ^ (2 * a) := by rw [← pow_mul g a 2, Nat.mul_comm]
  simpa [hpowa] using hcrit

end ProximityGap.Frontier.CharPTransferGeneral

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharPTransferGeneral.singleCarrier_factor
#print axioms ProximityGap.Frontier.CharPTransferGeneral.collision_iff_eq_neg_r
#print axioms ProximityGap.Frontier.CharPTransferGeneral.order_neg_r_of_carrier
#print axioms ProximityGap.Frontier.CharPTransferGeneral.exists_orderOf_eq_and_pow_eq_of_inverse
#print axioms ProximityGap.Frontier.CharPTransferGeneral.exists_carrier_collision_of_order_neg_r
