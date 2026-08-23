/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The subgroup collapse of `X^{n/2}` — why the smooth "counterexample" directions are CORRELATED

For a smooth Reed–Solomon code on the order-`n` multiplicative subgroup `⟨g⟩ = μ_n` with `n = 2m`,
the far-line direction `u₁ = X^m` is the source of the apparent smooth-domain proximity-gap
"counterexamples" ([BCHKS25] ePrint 2025/169, Thm 1.9). This file isolates the *algebraic* reason
they are not genuine MCA violations: they are the **correlated-agreement** case the MCA bad event
excludes.

The mechanism (measured in `scripts/probes/probe_monomial_incidence_qindependence.py`, here proven):

* `monomial_half_eq_one_or_neg_one` — on every point `g^i ∈ μ_n`, the monomial `X^m` takes the
  value `(g^i)^m ∈ {+1, −1}` (a square root of `(g^i)^n = 1`). So `X^m` collapses onto `{±1}`.
* `monomial_half_eq_one_on_evenSubgroup` — on the order-`m` subgroup `⟨g²⟩ = μ_m` (the `+1`-fibre)
  the monomial `X^m` is *constant `= 1`*, hence agrees with the degree-`0` polynomial there.

Consequence (the discard): `X^m` agrees with a degree-`< k` polynomial (the constant `1`) on the
`m = n/2` points of `μ_m`, and `X^{m+1} = X·X^m` agrees with the degree-`1` polynomial `X` there.
So the *pair* `(X^m, X^{m+1})` is **jointly** `δ`-close on `μ_m` at the Johnson radius `δ = 1/2` —
correlated agreement. The whole line `X^{m+1} + γ·X^m` is then trivially close for every `γ` (it
equals `X + γ` on `μ_m`), giving the full `q−1` incidence; but this is the correlated case, *not*
an MCA bad event. The genuine MCA `δ*` is set by **non-correlated** directions (`X^a` not self-close
on `> a` points), where the incidence is `q`-independent and lands in the window interior. This is
why the subgroup directions must be discarded, not chased.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

namespace ProximityGap.MonomialSubgroupCorrelated

variable {F : Type*} [Field F] {g : F} {m : ℕ}

/-- **`X^m` collapses to `±1` on `μ_n`** (`n = 2m`). For every point `g^i` of the order-`2m`
subgroup, the monomial value `(g^i)^m` is a square root of `1`, hence `±1`. -/
theorem monomial_half_eq_one_or_neg_one (hg : orderOf g = 2 * m) (i : ℕ) :
    (g ^ i) ^ m = 1 ∨ (g ^ i) ^ m = -1 := by
  have h1 : (g ^ i) ^ (2 * m) = 1 := by
    rw [← pow_mul, mul_comm i (2 * m), pow_mul, ← hg, pow_orderOf_eq_one, one_pow]
  have hsq : (g ^ i) ^ m * (g ^ i) ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m from by ring]; exact h1
  exact mul_self_eq_one_iff.mp hsq

/-- **`X^m` is constant `= 1` on the order-`m` subgroup `⟨g²⟩`** (the `+1`-fibre). Every point
`(g²)^j` is an `m`-th-power root, so `X^m` agrees with the degree-`0` polynomial `1` there. -/
theorem monomial_half_eq_one_on_evenSubgroup (hg : orderOf g = 2 * m) (j : ℕ) :
    ((g ^ 2) ^ j) ^ m = 1 := by
  rw [← pow_mul, ← pow_mul, show 2 * (j * m) = 2 * m * j from by ring, pow_mul, ← hg,
    pow_orderOf_eq_one, one_pow]

/-- **`X^{m+1}` is the degree-`1` polynomial `X` on `⟨g²⟩`.** Together with the previous lemma this
exhibits the joint (correlated) closeness of the pair `(X^m, X^{m+1})` on the half-subgroup: both
agree with low-degree polynomials (`1` and `X`) there. -/
theorem monomialSucc_eq_id_on_evenSubgroup (hg : orderOf g = 2 * m) (j : ℕ) :
    ((g ^ 2) ^ j) ^ (m + 1) = (g ^ 2) ^ j := by
  rw [pow_succ, monomial_half_eq_one_on_evenSubgroup hg j, one_mul]

end ProximityGap.MonomialSubgroupCorrelated

/-! ## Axiom audit -/
#print axioms ProximityGap.MonomialSubgroupCorrelated.monomial_half_eq_one_or_neg_one
#print axioms ProximityGap.MonomialSubgroupCorrelated.monomial_half_eq_one_on_evenSubgroup
#print axioms ProximityGap.MonomialSubgroupCorrelated.monomialSucc_eq_id_on_evenSubgroup
