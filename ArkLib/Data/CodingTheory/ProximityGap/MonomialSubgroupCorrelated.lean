/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The subgroup collapse of `X^{n/2}` — correlated agreement on the half-subgroup

For a smooth Reed–Solomon code on the order-`n` multiplicative subgroup `⟨g⟩ = μ_n` with `n = 2m`,
the far-line direction `u₁ = X^m` is the source of the apparent smooth-domain proximity-gap
"counterexamples" ([BCHKS25] ePrint 2025/169, Thm 1.9). This file proves the *algebraic* fact
that the pair `(X^{m+1}, X^m)` has **correlated agreement on one fixed subset**, the
half-subgroup `μ_m`. It does **not** prove that these directions produce no MCA bad events
(see the scope warning below).

The mechanism (measured in `scripts/probes/probe_monomial_incidence_qindependence.py`, here proven):

* `monomial_half_eq_one_or_neg_one` — on every point `g^i ∈ μ_n`, the monomial `X^m` takes the
  value `(g^i)^m ∈ {+1, −1}` (a square root of `(g^i)^n = 1`). So `X^m` collapses onto `{±1}`.
* `monomial_half_eq_one_on_evenSubgroup` — on the order-`m` subgroup `⟨g²⟩ = μ_m` (the `+1`-fibre)
  the monomial `X^m` is *constant `= 1`*, hence agrees with the degree-`0` polynomial there.

Consequence: `X^m` agrees with a degree-`< k` polynomial (the constant `1`) on the `m = n/2`
points of `μ_m`, and `X^{m+1} = X·X^m` agrees with the degree-`1` polynomial `X` there. So the
*pair* `(X^{m+1}, X^m)` is **jointly** `δ`-close on the specific subset `μ_m` at `δ = 1/2`, and
every line point `X^{m+1} + γ·X^m` agrees with `X + γ` on `μ_m`.

**Scope warning (audit PG-042): this does not discard the MCA bad event.** The event
`ProximityGap.mcaEvent` (`Errors.lean`) is *local*: `γ` is bad if there is **some** witness set
`S` with `|S| ≥ (1-δ)n` on which the line agrees with a codeword **and** the pair is not jointly
agreeing on that **same** `S`. Joint agreement on one subset (`μ_m`) does not imply joint
agreement on every witness subset, so existential joint proximity does not exclude the event.
Concrete instance (arithmetic checked below in `F17Witness`): over `F₁₇`, domain
`μ₈ = {1,2,4,8,9,13,15,16}`, codewords of degree `< 2`, `δ = 1/2`, `u₀ = X⁵`, `u₁ = X⁴`,
`γ = 15 = -2`, witness `S = {1,4,13,2}`. The line `X⁵ + 15X⁴ = X⁴(X+15)` agrees with the codeword
`X + 15` on `S`, but no degree-`< 2` polynomial agrees with `u₁ = X⁴` on `S` (it would be `1` at
`1, 4, 13`, hence constant `1`, but `2⁴ = 16`). So the pair is not jointly agreeing on `S` and
`γ = 15` satisfies the local MCA-event condition despite the global joint agreement on `μ₄`.
Any claim that the MCA threshold is set only by "non-correlated" directions, or that their
incidence is `q`-independent and lands in the window interior, is a separate statement that is
**not proved here**.

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

/-! ### A local MCA witness despite global joint agreement (audit PG-042)

Arithmetic for the `F₁₇` instance in the module docstring: `S = {1,4,13,2} ⊆ μ₈`, the line
`X⁵ + 15·X⁴` agrees with the degree-`1` polynomial `X + 15` on `S`, and no affine polynomial
`a + b·X` agrees with `u₁ = X⁴` on `S`. These are the two non-trivial facts behind the claim that
`γ = 15` meets the local `mcaEvent` condition (with the degree-`< 2` RS code on `μ₈`, `δ = 1/2`);
the packaging into `ProximityGap.mcaEvent` itself is not done here. -/
namespace F17Witness

/-- The witness set lies in the order-`8` subgroup `μ₈ ⊆ F₁₇`. -/
theorem witness_subset_mu8 : ∀ x ∈ ({1, 4, 13, 2} : Finset (ZMod 17)), x ^ 8 = 1 := by
  decide

/-- The line `X⁵ + 15·X⁴` agrees with the codeword `X + 15` on the witness set. -/
theorem line_agrees_on_witness :
    ∀ x ∈ ({1, 4, 13, 2} : Finset (ZMod 17)), x ^ 5 + 15 * x ^ 4 = x + 15 := by
  decide

/-- No affine polynomial `a + b·X` agrees with `X⁴` on the witness set, so the pair
`(X⁵, X⁴)` is not jointly agreeing with degree-`< 2` codewords on that set. -/
theorem direction_not_affine_on_witness :
    ∀ a b : ZMod 17, ¬ ∀ x ∈ ({1, 4, 13, 2} : Finset (ZMod 17)), a + b * x = x ^ 4 := by
  decide

end F17Witness

end ProximityGap.MonomialSubgroupCorrelated

/-! ## Axiom audit -/
#print axioms ProximityGap.MonomialSubgroupCorrelated.monomial_half_eq_one_or_neg_one
#print axioms ProximityGap.MonomialSubgroupCorrelated.monomial_half_eq_one_on_evenSubgroup
#print axioms ProximityGap.MonomialSubgroupCorrelated.monomialSucc_eq_id_on_evenSubgroup
#print axioms ProximityGap.MonomialSubgroupCorrelated.F17Witness.line_agrees_on_witness
#print axioms ProximityGap.MonomialSubgroupCorrelated.F17Witness.direction_not_affine_on_witness
