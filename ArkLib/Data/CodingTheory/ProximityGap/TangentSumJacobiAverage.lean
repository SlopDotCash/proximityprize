/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# The subgroup tangent sum is a Jacobi-sum average (Issue #407)

This file supplies one elementary, **axiom-clean** brick in the autocorrelation reduction of the
proximity-prize Gauss-period house (`RESEARCH_SYNTHESIS_407_TANGENT.md`,
`scripts/probes/probe_autocorrelation_identity_407.py`).

For a multiplicative character `χ` of order `m` on a finite field `F` (so `ker χ = {x : χ x = 1}` is
the order-`m`-index multiplicative subgroup), define the **subgroup tangent sum** of a character `φ`:

  `T(φ) := ∑_{w ∈ ker χ} φ(1 − w)`.

This is the multiplicative incomplete subgroup sum that enters the (unformalized, probe-checked)
autocorrelation identity **I3** `A_h = m·conj(τ_h)·T_h` relating it to the Gauss-period house
`B = max_b |∑_{x∈ker χ} ψ(bx)|`.

**Correction (audit 2026-10-28, PG-108): I3 holds only for nonzero frequencies and does not give
exact house control.** An earlier version of this header stated I3 unqualified, with `|τ_h| = √q`
"perfectly flat", and concluded that `T` controls the house *exactly*. Two corrections:

* **The zero frequency is an exception.** At `h = 0`, `τ_0 = −1` is the trivial-character Gauss
  sum (not of modulus `√q`), `T_0 = n − 1`, and the actual autocorrelation is
  `A_0 = (m−1)·q + 1`, whereas the displayed right side is `−m·(n − 1)`. So I3 (and
  `|τ_h| = √q`) requires `h ≠ 0` (nontrivial character), and the diagonal `h = 0` term must be
  treated separately in any I3-based reduction.
* **Pointwise tangent bounds are not equivalent to a house bound.** Even for `h ≠ 0`, passing from
  bounds on the magnitudes `|T_h|` to a bound on `max_b |η_b|` needs Fourier inversion with phase /
  coherence accounting; "all house concentration is carried by `T`" is not a proved equivalence.

See the archived `Research/ProximityPrize/kb/archive/RESEARCH_SYNTHESIS_407_TANGENT.md` for the
research-lane findings on the I3 route. The identity **I4** proved in this file does **not** depend
on I3: it holds for arbitrary multiplicative characters `χ, φ` (including trivial ones). This brick
puts `T` on the Jacobi-sum surface; it does not by itself control the house.

## Main result (machine-verified exact in the probe; here proven axiom-clean)

* `tangentSum_mul_orderOf_eq_sum_jacobiSum` (identity **I4**):
  `(orderOf χ : ℂ) · T(φ) = ∑_{i ∈ range (orderOf χ)} jacobiSum (χ^i) φ`,
  i.e. `T(φ) = (1/m) ∑_{i=0}^{m−1} J(χ^i, φ)` — the tangent sum is the **average of `m` Jacobi sums**.

Proof: expand each `jacobiSum (χ^i) φ = ∑_x (χ^i)(x)·φ(1−x)`, exchange the order of summation, and
collapse the inner `∑_{i<m} (χ x)^i` by the geometric-sum / orthogonality dichotomy (`= m` when
`χ x = 1`, `= 0` otherwise, since `(χ x)^m = (χ^m) x = 1` as `χ^m = 1`). No Weil input, no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Mathlib `Mathlib/NumberTheory/JacobiSum/Basic.lean` (`jacobiSum`).
-/

set_option linter.style.longLine false


open Finset
open scoped Classical

namespace ArkLib.ProximityGap.TangentSumJacobiAverage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **subgroup tangent sum** of a character `φ` over `ker χ = {x : χ x = 1}`:
`T(φ) = ∑_{w ∈ ker χ} φ(1 − w)`. (`0` is automatically excluded since `χ 0 = 0 ≠ 1`.) -/
noncomputable def tangentSum (χ φ : MulChar F ℂ) : ℂ :=
  ∑ x ∈ univ.filter (fun x => χ x = 1), φ (1 - x)

/-- **Key inner identity (character orthogonality on `⟨χ⟩`).** For a unit `x`, the sum of the first
`m = orderOf χ` powers of `χ` at `x` is `m` if `x ∈ ker χ` and `0` otherwise. -/
theorem sum_pow_apply_of_isUnit (χ : MulChar F ℂ) {x : F} (hx : IsUnit x) :
    ∑ i ∈ range (orderOf χ), (χ ^ i) x = if χ x = 1 then (orderOf χ : ℂ) else 0 := by
  have hsp : (↑hx.unit : F) = x := hx.unit_spec
  have hpow : ∀ i, (χ ^ i) x = (χ x) ^ i := by
    intro i; rw [← hsp]; exact MulChar.pow_apply_coe χ i hx.unit
  simp only [hpow]
  by_cases h : χ x = 1
  · rw [if_pos h]
    simp only [h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · -- geometric sum with ratio `χ x ≠ 1`; numerator `(χ x)^m − 1 = (χ^m) x − 1 = 1 − 1 = 0`.
    rw [geom_sum_eq h]
    have hm : (χ x) ^ orderOf χ = 1 := by
      rw [← hpow (orderOf χ), pow_orderOf_eq_one, MulChar.one_apply hx]
    rw [hm, sub_self, zero_div, if_neg h]

/-- **Identity I4: the subgroup tangent sum is the average of `m` Jacobi sums.**
`(orderOf χ) · T(φ) = ∑_{i < orderOf χ} jacobiSum (χ^i) φ`. -/
theorem tangentSum_mul_orderOf_eq_sum_jacobiSum (χ φ : MulChar F ℂ) :
    (orderOf χ : ℂ) * tangentSum χ φ = ∑ i ∈ range (orderOf χ), jacobiSum (χ ^ i) φ := by
  -- expand each Jacobi sum and exchange the order of summation
  have hexp : ∑ i ∈ range (orderOf χ), jacobiSum (χ ^ i) φ
      = ∑ x : F, (φ (1 - x)) * (∑ i ∈ range (orderOf χ), (χ ^ i) x) := by
    simp only [jacobiSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexp]
  -- the `x = 0` term vanishes; for units use the orthogonality dichotomy
  have hsplit : ∀ x : F, (φ (1 - x)) * (∑ i ∈ range (orderOf χ), (χ ^ i) x)
      = if χ x = 1 then (orderOf χ : ℂ) * φ (1 - x) else 0 := by
    intro x
    by_cases hx : IsUnit x
    · rw [sum_pow_apply_of_isUnit χ hx]
      by_cases h : χ x = 1 <;> simp [h, mul_comm]
    · -- `x` not a unit (`x = 0` in a field): every `(χ^i) x = 0`, and `χ x = 0 ≠ 1`.
      have hx0 : χ x = 0 := MulChar.map_nonunit χ hx
      have hzero : ∀ i, (χ ^ i) x = 0 := by
        intro i
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi; simpa using MulChar.map_nonunit (1 : MulChar F ℂ) hx
        · rw [MulChar.pow_apply' χ hi.ne' x, hx0, zero_pow hi.ne']
      simp only [hzero, Finset.sum_const_zero, mul_zero]
      rw [if_neg (by rw [hx0]; exact zero_ne_one)]
  -- collect the surviving terms = `m · T(φ)`
  simp only [hsplit, tangentSum]
  rw [Finset.mul_sum, ← Finset.sum_filter]

end ArkLib.ProximityGap.TangentSumJacobiAverage

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.TangentSumJacobiAverage.sum_pow_apply_of_isUnit
#print axioms ArkLib.ProximityGap.TangentSumJacobiAverage.tangentSum_mul_orderOf_eq_sum_jacobiSum
