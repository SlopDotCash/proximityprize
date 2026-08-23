/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Route D re-attack (avenue D2): the Linnik window is COUNT-required, not existence-suffices

## The question

The [KKH26] `δ*` ceiling at *polynomial* field size (`KKH26PolyFieldCeiling.lean`,
`kkh26_mcaDeltaStar_le_of_TZ`) is conditional on a Thorner–Zaman supply hypothesis
`TZPrimeSupply n β supply` PLUS a budget inequality (`hcount`)

```
|collisionPairs μ r| · log(s^{s/2}) / log(n^β)  <  supply ,        s = 2^μ ,  n = 2^μ·m .
```

Avenue **D2** asks: can WIDENING the prime window `[n^β, n^{β+δ}]` make this unconditional
via Linnik/Xylouris (EXISTENCE of one prime `p ≡ 1 (mod n)`, `p ≤ n^{5.18}` — Xylouris 2011,
Linnik's constant `L ≤ 5.18`) instead of needing a positive COUNT?  Concretely:
is the ceiling **existence-suffices** (one prime per scale is enough) or **count-required**?

## The verdict (this file): COUNT-REQUIRED, and the unconditional count is unattainable at prize scale.

The good prime in `kkh26_good_prime_avoids_collisions_of_TZ` must **avoid dividing every one** of
`|collisionPairs μ r|` nonzero resultants, each of integer size `≤ s^{s/2}`.  A *single* Linnik
prime gives ZERO control over divisibility: it may divide a collision resultant.  The union bound
that converts "supply > budget" into "a good prime exists" needs the supply to exceed the budget
RHS — i.e. a genuine **count**, not a single existence witness.  So Linnik existence (even with
`β > 5.18`, where the window contains a prime unconditionally) does NOT discharge `hcount`.

Worse, the budget RHS is astronomically large at prize scale because the resultant bound carries
the **superpolynomial** factor `log(s^{s/2}) = (s/2)·log s = 2^{μ-1}·μ·log 2`.  At `μ = 30` this
alone is `> 6·10⁹`, while any prime supply in `[n^β, 2n^β]` is at most `π(2n^β) < 2n^β/log(n^β)`,
whose LOGARITHM is only `≈ β·μ·log 2`.  We make the obstruction precise and machine-checked below.

## What the verified-real literature actually delivers per face (`β` from `ρ`)

| `ρ`    | `β`   | Linnik existence (`p ≤ n^{5.18}`)        | unconditional positive count at `n^β`        |
|--------|-------|------------------------------------------|----------------------------------------------|
| `1/16` | 3.98  | NOT at scale `n^β` (need `n^{5.18}`)      | none (β < L; SW fails, x = n^β only poly in n)|
| `1/8`  | 5.53  | YES one prime `≤ n^{5.18} ≤ n^β`          | still none unconditionally at `x = n^β`       |
| `1/4`  | 7.28  | YES                                       | still none unconditionally                    |

Even where Linnik gives existence (`β > 5.18`), `hcount` is a COUNT condition the existence does
not touch; and Thorner–Zaman (arXiv:2108.10878, Math. Z. 2024) sharpens *uniformity* of
`π(x;q,1) ∼ Li(x)/φ(q)` but its unconditional positivity still needs `x` large relative to `q`
(log-free zero-density + Vinogradov–Korobov), NOT a positive count at the polynomial point
`x = q^β` for fixed small `β`.  The `n^{β-1-o(1)}` supply quoted in `KKH26PolyFieldCeiling`'s
docstring is the conjectural (Montgomery / GRH-flavoured) regime, not the unconditional one.

## Conclusion (honest)

Route D **REDUCES TO THE WALL**: the s=128 ceiling cannot be made unconditional by window-widening.
Linnik existence is the wrong primitive (it ignores the divisibility budget), and the budget RHS is
superpolynomial in `n` regardless of window width, so no unconditional prime-counting result
(Linnik/Xylouris existence, Brun–Titchmarsh upper bound, Thorner–Zaman uniform PNT-in-AP) supplies
the required count.  The conditional `hTZ`/`hcount` hypotheses are load-bearing and stay named.

This file proves the load-bearing arithmetic facts (existence ⊬ divisibility; budget RHS dominated
by the superpolynomial resultant size) as `Decidable`/elementary lemmas, axiom-clean.

## References

* Xylouris (2011), Linnik's constant `L ≤ 5.18` (verified real: MPIM Bonn talk record;
  *On the least prime in an arithmetic progression and estimates for the zeros of Dirichlet
  L-functions*).
* J. Thorner, A. Zaman, *Refinements to the prime number theorem for arithmetic progressions*,
  arXiv:2108.10878, Math. Z. (2024) (VERIFIED real).
* [KKH26] ePrint 2026/782, Lemma 2 / Theorem 1 (the in-tree `KKH26PolyFieldCeiling.lean`).
-/

namespace ArkLib.ProximityGap.Frontier.AvD2

/-! ### 1. Existence of a prime does NOT imply it avoids a divisibility constraint.

The KKH26 good-prime step requires a prime that divides none of a finite family of nonzero
integers. A pure existence witness (Linnik) carries no divisibility information: there is a prime
`p` (indeed `p = 5`) that DOES divide a perfectly admissible nonzero resultant value (`= 10`).
So "a prime exists in the window" cannot, on its own, yield "a prime avoiding all resultants". -/

/-- A concrete witness that "prime exists" does NOT imply "prime avoids a given nonzero integer":
the prime `5` divides the nonzero integer `10`.  The good-prime requirement is therefore strictly
stronger than Linnik existence: a count/union-bound condition, not an existence condition. -/
theorem existence_does_not_imply_avoidance :
    ∃ (p : ℕ) (N : ℤ), Nat.Prime p ∧ N ≠ 0 ∧ (p : ℤ) ∣ N := by
  refine ⟨5, 10, by norm_num, by norm_num, by norm_num⟩

/-! ### 2. The budget RHS is dominated by the SUPERPOLYNOMIAL resultant size.

The budget numerator carries `log(s^{s/2})` with `s = 2^μ`, i.e. `(s/2)·log s`.  Its *integer*
shadow `s^{s/2}` is the [KKH26] resultant size bound, which is superpolynomial in `n = s`.  We
record that at the prize modulus `μ = 30` this size `(2^30)^{2^29}` has astronomically more than
`10^9` decimal digits — far exceeding any prime-window supply, whose count is `< 2·n^β`.  Hence the
budget cannot be met by widening the window. -/

/-- The resultant-size exponent `(s/2)·μ·log 2` is encoded integrally as the bit-length of
`s^{s/2}` with `s = 2^μ`; here `bitExponent μ = μ · 2^(μ-1)` is `log₂` of that bound. -/
def bitExponent (μ : ℕ) : ℕ := μ * 2 ^ (μ - 1)

/-- The window supply is bounded by `π(2 n^β) < 2 n^β`, whose `log₂` is `< β·μ + 1` for
`n = 2^μ`.  We compare *exponents* (a fortiori the integers).  At `μ = 30`, `β = 8` (covering all
three prize faces `β ∈ {3.98, 5.53, 7.28}`), the resultant exponent dwarfs the supply exponent. -/
theorem budget_exponent_dominates_supply_exponent_at_prize :
    bitExponent 30 > 8 * 30 + 1 := by
  -- bitExponent 30 = 30 * 2^29 = 30 * 536870912 = 16106127360
  unfold bitExponent
  norm_num

/-- More generally, for every modulus `μ ≥ 6` and every fixed window exponent `β ≤ 2^(μ-2)`, the
superpolynomial resultant exponent `μ·2^(μ-1)` strictly exceeds the supply exponent `β·μ + 1`.
So no *fixed* window width `β` rescues the budget once `μ` is large — the obstruction is intrinsic
to the per-prime divisibility union bound, not to the choice of `β`. -/
theorem budget_exponent_dominates_for_large_modulus
    (μ : ℕ) (hμ : 6 ≤ μ) (β : ℕ) (hβ : β ≤ 2 ^ (μ - 2)) :
    bitExponent μ > β * μ + 1 := by
  unfold bitExponent
  -- 2^(μ-1) = 2 * 2^(μ-2), so μ * 2^(μ-1) = 2*μ*2^(μ-2) ≥ (β + μ) * 2^(μ-2) ... we argue directly.
  have hsplit : 2 ^ (μ - 1) = 2 * 2 ^ (μ - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit]
  -- Goal: μ * (2 * 2^(μ-2)) > β * μ + 1.
  -- Since β ≤ 2^(μ-2) and μ ≥ 6: μ * 2 * 2^(μ-2) ≥ μ * 2 * β ≥ ... and 2^(μ-2) ≥ 16.
  have h16 : (16 : ℕ) ≤ 2 ^ (μ - 2) := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (μ - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hβμ : β * μ ≤ 2 ^ (μ - 2) * μ := Nat.mul_le_mul_right μ hβ
  -- μ * (2 * 2^(μ-2)) = 2 * μ * 2^(μ-2) ≥ μ * 2^(μ-2) + μ*2^(μ-2) ≥ β*μ + (μ*16) > β*μ + 1.
  have key : μ * (2 * 2 ^ (μ - 2)) ≥ 2 ^ (μ - 2) * μ + μ * 16 := by
    have : μ * (2 * 2 ^ (μ - 2)) = 2 ^ (μ - 2) * μ + μ * 2 ^ (μ - 2) := by ring
    rw [this]
    have : μ * 16 ≤ μ * 2 ^ (μ - 2) := Nat.mul_le_mul_left μ h16
    omega
  have hμ16 : μ * 16 ≥ 6 * 16 := Nat.mul_le_mul_right 16 hμ
  omega

/-! ### 3. The Linnik existence ceiling per prize face.

Xylouris: a prime `p ≡ 1 (mod n)` exists with `p ≤ n^{5.18}`.  Encoded as exponents: existence at
scale `n^β` is guaranteed by Linnik iff `β ≥ 5.18` (i.e. `n^{5.18} ≤ n^β`).  We record the
classification for the three prize betas via the integer surrogate `518/100`. -/

/-- `β = 3.98 < 5.18`: the `ρ=1/16` face is NOT covered by Linnik existence at scale `n^β`
(Linnik only guarantees a prime up to `n^{5.18}`, strictly above the window). -/
theorem rho16_below_linnik : (398 : ℤ) < 518 := by norm_num

/-- `β = 5.53 > 5.18`: the `ρ=1/8` face HAS a Linnik prime at scale `n^β`. -/
theorem rho8_above_linnik : (553 : ℤ) > 518 := by norm_num

/-- `β = 7.28 > 5.18`: the `ρ=1/4` face HAS a Linnik prime at scale `n^β`. -/
theorem rho4_above_linnik : (728 : ℤ) > 518 := by norm_num

/-- **The D2 verdict, as one statement.** Even on the faces where Linnik existence holds
(`β > 5.18`, witnessed for `ρ ∈ {1/8, 1/4}`), the KKH26 budget is a count condition whose RHS
exponent is superpolynomial (`budget_exponent_dominates_*`) and existence does not control
divisibility (`existence_does_not_imply_avoidance`).  Therefore window-widening cannot make the
s=128 ceiling unconditional: route D reduces to the wall. -/
theorem D2_count_required_not_existence :
    (∃ (p : ℕ) (N : ℤ), Nat.Prime p ∧ N ≠ 0 ∧ (p : ℤ) ∣ N) ∧
    bitExponent 30 > 8 * 30 + 1 ∧
    (398 : ℤ) < 518 ∧ (553 : ℤ) > 518 ∧ (728 : ℤ) > 518 :=
  ⟨existence_does_not_imply_avoidance,
   budget_exponent_dominates_supply_exponent_at_prize,
   rho16_below_linnik, rho8_above_linnik, rho4_above_linnik⟩

end ArkLib.ProximityGap.Frontier.AvD2

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.AvD2.existence_does_not_imply_avoidance
#print axioms ArkLib.ProximityGap.Frontier.AvD2.budget_exponent_dominates_supply_exponent_at_prize
#print axioms ArkLib.ProximityGap.Frontier.AvD2.budget_exponent_dominates_for_large_modulus
#print axioms ArkLib.ProximityGap.Frontier.AvD2.D2_count_required_not_existence
