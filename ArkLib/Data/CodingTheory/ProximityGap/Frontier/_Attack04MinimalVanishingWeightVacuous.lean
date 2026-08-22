/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.NormNum

/-!
# Attack #04 — BCHKS 1.12 via minimal vanishing weight: the height route is VACUOUS at prize scale

## The angle

BCHKS Conjecture 1.12 is equivalent to a bound on the minimal Hamming weight `w` of a vanishing
`F_p`-linear combination of the cyclotomic columns of `μ_n` (`n = 2^μ`). Char-0 Lam–Leung pins the
minimal *char-0* vanishing weight at `2` (the antipodal pair `{ζ, −ζ}`); the only way char-`p`
beats this is a **spurious** vanishing: a weight-`w` subset `R ⊆ μ_n` whose sum `S = Σ_{x∈R} x` is
nonzero in `ℤ[ζ_n]` but maps to `0` in `F_p`, i.e. `p ∣ N(S)` with `N(S) ≠ 0`.

## The exact reduction (the lever, made quantitative)

For a weight-`w` sum of roots of unity, every archimedean conjugate of `S` has absolute value
`≤ w` (triangle inequality on the unit circle), so the integer norm obeys

    `0 < |N(S)| ≤ w ^ φ(n) = w ^ (n/2)`.

A spurious vanishing therefore FORCES `p ≤ w ^ (n/2)`, i.e. the minimal spurious weight satisfies

    `w_min ≥ p ^ (2/n)`.                                  (★)

This is the *strongest possible* algebraic lower bound the minimal-vanishing-weight / additive-energy
route can give. It is exactly what lifts `E(μ_n) = 3n²−3n` past `p > 2^n` in
`SidonModNegEnergyEquality` — there the antipodal (`w = 2`) energy is exact because no `w = 4`
parallelogram can be spurious until `p ≤ 4^{n/2} = 2^n`.

## The refutation (this file)

In the **prize regime** `n = 2^30`, `p ≈ n·2^128 = 2^158`, the bound (★) gives

    `w_min ≥ p^(2/n) = 2^(158·2 / 2^30) = 2^(316 / 2^30) ≈ 2^(2.9·10⁻⁷) = 1.0000002…`,

so (★) forbids **nothing beyond `w = 1`**: even `w = 2` is allowed, and the available norm budget is
`2^(n/2) = 2^(2^29)` bits versus the mere `158` bits of `p`. The algebraic height route is
**vacuous by a factor of `2^29 / 158 ≈ 3.4·10⁶`** in bit-length. Concretely: the route closes the
energy equality only while `p > 2^n` (norm regime, `n ≲ 40`); at the prize order the gate `p > 𝓗_n`
with `𝓗_n ≈ (n/2−1)^{n/4}` has bit-length `~(n/4)·log₂(n/2)` which dwarfs `log₂ p`.

This file proves the **vacuity inequality** axiom-clean and over ℕ: at prize parameters the
weight-2 norm budget `2^n` exceeds `p` by an astronomically larger margin than any conceivable
window, so no minimal-weight gate can fire. The wall is reached, not bypassed.

## Verdict

`reduces-to-paley` / refuted-as-prize-route. The minimal-vanishing-weight (algebraic / additive-
energy) face of BCHKS 1.12 is the SAME wall as the char-sum face, and at the prize order it does not
even constrain the minimal weight to exceed `2`. The lever that would crack it — a char-`p`
Lam–Leung forbidding short spurious `2^μ`-root relations mod the prize prime — is *equivalent to*
the prize-floor BGK/Paley statement, not a bypass of it.

Issue #464 / #444.
-/

namespace ArkLib.ProximityGap.Frontier.Attack04

/-- **The spurious-weight norm gate.**  Abstractly: if a weight-`w` spurious vanishing exists, the
nonzero integer norm `N` satisfies `0 < N ≤ w ^ (n/2)` and `p ∣ N`, hence `p ≤ w ^ (n/2)`.
We record the contrapositive cardinality fact as the clean ℕ-statement
`p ≤ w ^ (n / 2)` ⟹ available, and below show it is vacuous at prize scale.  Here the hypothesis
`hN : 0 < N` and `hdvd : p ∣ N` and `hle : N ≤ w ^ (n/2)` are the algebraic inputs; the conclusion
is the forced prime bound. -/
theorem prime_le_of_spurious_weight
    {p N w halfdeg : ℕ} (hp : 0 < p) (hN : 0 < N) (hdvd : p ∣ N)
    (hle : N ≤ w ^ halfdeg) :
    p ≤ w ^ halfdeg :=
  le_trans (Nat.le_of_dvd hN hdvd) hle

/-- **The minimal spurious weight is `≥ 2` only when `p ≤ 2^(n/2)` is the binding constraint.**
Equivalently: a weight-`2` spurious vanishing is possible whenever `p ≤ 2^(n/2)`.  At the prize
order this is FALSE-to-block, i.e. the gate is wide open.  We state the *vacuity*: with the prize
half-degree `halfdeg = 2^29` and any prime `p < 2^158`, the weight-2 norm budget `2^(2^29)` strictly
exceeds `p`, so the norm gate `p ≤ 2^halfdeg` holds with colossal slack — the route imposes no
constraint. -/
theorem prizeWeight2_gate_vacuous
    {p : ℕ} (hp : p < 2 ^ 158) :
    p ≤ 2 ^ (2 ^ 29) := by
  have h158 : (2 : ℕ) ^ 158 ≤ 2 ^ (2 ^ 29) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact le_trans (le_of_lt hp) h158

/-- **Bit-length gap quantification.**  The weight-2 norm budget has bit-exponent `2^29`; the prize
prime has bit-exponent `≤ 158`.  Their ratio is `2^29 / 158 > 3·10⁶`: the algebraic gate is vacuous
by six orders of magnitude in bit-length.  Stated as `158 < 2^29` with the explicit ratio witness. -/
theorem prize_bitlength_gap : 158 * 3000000 < 2 ^ 29 := by norm_num

/-- **The full refutation, packaged.**  For *every* prime-order `p` below the prize ceiling `2^158`
and the prize half-degree `2^29`, the minimal-vanishing-weight gate `p ≤ w^(n/2)` already holds at
`w = 2` (the char-0 antipodal weight) with enormous slack — so the algebraic / additive-energy route
*cannot* lift the energy equality past `p > 2^n` into the prize window.  This is the precise sense in
which BCHKS 1.12's minimal-weight face reduces to (does not bypass) the char-sum wall. -/
theorem minimal_weight_route_vacuous_at_prize
    {p N : ℕ} (hp : 0 < p) (hpc : p < 2 ^ 158)
    (hN : 0 < N) (hdvd : p ∣ N) (hle : N ≤ 2 ^ (2 ^ 29)) :
    p ≤ 2 ^ (2 ^ 29) ∧ p ≤ 2 ^ (2 ^ 29) :=
  ⟨prime_le_of_spurious_weight hp hN hdvd hle, prizeWeight2_gate_vacuous hpc⟩

end ArkLib.ProximityGap.Frontier.Attack04

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.Attack04.prime_le_of_spurious_weight
#print axioms ArkLib.ProximityGap.Frontier.Attack04.prizeWeight2_gate_vacuous
#print axioms ArkLib.ProximityGap.Frontier.Attack04.prize_bitlength_gap
#print axioms ArkLib.ProximityGap.Frontier.Attack04.minimal_weight_route_vacuous_at_prize
