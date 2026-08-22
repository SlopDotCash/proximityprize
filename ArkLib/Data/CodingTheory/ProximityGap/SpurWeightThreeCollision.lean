/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The weight-3 spurious char-`p` collision: `Spur_2(3) ≥ 1` (Issue #444)

The latest characterization of the prize's open core (commit `40df3426d`, KB doc
`direct-supnorm-data-beta4-2026-06-15`) pins it to an **arithmetic** (p-divisibility), not metric
(size), statement. The char-`p` energy splits as `E_r = E_r^{(0)} + Spur_r(p)`, where the spurious
excess counts antipodal-free short relations `T` (`|T| ≤ 2r`) whose cyclotomic norm is divisible by
the prize prime `p`:

    `Spur_r(p) = #{ antipodal-free T, |T| ≤ 2r : p ∣ N(σ_T) }`,   `σ_T = Σ_{i∈T} ±ζ_{2^m}^i`.

The **weight-2 base rung** (`ShortRelationNormBase.not_dvd_weight_two_norm_of_odd`, push `a823e4658`)
showed `Spur` from the *smallest* relations vanishes at every odd prize prime: `N(1 − ζ) = Φ_{2^m}(1)
= 2`, divisible only by `2`, so `Spur_1(p) = 0` for odd `p`. This left open whether the whole
divisibility tower collapses (which would *break* the wall) or whether odd primes appear at higher
weight (which *is* the wall).

## The finding: the tower does NOT collapse — odd primes appear at weight 3

This file settles that, in the smallest non-trivial case, **unconditionally and concretely**:

> **At `m = 3` (`μ_8`), the weight-3 antipodal-free relation `1 + ζ + ζ³` has `3 ∣ N(σ)`.**

Probe `probe_weight4_norm_divis.py` (exact sympy, `m = 2..5`): unlike the constant weight-2 norm `2`,
the weight-3/4 antipodal-free norms carry genuine **odd** prime factors (e.g. `N(1+ζ+ζ³) = 9 = 3²` at
`m=3`, `N(1+ζ+ζ²+ζ⁴) = 34 = 2·17` at `m=4`, `= 2·641` at `m=5`, with `641 ∣ 2³²+1` a Fermat factor),
and these grow doubly-exponentially (`~ μ(R)^{2^{m−1}}`, `μ = ` Mahler measure). So `Spur` is genuinely
nonzero at odd primes for weight `≥ 3` — the divisibility tower does NOT collapse like weight-2.

We formalize this via the **decidable** (resultant-free, norm-free) characterization: `p ∣ N(σ_T)` iff
`Φ_{2^m}` and the relation polynomial `R_T` share a root over `F̄_p`, iff they are **not coprime** in
`F_p[X]`. At `m = 3`, `p = 3`:

* `Φ_8 = X⁴ + 1 = (X²+X−1)(X²−X−1)`  factors over `F_3` (it is NOT irreducible mod 3), and
* `1 + X + X³ = (X−1)(X²+X−1)`  shares the **non-unit** factor `X²+X−1`,

so `Φ_8` and `1+X+X³` are not coprime in `F_3[X]`: there is a primitive 8-th root `g ∈ F_9` (e.g.
`g = 1+t`, `t² = −1`) with `1 + g + g³ = 0` — an antipodal-free vanishing relation among 8-th roots
that does **not** exist in characteristic `0` (`{0,1,3}` has no two indices differing by `4`, so it is
antipodal-free; over `ℂ` the sum `1+ζ+ζ³ ≠ 0`). Hence `Spur_2(3) ≥ 1`.

## Results (axiom-clean)

* `phi8_zmod3`        : `Φ_8 = X⁴ + 1` over `F_3`.
* `phi8_factor_mod3`  : `X⁴ + 1 = (X²+X−1)(X²−X−1)` over `F_3` (Φ_8 reducible mod 3).
* `rel_factor_mod3`   : `1 + X + X³ = (X−1)(X²+X−1)` over `F_3` (the relation shares the factor).
* `weight3_relation_not_coprime_mod3` : **THE WALL RUNG** — `Φ_8` and `1+X+X³` are NOT coprime in
    `F_3[X]`. Equivalently `3 ∣ N(1+ζ+ζ³)`: char-`3` energy from this weight-3 relation STRICTLY
    exceeds char-`0`, so `Spur_2(3) ≥ 1`. The divisibility tower does NOT collapse at weight `≥ 3`.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure. It is the *companion* to the weight-2 base case: where weight-2 gave `Spur = 0` at
all odd primes (norm `2`), this exhibits the FIRST odd prime at which `Spur > 0` (weight 3, `m = 3`,
`p = 3`), proving the p-divisibility tower is genuinely non-trivial above weight 2 — i.e. the wall is
real and lives exactly where the latest characterization says (the count `Spur_r(p)`, not the norm
size). It is thinness-essential in the same mild sense as the base case: `Φ_8` reducibility mod 3 is a
prime-power-`2` cyclotomic fact (`8 = 2³`, `8 ∣ 3²−1` so `F_9 ⊇ μ_8`); for the full group `n = q−1`
the analogous relation lives in the field itself and the statement is vacuous. The OPEN core is the
*count* `Spur_r(p)` at depth `r ≈ log q` (weight `≈ 2 log q`), where the norms are large and the
p-divisibility is the genuine BCHKS-1.12 wall. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- KB `direct-supnorm-data-beta4-2026-06-15`; `ShortRelationNormBase.lean` (weight-2 base, `a823e4658`).
- Probe: `scripts/probes/probe_weight4_norm_divis.py`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Polynomial

namespace ArkLib.ProximityGap.SpurWeightThree

/-- `3` is prime, so `ZMod 3 = F_3` is a field (gives `NoZeroDivisors`, `IsCoprime` machinery). -/
local instance fact3 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- **`Φ_8 = X⁴ + 1` over `F_3`.** The `2^m`-th cyclotomic polynomial is `X^{2^{m−1}} + 1`; here
`m = 3` gives `X⁴ + 1`. Holds over any commutative ring; we instantiate at `F_3`. -/
theorem phi8_zmod3 : cyclotomic (2 ^ 3) (ZMod 3) = X ^ 4 + 1 := by
  have h : (2 : ℕ) ^ 3 = 2 ^ ((3 - 1) + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- The characteristic-`3` collapse `3 = 0` in `F_3[X]`, used to clear the `−3X²` / `3X` cross-terms
in the two factorizations below. -/
theorem three_eq_zero : (3 : (ZMod 3)[X]) = 0 := by
  have h3 : (3 : (ZMod 3)) = 0 := by decide
  calc (3 : (ZMod 3)[X]) = C (3 : ZMod 3) := by norm_cast
    _ = C 0 := by rw [h3]
    _ = 0 := map_zero C

/-- **`X⁴ + 1` factors over `F_3`: `Φ_8 = (X²+X−1)(X²−X−1)`.** So `Φ_8` is REDUCIBLE mod `3` — the
prime `3` splits `μ_8` into `F_9`. (Over `ℚ`, `Φ_8` is irreducible; the reducibility mod `3` is the
arithmetic seed of the spurious collision.) -/
theorem phi8_factor_mod3 :
    (X ^ 4 + 1 : (ZMod 3)[X]) = (X ^ 2 + X - 1) * (X ^ 2 - X - 1) := by
  linear_combination (X ^ 2) * three_eq_zero

/-- **The weight-3 antipodal-free relation factors and SHARES the factor `X²+X−1`:**
`1 + X + X³ = (X−1)(X²+X−1)` over `F_3`. The exponent set `{0,1,3}` is antipodal-free (no two indices
differ by `2^{m−1}=4` mod `8`), and over `ℂ` the sum `1+ζ+ζ³ ≠ 0`; the shared factor below is what
makes it vanish in characteristic `3`. -/
theorem rel_factor_mod3 :
    (1 + X + X ^ 3 : (ZMod 3)[X]) = (X - 1) * (X ^ 2 + X - 1) := by
  linear_combination X * three_eq_zero

/-- `X²+X−1` divides `Φ_8` over `F_3`. -/
theorem common_dvd_phi8 :
    (X ^ 2 + X - 1 : (ZMod 3)[X]) ∣ cyclotomic (2 ^ 3) (ZMod 3) := by
  rw [phi8_zmod3, phi8_factor_mod3]; exact Dvd.intro _ rfl

/-- `X²+X−1` divides the weight-3 relation `1+X+X³` over `F_3`. -/
theorem common_dvd_rel :
    (X ^ 2 + X - 1 : (ZMod 3)[X]) ∣ (1 + X + X ^ 3) := by
  rw [rel_factor_mod3]; exact ⟨X - 1, by ring⟩

/-- The shared factor `X²+X−1` is a NON-unit (it has `natDegree = 2`, units have `natDegree 0`). -/
theorem nonunit_common : ¬ IsUnit (X ^ 2 + X - 1 : (ZMod 3)[X]) := by
  intro hu
  have hd : (X ^ 2 + X - 1 : (ZMod 3)[X]).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hu
  have h2 : (X ^ 2 + X - 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
  omega

/-- **THE WALL RUNG: `Φ_8` and the weight-3 antipodal-free relation `1+X+X³` are NOT coprime over
`F_3`.** Equivalently, the prize prime `p = 3` divides the cyclotomic norm `N(1 + ζ + ζ³)` (they share
the root of `X²+X−1` in `F_9`): there is a primitive `8`-th root `g ∈ F_9` with `1 + g + g³ = 0`, an
antipodal-free vanishing relation among `8`-th roots that does NOT exist in characteristic `0`.

Hence the weight-3 spurious-collision count `Spur_2(3) ≥ 1`: char-`3` energy from this relation
STRICTLY exceeds char-`0`. Contrast the weight-2 base case `ShortRelationNormBase`, where every odd
prime is coprime to `Φ_{2^m}` and `Spur = 0`. **The p-divisibility tower does NOT collapse at weight
`≥ 3` — the BCHKS-1.12 wall is genuinely arithmetic and non-trivial above the base.** -/
theorem weight3_relation_not_coprime_mod3 :
    ¬ IsCoprime (cyclotomic (2 ^ 3) (ZMod 3)) (1 + X + X ^ 3 : (ZMod 3)[X]) := by
  intro hcop
  exact nonunit_common (hcop.isUnit_of_dvd' common_dvd_phi8 common_dvd_rel)

end ArkLib.ProximityGap.SpurWeightThree

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurWeightThree.phi8_zmod3
#print axioms ArkLib.ProximityGap.SpurWeightThree.phi8_factor_mod3
#print axioms ArkLib.ProximityGap.SpurWeightThree.rel_factor_mod3
#print axioms ArkLib.ProximityGap.SpurWeightThree.weight3_relation_not_coprime_mod3
