/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The weight-4 spurious char-`p` collision: `Spur_2(17) ≥ 1` at `m = 4` (Issue #444)

This file is the **weight-4 companion** to `SpurWeightThreeCollision` (`Spur_2(3) ≥ 1` at `m = 3`),
extending the spurious-collision divisibility tower one rung higher with the cleanest possible
witness: a primitive `16`-th root of unity lying in the **base field** `F_17` itself.

## Background: the Spur tower (the arithmetic prize core)

The latest characterization of the prize's open core (KB `direct-supnorm-data-beta4-2026-06-15`)
pins it to an **arithmetic** (p-divisibility) statement: the char-`p` energy splits as
`E_r = E_r^{(0)} + Spur_r(p)`, where the spurious excess counts antipodal-free short relations `T`
(`|T| ≤ 2r`) whose cyclotomic norm is divisible by the prize prime `p`:

    `Spur_r(p) = #{ antipodal-free T, |T| ≤ 2r : p ∣ N(σ_T) }`,   `σ_T = Σ_{i∈T} ζ_{2^m}^i`.

The tower so far:
* **weight 2** (`ShortRelationNormBase.not_dvd_weight_two_norm_of_odd`): `N(1−ζ) = Φ_{2^m}(1) = 2`,
  divisible only by `2`, so `Spur_1(p) = 0` at every odd prize prime — the base rung collapses.
* **weight 3** (`SpurWeightThree.weight3_relation_not_coprime_mod3`): `3 ∣ N(1+ζ+ζ³)` at `m = 3`,
  via the shared **degree-2** factor `X²+X−1` of `Φ_8` and `1+X+X³` over `F_3` (the root lives in
  `F_9`, a quadratic extension) — the tower does NOT collapse at weight `≥ 3`.

## The finding: weight 4 has a BASE-FIELD collision at `p = 17`, `m = 4` (`μ_16`)

Probe `probe_spur_weight4_collision.py` / `probe_spur_w4_verify17.py` (exact `sympy`, decidable
`gcd` over `F_p`): the antipodal-free weight-4 relation `1 + ζ + ζ² + ζ⁴` (exponent set `{0,1,2,4}`,
no two indices differ by `2^{m−1}=8`) collides at the **smallest** prime `p = 17`, and uniquely
among the eight relations of this rotation class the shared factor is **degree 1**:

> over `F_17`, `g = 12` is a primitive `16`-th root of unity (`g^8 = −1`, order `16`), and
> `1 + g + g² + g⁴ = 0` — an antipodal-free vanishing relation among `16`-th roots that does
> **not** exist over `ℂ` (`|1 + ζ + ζ² + ζ⁴| ≈ 3.36 ≠ 0`).

So `(X − 12)` divides BOTH `Φ_16 = X⁸ + 1` and `1 + X + X² + X⁴` over `F_17`, hence they are not
coprime, hence `17 ∣ N(1 + ζ + ζ² + ζ⁴)`, hence `Spur_2(17) ≥ 1`. Because the root is in the base
field (degree-1 factor), the witness is fully decidable arithmetic in `ZMod 17` — no field
extension construction is needed (sharper than the weight-3 `F_9` witness).

## Results (axiom-clean)

* `phi16_zmod17`               : `Φ_16 = X⁸ + 1` over `F_17`.
* `g_isRoot_phi16`             : `12` is a root of `Φ_16` over `F_17` (a primitive 16th root, in base field).
* `g_isRoot_rel`              : `12` is a root of the weight-4 relation `1 + X + X² + X⁴` over `F_17`.
* `linfac_dvd_phi16` / `linfac_dvd_rel` : `(X − 12)` divides each (deg-1 `dvd_iff_isRoot`).
* `weight4_relation_not_coprime_mod17` : **THE WALL RUNG (weight 4)** — `Φ_16` and `1+X+X²+X⁴` are
    NOT coprime over `F_17`, i.e. `17 ∣ N(1+ζ+ζ²+ζ⁴)`, i.e. `Spur_2(17) ≥ 1`.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure. It is the weight-4 companion to the weight-2 base and weight-3 rung: it extends
the p-divisibility tower to weight 4 with the cleanest (base-field, degree-1) witness, confirming
the spurious-collision count `Spur_r(p)` is genuinely nonzero at weight 4 (a new odd prime, `17`,
appears). Thinness-essential in the same mild sense as the lower rungs: `Φ_16` having a root in
`F_17` is the prime-power-`2` cyclotomic fact `16 ∣ 17 − 1` (so `μ_16 ⊆ F_17^*`); for the full group
`n = q − 1` the relation lives in the field itself and the statement is vacuous. The OPEN core is the
*count* `Spur_r(p)` at depth `r ≈ log q` (weight `≈ 2 log q`), the genuine BCHKS-1.12 wall. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- KB `direct-supnorm-data-beta4-2026-06-15`; `SpurWeightThreeCollision.lean` (weight-3 rung);
  `ShortRelationNormBase.lean` (weight-2 base).
- Probes: `scripts/probes/probe_spur_weight4_collision.py`, `probe_spur_w4_verify17.py`,
  `probe_spur_w4_cofactors.py`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Polynomial

namespace ArkLib.ProximityGap.SpurWeightFour

/-- `17` is prime, so `ZMod 17 = F_17` is a field. -/
local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- **`Φ_16 = X⁸ + 1` over `F_17`.** The `2^m`-th cyclotomic polynomial is `X^{2^{m−1}} + 1`; here
`m = 4` gives `X⁸ + 1`. Holds over any commutative ring; we instantiate at `F_17`. -/
theorem phi16_zmod17 : cyclotomic (2 ^ 4) (ZMod 17) = X ^ 8 + 1 := by
  have h : (2 : ℕ) ^ 4 = 2 ^ ((4 - 1) + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- **`12` is a primitive `16`-th root of unity in the base field `F_17`.** It is a root of
`Φ_16 = X⁸ + 1` (`12⁸ = −1` over `F_17`). Decidable arithmetic in `ZMod 17`. -/
theorem g_isRoot_phi16 :
    (X ^ 8 + 1 : (ZMod 17)[X]).IsRoot (12 : ZMod 17) := by
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  decide

/-- **`12` is a root of the weight-4 antipodal-free relation `1 + X + X² + X⁴` over `F_17`.** The
exponent set `{0,1,2,4}` is antipodal-free (no two indices differ by `2^{m−1} = 8`), and over `ℂ`
the sum `1 + ζ + ζ² + ζ⁴ ≠ 0`; this root in `F_17` is the char-`17`-only collision. -/
theorem g_isRoot_rel :
    (1 + X + X ^ 2 + X ^ 4 : (ZMod 17)[X]).IsRoot (12 : ZMod 17) := by
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  decide

/-- `(X − 12)` divides `Φ_16` over `F_17` (degree-1 factor ↔ base-field root). -/
theorem linfac_dvd_phi16 :
    (X - C (12 : ZMod 17)) ∣ cyclotomic (2 ^ 4) (ZMod 17) := by
  rw [phi16_zmod17, dvd_iff_isRoot]; exact g_isRoot_phi16

/-- `(X − 12)` divides the weight-4 relation `1 + X + X² + X⁴` over `F_17`. -/
theorem linfac_dvd_rel :
    (X - C (12 : ZMod 17)) ∣ (1 + X + X ^ 2 + X ^ 4 : (ZMod 17)[X]) := by
  rw [dvd_iff_isRoot]; exact g_isRoot_rel

/-- The shared factor `X − 12` is a NON-unit (it has `natDegree = 1`; units have `natDegree 0`). -/
theorem nonunit_linfac : ¬ IsUnit (X - C (12 : ZMod 17)) := by
  intro hu
  have hd : (X - C (12 : ZMod 17)).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hu
  have h1 : (X - C (12 : ZMod 17)).natDegree = 1 := natDegree_X_sub_C _
  omega

/-- **THE WALL RUNG (weight 4): `Φ_16` and the weight-4 antipodal-free relation `1+X+X²+X⁴` are NOT
coprime over `F_17`.** Equivalently, the prize prime `p = 17` divides the cyclotomic norm
`N(1 + ζ + ζ² + ζ⁴)` (they share the base-field root `12`, a primitive `16`-th root of unity in
`F_17`): there is `g = 12 ∈ F_17` with `g` of order `16` and `1 + g + g² + g⁴ = 0`, an antipodal-free
vanishing relation among `16`-th roots that does NOT exist in characteristic `0`.

Hence the weight-4 spurious-collision count `Spur_2(17) ≥ 1`: char-`17` energy from this relation
STRICTLY exceeds char-`0`. This extends the divisibility tower past the weight-3 rung
(`SpurWeightThree`, `3 ∣ N(1+ζ+ζ³)` at `m = 3` via an `F_9` root) with a cleaner base-field witness,
reconfirming the BCHKS-1.12 wall is genuinely arithmetic and grows with the relation weight. -/
theorem weight4_relation_not_coprime_mod17 :
    ¬ IsCoprime (cyclotomic (2 ^ 4) (ZMod 17)) (1 + X + X ^ 2 + X ^ 4 : (ZMod 17)[X]) := by
  intro hcop
  exact nonunit_linfac (hcop.isUnit_of_dvd' linfac_dvd_phi16 linfac_dvd_rel)

end ArkLib.ProximityGap.SpurWeightFour

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurWeightFour.phi16_zmod17
#print axioms ArkLib.ProximityGap.SpurWeightFour.g_isRoot_phi16
#print axioms ArkLib.ProximityGap.SpurWeightFour.g_isRoot_rel
#print axioms ArkLib.ProximityGap.SpurWeightFour.weight4_relation_not_coprime_mod17
