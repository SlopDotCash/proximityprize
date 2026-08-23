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
# The spurious-collision prime `p = 3` PERSISTS up the dyadic tower: bad at `m = 3` AND `m = 4` (#444)

The latest characterization of the prize's open core (KB `direct-supnorm-data-beta4-2026-06-15`)
pins it to an **arithmetic** (p-divisibility) statement: the char-`p` energy splits as
`E_r = E_r^{(0)} + Spur_r(p)`, where the spurious excess counts antipodal-free short relations `T`
(`|T| ≤ 2r`) whose cyclotomic norm is divisible by the prize prime `p`:

    `Spur_r(p) = #{ antipodal-free T, |T| ≤ 2r : p ∣ N(σ_T) }`,   `σ_T = Σ_{i∈T} ±ζ_{2^m}^i`,

decidably characterized as: `p` is a *bad prime at depth `m`* iff `Φ_{2^m}` and some short relation
polynomial `R_T` are **not coprime** in `F_p[X]` (they share a root in `F̄_p`).

## What the tower has so far — POINT witnesses at increasing `m`

* **weight 2** (`ShortRelationNormBase.not_dvd_weight_two_norm_of_odd`): `N(1−ζ) = Φ_{2^m}(1) = 2`
  — every odd prime is coprime, `Spur` from weight 2 vanishes at every `m`.
* **weight 3, `m = 3`** (`SpurWeightThree.weight3_relation_not_coprime_mod3`): `p = 3` is bad at
  `m = 3` — `Φ_8 = (X²+X−1)(X²−X−1)` over `F_3`, sharing `X²+X−1` with `1+X+X³`.
* weight-3 split (`SpurSplitPrizeRegime`, `p = 17`), weight-4 (`SpurWeightFourCollision`, `p = 17`;
  `SpurWeightFourFermat641`, the Fermat divisor `641`).

Each of those is a witness at ONE fixed `m`. The mechanism the prize argument actually needs is that
a bad prime does **not disappear** as you climb the dyadic tower `μ_8 ⊂ μ_16 ⊂ …` — the abstract
"Chebotarev persistence" assumption (referenced in `Frontier/_wf8B4`, `SpurWeightFourFermat641`).
This file supplies the **first CONCRETE same-prime tower-persistence rung**, grounding that
assumption with an actual lower step.

## The finding: the SAME prime `p = 3` is still bad one rung up, at `m = 4` (`μ_16`)

Probe `probe_spur_prime_persist.py` (exact `sympy`, decidable `gcd` over `F_p`): the prime `p = 3`,
bad at `m = 3`, remains bad at `m = 4` via the antipodal-free weight-3 relation `1 + ζ² − ζ⁴`
(exponent set `{0,2,4}`, no two indices differ by `2^{m−1} = 8`):

> over `F_3`, `Φ_16 = X⁸ + 1 = (X⁴+X²−1)(X⁴−X²−1)` is REDUCIBLE, and the relation polynomial
> `1 + X² − X⁴ = −(X⁴−X²−1)` is (up to sign) the **second factor verbatim**, so `Φ_16` and the
> relation share the degree-`4` non-unit `X⁴−X²−1`: they are NOT coprime in `F_3[X]`.

The shared root lives in `F_{3⁴} = F_81` (the order of `3` mod `16` is `4`), an antipodal-free
vanishing among `16`-th roots that does NOT exist in characteristic `0`. Hence `Spur_2(3) ≥ 1`
**at `m = 4` as well**: the bad prime `3` does not drop out of the spurious set up the tower.

## Honest scope

NOT a CORE bound, NOT a refutation. A **concrete persistence rung**: the spurious-prime set at the
prize prime `p = 3` is shown non-empty at BOTH `m = 3` and `m = 4` with explicit, decidable,
axiom-clean `F_3[X]` certificates — the first verbatim same-prime tower-persistence witness, turning
the previously *assumed* "Chebotarev persistence" of the spur into a *proven* lower step (`m = 3 → 4`).
It does NOT prove persistence for all `m` (that is the open uniform-in-`m` content), and it carries no
capacity / beyond-Johnson / cliff-at-`n/2` / `δ*→0` claim. The relation is antipodal-free and vanishes
only in characteristic `3` (over `ℂ`, `1 + ζ² − ζ⁴ ≠ 0` for a primitive `16`-th root). `CORE M(μ_n) ≤
C·√(n·log(p/n))` OPEN.

Issue #444.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Polynomial

namespace ArkLib.ProximityGap.SpurPrimePersist

/-- `3` is prime, so `ZMod 3 = F_3` is a field (gives `NoZeroDivisors`, `IsCoprime` machinery). -/
local instance fact3 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- **`Φ_16 = X⁸ + 1` over `F_3`.** The `2^m`-th cyclotomic polynomial is `X^{2^{m−1}} + 1`; here
`m = 4` gives `X⁸ + 1`. Holds over any commutative ring; we instantiate at `F_3`. -/
theorem phi16_zmod3 : cyclotomic (2 ^ 4) (ZMod 3) = X ^ 8 + 1 := by
  have h : (2 : ℕ) ^ 4 = 2 ^ ((4 - 1) + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- The characteristic-`3` collapse `3 = 0` in `F_3[X]`, used to clear the `−3X⁴` cross-term in the
factorization below. -/
theorem three_eq_zero : (3 : (ZMod 3)[X]) = 0 := by
  have h3 : (3 : (ZMod 3)) = 0 := by decide
  calc (3 : (ZMod 3)[X]) = C (3 : ZMod 3) := by norm_cast
    _ = C 0 := by rw [h3]
    _ = 0 := map_zero C

/-- **`X⁸ + 1` factors over `F_3`: `Φ_16 = (X⁴+X²−1)(X⁴−X²−1)`.** So `Φ_16` is REDUCIBLE mod `3` —
the same arithmetic seed (`Φ_{2^m}` reducible mod `3`) that made `m = 3` bad reappears at `m = 4`.
The expansion is `(X⁴−1)² − (X²)² = X⁸ − 3X⁴ + 1`, and `−3X⁴ = 0` over `F_3`. -/
theorem phi16_factor_mod3 :
    (X ^ 8 + 1 : (ZMod 3)[X]) = (X ^ 4 + X ^ 2 - 1) * (X ^ 4 - X ^ 2 - 1) := by
  linear_combination (X ^ 4) * three_eq_zero

/-- **The weight-3 antipodal-free relation IS the second factor (up to sign):**
`1 + X² − X⁴ = −(X⁴−X²−1)` over `F_3` (in fact over any ring). The exponent set `{0,2,4}` is
antipodal-free (no two indices differ by `2^{m−1}=8` mod `16`), and over `ℂ` the sum `1+ζ²−ζ⁴ ≠ 0`;
the shared factor below is what makes it vanish in characteristic `3`. -/
theorem rel_factor_mod3 :
    (1 + X ^ 2 - X ^ 4 : (ZMod 3)[X]) = (-1 : (ZMod 3)[X]) * (X ^ 4 - X ^ 2 - 1) := by
  ring

/-- `X⁴−X²−1` divides `Φ_16` over `F_3`. -/
theorem common_dvd_phi16 :
    (X ^ 4 - X ^ 2 - 1 : (ZMod 3)[X]) ∣ cyclotomic (2 ^ 4) (ZMod 3) := by
  rw [phi16_zmod3, phi16_factor_mod3]; exact Dvd.intro_left _ rfl

/-- `X⁴−X²−1` divides the weight-3 relation `1+X²−X⁴` over `F_3`. -/
theorem common_dvd_rel :
    (X ^ 4 - X ^ 2 - 1 : (ZMod 3)[X]) ∣ (1 + X ^ 2 - X ^ 4) := by
  rw [rel_factor_mod3]; exact ⟨-1, by ring⟩

/-- The shared factor `X⁴−X²−1` is a NON-unit (it has `natDegree = 4`, units have `natDegree 0`). -/
theorem nonunit_common : ¬ IsUnit (X ^ 4 - X ^ 2 - 1 : (ZMod 3)[X]) := by
  intro hu
  have hd : (X ^ 4 - X ^ 2 - 1 : (ZMod 3)[X]).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hu
  have h4 : (X ^ 4 - X ^ 2 - 1 : (ZMod 3)[X]).natDegree = 4 := by compute_degree!
  omega

/-- **THE PERSISTENCE RUNG: `Φ_16` and the weight-3 antipodal-free relation `1+X²−X⁴` are NOT coprime
over `F_3`.** Equivalently, the prize prime `p = 3` — already bad at depth `m = 3`
(`SpurWeightThree.weight3_relation_not_coprime_mod3`) — divides the cyclotomic norm `N(1 + ζ² − ζ⁴)`
at depth `m = 4` too (they share the root of `X⁴−X²−1` in `F_81`): there is a primitive `16`-th root
`g ∈ F_81` with `1 + g² − g⁴ = 0`, an antipodal-free vanishing among `16`-th roots that does NOT exist
in characteristic `0`.

Hence the weight-3 spurious-collision count `Spur_2(3) ≥ 1` at `m = 4` as well: the bad prime `3` does
**not drop out** of the spurious set as the dyadic tower climbs `μ_8 ⊂ μ_16`. This is the first
concrete same-prime persistence rung — it grounds the previously *assumed* "Chebotarev persistence" of
the spur (referenced in `Frontier/_wf8B4`) with an explicit decidable lower step. NOT a CORE closure;
the uniform-in-`m` persistence remains the open content. -/
theorem persist_weight3_relation_not_coprime_mod3 :
    ¬ IsCoprime (cyclotomic (2 ^ 4) (ZMod 3)) (1 + X ^ 2 - X ^ 4 : (ZMod 3)[X]) := by
  intro hcop
  exact nonunit_common (hcop.isUnit_of_dvd' common_dvd_phi16 common_dvd_rel)

end ArkLib.ProximityGap.SpurPrimePersist

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurPrimePersist.phi16_zmod3
#print axioms ArkLib.ProximityGap.SpurPrimePersist.phi16_factor_mod3
#print axioms ArkLib.ProximityGap.SpurPrimePersist.rel_factor_mod3
#print axioms ArkLib.ProximityGap.SpurPrimePersist.persist_weight3_relation_not_coprime_mod3
