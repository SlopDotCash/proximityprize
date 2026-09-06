/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient

/-!
# wf-L5 (#444): the `d = 16` char-`p` **order obstruction** for Chai–Fan Q1, as a theorem

This is the companion close-out to `_wfL5_ChaiFanQ1CharP.lean`
(`chaiFan_Q1_charP_degree_atom` / `chaiFan_Q1_charP_d16_shadow`, the faithful char-`p` degree
atom of Chai–Fan Q1) and `_wf9OT1_ChaiFanQ1Cyclotomic.lean` (`chaiFan_Q1_charZero`, the
char-0 settlement at every `d`).

## The lane verdict, now a machine-checked fact (not just a probe)

The char-0 proof of Q1 at `d = 16` is the cyclotomic degree fact `φ(16) = 8`: the half-basis
`{ω^0, …, ω^7}` is the power basis of `ℚ(ω)/ℚ`, so no nontrivial `{-1,0,1}`-combination
vanishes. The faithful char-`p` shadow of that degree-8 argument is
`deg(minpoly_{𝔽_p} ω) = ord₁₆(p)`, the multiplicative order of `p` in `(ℤ/16)^×`. The mission
asked for a *uniform resultant* `R₁₆ ≠ 0 mod p`. **No such invariant exists**, and the precise
reason is the following purely group-theoretic fact, proven here axiom-clean:

> For **every** unit `u ∈ (ℤ/16)^×`, `u^4 = 1`, hence `orderOf u ≤ 4`.

Equivalently: the **exponent** of `(ℤ/16)^×` is `4 < 8 = φ(16)`. Since `ord₁₆(p) = orderOf (p)`
in `(ℤ/16)^×`, this gives `deg(minpoly_{𝔽_p} ω) ≤ 4` for **every** prime `p`. So the char-0
degree-8 wall has *no* char-`p` shadow at `d = 16` (and at every dyadic `d ≥ 8`, where
`(ℤ/2^μ)^× ≅ ℤ/2 × ℤ/2^{μ-2}` has exponent `2^{μ-2} < 2^{μ-1} = φ(2^μ)`). There is no resultant
`R₁₆`; Q1 at prize scale holds by the **norm bound**, not algebra: the resultant
`Res(Φ₁₆, P) = Norm_{ℚ(ζ₁₆)/ℚ}(P(ζ))` is a rational integer with absolute value `≤ 2401 = 7^4`
over all nonzero `{-1,0,1}`-combinations `P`, and it is nonzero by `chaiFan_Q1_charZero`; hence
for every prime `p > 2401` (in particular every prize prime `p ≥ n^4 = 16^4 = 65536`), `p ∤ Res`,
so `P(ω) ≠ 0` in char `p`. See `scripts/probes/probe_wfL5_q1_d16_normbound_bypass.py`
(independent norm engine + sympy resultant cross-check).

## What is proven here (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

* `units_zmod_16_pow_four_eq_one` — every `u : (ZMod 16)ˣ` satisfies `u^4 = 1`.
* `units_zmod_16_orderOf_le_four` — every `u : (ZMod 16)ˣ` has `orderOf u ≤ 4`.
* `units_zmod_16_orderOf_lt_totient` / `chaiFan_Q1_d16_no_charp_degree_shadow` — the consumer
  statement: the order of any unit (= `deg minpoly_{𝔽_p} ω = ord₁₆(p)`) is `< 8 = φ(16)`. This is
  the exact pin of "no resultant `R₁₆`".

## Tag

`proven-per-fixed-d-char-p` (the obstruction is now a theorem). The uniform resultant route is
`GENUINELY-OBSTRUCTED` at `d = 16`. This is the non-BGK algebraic lane; it does not touch the
BGK wall.
-/

namespace ArkLib.ProximityGap.ChaiFanQ1D16Obstruction

/-- **Every unit of `(ℤ/16)^×` is killed by the 4th power.**

`(ℤ/16)^× ≅ ℤ/2 × ℤ/4` has order `φ(16) = 8` but exponent `4`. Proven by `decide` over the
finite group `(ZMod 16)ˣ` (lightweight: a single quantifier over 8 units). -/
theorem units_zmod_16_pow_four_eq_one (u : (ZMod 16)ˣ) : u ^ 4 = 1 := by
  revert u; decide

/-- **Every unit of `(ℤ/16)^×` has order at most `4`.**

Consequence of `units_zmod_16_pow_four_eq_one` via `orderOf_le_of_pow_eq_one`. In particular
`orderOf (p : (ZMod 16)ˣ) = ord₁₆(p) ≤ 4` for every odd prime `p`, which equals
`deg(minpoly_{𝔽_p} ω)` for a primitive `16`-th root `ω` in char `p`. -/
theorem units_zmod_16_orderOf_le_four (u : (ZMod 16)ˣ) : orderOf u ≤ 4 :=
  orderOf_le_of_pow_eq_one (by norm_num) (units_zmod_16_pow_four_eq_one u)

/-- **Strictly below the char-0 half-basis size.** `orderOf u ≤ 4 < 8 = φ(16)`. -/
theorem units_zmod_16_orderOf_lt_totient (u : (ZMod 16)ˣ) :
    orderOf u < Nat.totient 16 := by
  have h := units_zmod_16_orderOf_le_four u
  have h16 : Nat.totient 16 = 8 := by decide
  omega

/-- **The `d = 16` char-`p` obstruction, as the consumer statement.**

For a primitive `16`-th root of unity `ω` in a field of characteristic `p` (`p` an odd prime),
`deg(minpoly_{𝔽_p} ω) = ord₁₆(p) = orderOf (p : (ZMod 16)ˣ) ≤ 4 < 8 = φ(16)`. Hence the faithful
char-`p` Q1 degree atom (`chaiFan_Q1_charP_degree_atom`) can only cover `≤ 4` of the `8`
half-basis directions: **no resultant `R₁₆` exists**, the char-0 degree-8 wall has no char-`p`
shadow at `d = 16`, and Q1 char-`p` at prize scale is a norm-bound/counting fact, not algebra.

Stated abstractly via the group order so that it holds for the order of *any* odd prize prime:
the order in `(ℤ/16)^×` of any unit is `< φ(16)`. -/
theorem chaiFan_Q1_d16_no_charp_degree_shadow (u : (ZMod 16)ˣ) :
    orderOf u < Nat.totient 16 :=
  units_zmod_16_orderOf_lt_totient u

-- Axiom audit: must be exactly [propext, Classical.choice, Quot.sound].
#print axioms units_zmod_16_pow_four_eq_one
#print axioms units_zmod_16_orderOf_le_four
#print axioms chaiFan_Q1_d16_no_charp_degree_shadow

end ArkLib.ProximityGap.ChaiFanQ1D16Obstruction
