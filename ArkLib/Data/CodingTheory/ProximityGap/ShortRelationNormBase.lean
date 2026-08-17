/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# The weight-2 short-relation norm base case of the char-`p` p-divisibility tower (Issue #444)

The latest characterization of the prize's open core (commit `40df3426d`, KB doc
`direct-supnorm-data-beta4-2026-06-15.md`) pins it to an **arithmetic** (divisibility), not metric
(size), statement. The char-`p` energy splits as `E_r = E_r^{(0)} + Spur_r(p)`, where the spurious
excess is the count of antipodal-free short relations `T` (`|T| ≤ 2r`) whose cyclotomic norm is
divisible by the prize prime:

    `Spur_r(p) = #{ antipodal-free T, |T| ≤ 2r : p ∣ N(σ_T) }`,   `σ_T = Σ_{i∈T} ±ζ_{2^m}^i`.

Improving the norm SIZE ceiling (`(2r)^{n/2} → (2r)^{n/4} → …`, lane wf-M1 `mahler_norm_bound`) bounds
the WRONG object — the real quantity is the p-DIVISIBILITY count. This file proves the **absolute base
case** of that count tower, fully UNCONDITIONALLY (no divisibility hypothesis to discharge — it is
discharged here from Mathlib's exact cyclotomic evaluation).

## The base case

The simplest antipodal-free relation has weight 2: a single difference `σ = ζ^a − ζ^b` with
`a − b` odd (so `ζ^{a−b}` is again a primitive `2^m`-th root, hence `σ` is non-antipodal and `≠ 0`).
Up to the unit `ζ^b` this is `1 − ζ^{a−b}`, whose norm is the value of the minimal polynomial at `1`:

    `N(1 − ζ_{2^m}) = Φ_{2^m}(1)`.

Since `Φ_{2^m}(x) = x^{2^{m−1}} + 1` (the `p = 2`, `k = m − 1` prime-power cyclotomic),
`Φ_{2^m}(1) = 2` for every `m ≥ 1`. This is the **smallest** nonzero short-relation norm (constant
`2`, NOT the size-ceiling `(2)^{n/4}`), and crucially it is divisible only by the prime `2`:

> **For every ODD prime `p`, `p ∤ Φ_{2^m}(1) = 2`** — so the weight-2 spurious count `Spur` at any odd
> prize prime is `0`: char-`p` energy from weight-2 relations EXACTLY equals char-`0`.

This is the genuinely UNCONDITIONAL bottom rung of the BCHKS-1.12 p-divisibility tower (the size route
cannot even state it, since it bounds norm magnitude, not divisibility). It is thinness-essential in the
mild sense that it is the `p = 2` prime-power cyclotomic value `Φ_{2^m}(1) = 2`; for non-prime-power `n`
the value `Φ_n(1) = 1` (Mathlib `eval_one_cyclotomic_not_prime_pow`), a different arithmetic.

## Results (axiom-clean)

* `eval_one_cyclotomic_two_pow`     : `Φ_{2^m}(1) = 2` over `ℤ` (`m ≥ 1`), from `eval_one_cyclotomic_prime_pow`.
* `not_dvd_weight_two_norm_of_odd`  : an odd prime `p` does NOT divide `Φ_{2^m}(1)` — the weight-2
    spurious-collision count vanishes at every odd prize prime (the unconditional base rung).
* `weight_two_norm_eq_two`          : the (ℤ-)norm form `(Φ_{2^m}(1) : ℤ) = 2`.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure and NOT a new analytic input — it is an EXACT arithmetic identity from Mathlib's
cyclotomic library, packaged as the weight-2 base rung of the p-divisibility count that the latest
prize characterization identifies as the RIGHT object. It discharges the depth-1 divisibility
hypothesis of `HaloFreeDivisibility.sum_pow_eq_zero_iff_antipodalClosed_of_not_dvd` for the smallest
weight unconditionally. The OPEN core is the count `Spur_r(p)` at depth `r ≈ log q` (weight `≈ 2 log q`),
where the norms are large and the p-divisibility is the genuine BCHKS-1.12 wall. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- KB `direct-supnorm-data-beta4-2026-06-15.md`; lane wf-M1 `_wf5M1_HeightCountRoute.lean`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Polynomial

namespace ArkLib.ProximityGap.ShortRelationNormBase

/-- **The exact weight-2 short-relation norm: `Φ_{2^m}(1) = 2` (`m ≥ 1`).** The minimal polynomial
of the primitive `2^m`-th root `ζ` is `Φ_{2^m}`, and `N(1 − ζ) = Φ_{2^m}(1)`. As `2^m = 2^{(m−1)+1}`
is a prime power of `2`, Mathlib's `eval_one_cyclotomic_prime_pow` gives the value `2`. -/
theorem eval_one_cyclotomic_two_pow {m : ℕ} (hm : 1 ≤ m) :
    eval (1 : ℤ) (cyclotomic (2 ^ m) ℤ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm  -- m = 1 + k
  -- 2 ^ (1 + k) = 2 ^ (k + 1)
  have e : 2 ^ (1 + k) = 2 ^ (k + 1) := by ring_nf
  rw [e]
  -- eval 1 (cyclotomic (2 ^ (k+1)) ℤ) = 2  (the prime p = 2)
  simp

/-- **The ℤ-norm form: `(Φ_{2^m}(1) : ℤ) = 2`.** Restatement of `eval_one_cyclotomic_two_pow` as the
value of the weight-2 cyclotomic norm. -/
theorem weight_two_norm_eq_two {m : ℕ} (hm : 1 ≤ m) :
    eval (1 : ℤ) (cyclotomic (2 ^ m) ℤ) = (2 : ℤ) :=
  eval_one_cyclotomic_two_pow hm

/-- **THE UNCONDITIONAL BASE RUNG: an odd prime never divides the weight-2 short-relation norm.**
For `m ≥ 1` and a prime `p` with `p ≠ 2` (i.e. odd), `p ∤ Φ_{2^m}(1) = 2`. Hence at every odd prize
prime the weight-2 spurious-collision count `Spur` vanishes — char-`p` energy from weight-2 relations
EXACTLY equals char-`0`. This is the bottom rung of the BCHKS-1.12 p-divisibility tower, discharged
with NO size hypothesis and NO open divisibility assumption. -/
theorem not_dvd_weight_two_norm_of_odd {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    ¬ (p : ℤ) ∣ eval (1 : ℤ) (cyclotomic (2 ^ m) ℤ) := by
  rw [eval_one_cyclotomic_two_pow hm]
  -- ¬ (p : ℤ) ∣ 2, for an odd prime p
  intro hdvd
  -- (p : ℤ) ∣ 2 ⟹ p ∣ 2 in ℕ ⟹ p = 2 (p prime), contradiction with p ≠ 2
  have hnat : p ∣ 2 := by
    have : (p : ℤ) ∣ (2 : ℤ) := hdvd
    exact_mod_cast this
  -- p prime dividing 2 ⟹ p = 2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hnat
  exact hodd hp2

end ArkLib.ProximityGap.ShortRelationNormBase

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ShortRelationNormBase.eval_one_cyclotomic_two_pow
#print axioms ArkLib.ProximityGap.ShortRelationNormBase.weight_two_norm_eq_two
#print axioms ArkLib.ProximityGap.ShortRelationNormBase.not_dvd_weight_two_norm_of_odd
