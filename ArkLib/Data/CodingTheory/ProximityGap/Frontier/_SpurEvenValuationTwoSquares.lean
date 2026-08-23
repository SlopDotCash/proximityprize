/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The sum-of-two-squares even-valuation law for char-`p` spurious-collision norms (Issue #444)

`SpurBadPrimeChebotarev.lean` lands the **in-field** Chebotarev exclusion: no prime `p ≡ 3 mod 4`
admits a primitive `2^m`-th root of unity in `ZMod p` (`m ≥ 2`), so `μ_{2^m}` does not embed and the
*in-field* spurious-collision count is `0` there. Its docstring records — but explicitly does NOT
formalize — the **global counterpart**:

> "every relation norm `N(σ_T)` from `ℚ(ζ_{2^m})` (`m ≥ 2`) is a **sum of two squares** … because
>  `ℚ(ζ_{2^m}) ⊇ ℚ(i)` so the field norm factors through `N_{ℚ(i)/ℚ}(a + bi) = a² + b²`. Consequently
>  a prime `p ≡ 3 mod 4` divides `N(σ_T)` only to an **even** power — it can never supply an
>  *odd-multiplicity* (genuine) spurious collision. … the even-valuation norm fact is its global
>  counterpart and is recorded as the probe finding."

The `pdiv-chebotarev` report (`/tmp/arklib-reports/prize-grind-pdiv-chebotarev-20260615-171500.md`)
flags this as "the only clean global cut" on the bad-prime set inside the surviving `p ≡ 1 mod 4`
class — and leaves it as prose + probe. **This file discharges that global even-valuation law into
theorems**, char-free / field-universal arithmetic, building only on Mathlib's
`Nat.eq_sq_add_sq_iff` (the Fermat–Christmas factorization characterization).

## The mechanism (global, weight-independent)

`ℚ(ζ_{2^m}) ⊇ ℚ(i)` (`i = ζ_{2^m}^{2^{m−2}}`, `m ≥ 2`), so the absolute field norm of any element
factors as `N_{ℚ(ζ)/ℚ}(x) = N_{ℚ(i)/ℚ}(N_{ℚ(ζ)/ℚ(i)}(x))` and `N_{ℚ(i)/ℚ}(a + bi) = a² + b²`. Hence
the (positive) integer norm `N(σ_T) = |Res_ℤ(R_T, Φ_{2^m})|` of every short relation is a **sum of two
squares**. (Probe `probe_s2s_even_valuation.py`: `0` sum-of-two-squares failures across all `256 +
4001 + 4001` weight-4 antipodal-free relation norms at `m = 3,4,5`; `0` occurrences of a `p ≡ 3 mod 4`
prime dividing a norm to odd power.)

This file takes "`N` is a sum of two squares" as the (justified) global hypothesis and lands the
**arithmetic transfer** it powers — the part that constrains the bad-prime set, which the in-field
embedding exclusion alone cannot state:

* `padicValNat_even_of_isSumTwoSq` — `N ≠ 0`, `N = x² + y²`, `p ≡ 3 mod 4` prime  ⟹  `Even (padicValNat p N)`.
* `not_three_mod_four_of_odd_padicValNat` — contrapositive: an ODD-multiplicity prime in a sum of two
  squares is `≢ 3 mod 4`.
* `sq_dvd_of_dvd_of_isSumTwoSq` (the SPURIOUS-COLLISION FORM) — if `p ≡ 3 mod 4` *divides* a relation
  norm `N` (a sum of two squares), then already `p² ∣ N`. So a `p ≡ 3 mod 4` prime is NEVER a
  *simple* (multiplicity-one) divisor: it can only ever appear squared. A genuine — i.e.
  odd-multiplicity — spurious collision at such a prime is impossible.

This SHARPENS the support cut: the in-field exclusion removes `p ≡ 3 mod 4` from the embedding class;
this shows that even in the *global* norm, a `p ≡ 3 mod 4` prime can never carry odd valuation, so it
is structurally incapable of being a genuine spurious collision. The bad-prime set's `p ≡ 3 mod 4`
part is confined to even powers, never simple divisors.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure and NOT a new analytic input. Pure char-free / field-universal **arithmetic** (a
`padicValNat` parity fact transferred from `Nat.eq_sq_add_sq_iff`) — by rule 3 it cannot by itself
prove CORE `M(μ_n) ≤ C·√(n·log(p/n))`, which is thinness-essential. It is a SUPPORT constraint on
`Spur_r(p)`: it removes `p ≡ 3 mod 4` from the *genuine* (odd-multiplicity) spurious primes, the global
counterpart of the in-field embedding exclusion. It does NOT bound `Spur_r(p)` inside the surviving
`p ≡ 1 mod 4` class — the prize primes (`p ≡ 1 mod 2^m`) ALL live there, so the deep BCHKS-1.12 wall is
untouched. NON-MOMENT (a divisibility/valuation parity fact, not an additive-moment / energy bound).
No capacity / beyond-Johnson / growth-law claim; the asymptotic-guard cliff-at-`n/2` is UNTOUCHED.
The `IsSumTwoSq` hypothesis is the (probe-verified, mechanism-justified) global input; this file lands
the arithmetic it powers, not the field-theoretic factorization itself. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- `SpurBadPrimeChebotarev.lean` (in-field embedding exclusion; records this s2s fact as prose/probe).
- `ShortRelationNormBase.lean` (the weight-2 base rung `N(1 − ζ_{2^m}) = Φ_{2^m}(1) = 2`).
- KB `direct-supnorm-data-beta4-2026-06-15.md`. Mathlib `Nat.eq_sq_add_sq_iff` (Fermat–Christmas).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.SpurEvenValuationTwoSquares

open Nat

/-- **`N` is a sum of two squares** (the global cyclotomic-norm hypothesis: every short-relation norm
`N(σ_T)` is a sum of two squares because `ℚ(ζ_{2^m}) ⊇ ℚ(i)` factors the field norm through
`a² + b²`). Stated as an existential over `ℕ` so it matches Mathlib's `Nat.eq_sq_add_sq_iff`. -/
def IsSumTwoSq (N : ℕ) : Prop := ∃ x y : ℕ, N = x ^ 2 + y ^ 2

/-- **The even-valuation law.** If `N` is a sum of two squares and `p ≡ 3 mod 4` is prime, then the
exponent of `p` in `N` is **even**. This is the exact "every prime `p ≡ 3 mod 4` divides `N(σ_T)` only
to an even power" claim recorded as prose in `SpurBadPrimeChebotarev`. Discharged via Mathlib's
factorization characterization `Nat.eq_sq_add_sq_iff` (the forward direction restricted to the prime `p`
once it is shown to be a prime factor). -/
theorem padicValNat_even_of_isSumTwoSq {N p : ℕ} (hN : IsSumTwoSq N) (hp : p.Prime)
    (h3 : p % 4 = 3) : Even (padicValNat p N) := by
  -- N = 0: `padicValNat p 0 = 0` is even.
  rcases N.eq_zero_or_pos with rfl | hN0
  · simp
  -- N > 0: `Nat.eq_sq_add_sq_iff` gives the parity over `N.primeFactors`; extend to all `p ≡ 3 mod 4`.
  have hchar := (Nat.eq_sq_add_sq_iff (n := N)).mp hN
  by_cases hmem : p ∈ N.primeFactors
  · exact hchar p hmem h3
  · -- `p ∉ N.primeFactors` with `N ≠ 0` and `p` prime ⟹ `p ∤ N`, so `padicValNat p N = 0` (even).
    have hdvd : ¬ p ∣ N := by
      intro hd
      exact hmem (Nat.mem_primeFactors.mpr ⟨hp, hd, hN0.ne'⟩)
    have hval0 : padicValNat p N = 0 := by
      haveI : Fact p.Prime := ⟨hp⟩
      exact padicValNat.eq_zero_of_not_dvd hdvd
    rw [hval0]; exact Even.zero

/-- **Contrapositive: an odd-multiplicity prime of a sum of two squares is `≢ 3 mod 4`.**
If `p` is prime with ODD exponent in a sum of two squares `N`, then `p % 4 ≠ 3`. -/
theorem not_three_mod_four_of_odd_padicValNat {N p : ℕ} (hN : IsSumTwoSq N) (hp : p.Prime)
    (hodd : Odd (padicValNat p N)) : p % 4 ≠ 3 := by
  intro h3
  exact (Nat.not_odd_iff_even.mpr (padicValNat_even_of_isSumTwoSq hN hp h3)) hodd

/-- **The spurious-collision form: `p ≡ 3 mod 4` is never a simple divisor of a relation norm.**
If a prime `p ≡ 3 mod 4` divides a relation norm `N` that is a sum of two squares, then already
`p² ∣ N`. Hence `p` is never a multiplicity-one divisor: it can only appear squared. A *genuine*
(odd-multiplicity) char-`p` spurious collision at a `p ≡ 3 mod 4` prime is therefore impossible. -/
theorem sq_dvd_of_dvd_of_isSumTwoSq {N p : ℕ} (hN : IsSumTwoSq N) (hp : p.Prime)
    (h3 : p % 4 = 3) (hN0 : N ≠ 0) (hdvd : p ∣ N) : p ^ 2 ∣ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `padicValNat p N` is even and `≥ 1` (since `p ∣ N`), hence `≥ 2`, so `p² ∣ N`.
  have heven : Even (padicValNat p N) := padicValNat_even_of_isSumTwoSq hN hp h3
  have h1 : 1 ≤ padicValNat p N := one_le_padicValNat_of_dvd hN0 hdvd
  have h2 : 2 ≤ padicValNat p N := by
    rcases heven with ⟨t, ht⟩
    omega
  -- `p ^ 2 ∣ N ↔ 2 ≤ padicValNat p N`.
  exact (padicValNat_dvd_iff_le hN0).mpr h2

/-- **The bad-prime support cut (packaged).** For a relation norm `N` that is a sum of two squares,
the set of `p ≡ 3 mod 4` primes dividing `N` to ODD multiplicity is EMPTY. Equivalently: every
`p ≡ 3 mod 4` prime factor of `N` has even valuation. This is the global complement of the in-field
embedding exclusion (`SpurBadPrimeChebotarev.spur_field_excludes_three_mod_four`). -/
theorem no_odd_three_mod_four_factor {N : ℕ} (hN : IsSumTwoSq N) :
    ∀ p, p.Prime → p % 4 = 3 → ¬ Odd (padicValNat p N) := by
  intro p hp h3 hodd
  exact (not_three_mod_four_of_odd_padicValNat hN hp hodd) h3

end ArkLib.ProximityGap.SpurEvenValuationTwoSquares
