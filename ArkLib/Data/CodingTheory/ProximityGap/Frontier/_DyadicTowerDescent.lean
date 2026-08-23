/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AntipodalDyadicSymmetric

/-!
# The iterated dyadic tower descent (#407 / #444)

`_AntipodalDyadicSymmetric` formalized ONE octave of the antipodal descent: the antipodal polynomial
`P = ∏_{z∈Z}(X−z)(X+z)` equals `Q.comp (X^2)` for `Q = ∏(X − z²)`, so `P`'s spectrum lives on even
degrees with `P.coeff (2ℓ) = Q.coeff ℓ`. This file lands the **iterated** form — the full
antipodal-tower self-similarity behind #444 c.97's claim that *the worst-case 2-sparse list is
constant in `n` at a fixed dyadic ratio* `D/n = a/2^s`:

* **Composition associativity for `X`-powers** (`comp_X_pow_comp_X_pow`): iterating the one-octave
  descent `comp (X^2)` exactly `s` times collapses to a single `comp (X^{2^s})` — so an
  `s`-fold antipodally-towered set has polynomial `Q_s.comp (X^{2^s})` over a base of size `n/2^s`.
* **The general `comp (X^m)` coefficient descent** (`coeff_comp_X_pow_mul`,
  `coeff_comp_X_pow_eq_zero`): the spectrum of `Q.comp (X^m)` lives exactly on the `m`-divisible
  degrees, with `(Q.comp (X^m)).coeff (m·ℓ) = Q.coeff ℓ`. At `m = 2^s` this is the tower descent:
  the degree-`2^s ℓ` data of the size-`n` object IS the degree-`ℓ` data of the size-`n/2^s` base —
  prime-independent, constant in `n` at fixed dyadic ratio.

**Honest scope.** This is the prime-independent *algebraic* self-similarity engine (PROVEN, over any
commutative ring), the mechanism that makes the off-BGK list count prime-decoupled and `n`-uniform at
fixed dyadic ratio (#444 c.97). It is NOT a closure of the prize: the list **upper bound** — that the
elementary-symmetric constraints cut independently at each rung — is the open core, untouched here.
Axiom-clean. Issues #407, #444.
-/

open Polynomial

namespace ProximityGap.Frontier.DyadicTowerDescent

variable {R : Type*} [CommSemiring R]

/-- **Composition associativity for `X`-powers.** Iterating `comp (X^a)` then `comp (X^b)` is a
single `comp (X^(a*b))`. Iterating the one-octave antipodal descent (`a = b = 2`) `s` times
therefore collapses to `comp (X^{2^s})` — the full tower in one step. -/
theorem comp_X_pow_comp_X_pow (P : R[X]) (a b : ℕ) :
    (P.comp (X ^ a)).comp (X ^ b) = P.comp (X ^ (a * b)) := by
  rw [Polynomial.comp_assoc]
  congr 1
  rw [Polynomial.X_pow_comp, ← pow_mul, Nat.mul_comm]

/-- **Tower descent on coefficients (the `m`-divisible rung).** The degree-`m·ℓ` coefficient of
`Q.comp (X^m)` is exactly the degree-`ℓ` coefficient of the base `Q`. At `m = 2^s` this says the
size-`n` object's `2^s ℓ`-data equals the size-`n/2^s` base's `ℓ`-data: prime-independent, constant
in `n` at fixed dyadic ratio. -/
theorem coeff_comp_X_pow_mul (Q : R[X]) {m : ℕ} (hm : 0 < m) (ℓ : ℕ) :
    (Q.comp (X ^ m)).coeff (m * ℓ) = Q.coeff ℓ := by
  rw [← Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_expand_mul' hm]

/-- **Tower descent kills the off-rung spectrum.** `Q.comp (X^m)` vanishes on every degree not
divisible by `m`. At `m = 2^s` this is the spectral support of the `s`-fold antipodal tower. -/
theorem coeff_comp_X_pow_eq_zero (Q : R[X]) {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : ¬ m ∣ k) :
    (Q.comp (X ^ m)).coeff k = 0 := by
  rw [← Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_expand hm]
  simp [hk]

/-- **The two-power instance** (`m = 2^s`): the spectrum of an `s`-fold tower lives on the
`2^s`-divisible degrees, with the degree-`2^s·ℓ` data equal to the base's degree-`ℓ` data. -/
theorem coeff_comp_X_two_pow_mul (Q : R[X]) (s ℓ : ℕ) :
    (Q.comp (X ^ (2 ^ s))).coeff (2 ^ s * ℓ) = Q.coeff ℓ :=
  coeff_comp_X_pow_mul Q (pow_pos (by norm_num) s) ℓ

theorem coeff_comp_X_two_pow_eq_zero (Q : R[X]) (s : ℕ) {k : ℕ} (hk : ¬ (2 ^ s) ∣ k) :
    (Q.comp (X ^ (2 ^ s))).coeff k = 0 :=
  coeff_comp_X_pow_eq_zero Q (pow_pos (by norm_num) s) hk

end ProximityGap.Frontier.DyadicTowerDescent

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DyadicTowerDescent.comp_X_pow_comp_X_pow
#print axioms ProximityGap.Frontier.DyadicTowerDescent.coeff_comp_X_pow_mul
#print axioms ProximityGap.Frontier.DyadicTowerDescent.coeff_comp_X_pow_eq_zero
#print axioms ProximityGap.Frontier.DyadicTowerDescent.coeff_comp_X_two_pow_mul
