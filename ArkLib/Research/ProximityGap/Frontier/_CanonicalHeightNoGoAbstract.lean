/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic

/-!
# Abstract height no-go for canonical bad primes

This file factors the cheap logical part out of the concrete `n = 128` height refutation.  The
expensive file only has to certify a concrete bad prime above `n^4`; once that witness is available,
the polynomial-height shortcut is refuted by the generic lemmas here.

The point is deliberately modest: a least-prime-in-AP theorem can control the smallest bad prime,
but one bad prime above `n^4` already refutes any claim that all canonical bad primes lie below
`n^4`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CanonicalHeightNoGoAbstract

/-- A minimal abstract version of the canonical width-four bad-prime predicate at a scale `n`.
It records only the arithmetic shape needed by height arguments: a prime `p`, a primitive-looking
`n`-th root witness, and the denominator-cleared width-four collision. -/
def CanonicalBadPrimeAt (n p : ℕ) : Prop :=
  Nat.Prime p ∧ n ∣ p - 1 ∧
    ∃ ζ : ZMod p, ζ ^ n = 1 ∧ ζ ^ (n / 2) ≠ 1 ∧
      (ζ ^ 4 + 1) ^ n = (ζ ^ 2 + 1) ^ n

/-- A single canonical bad prime above `n^4` refutes any closed-form claim that all canonical bad
primes at scale `n` are bounded by `n^4`. -/
theorem not_forall_canonicalBadPrimeAt_le_n4_of_exists_gt
    {n : ℕ}
    (h : ∃ p : ℕ, CanonicalBadPrimeAt n p ∧ n ^ 4 < p) :
    ¬ ∀ p : ℕ, CanonicalBadPrimeAt n p -> p ≤ n ^ 4 := by
  rintro hbound
  rcases h with ⟨p, hpbad, hpgt⟩
  exact not_lt_of_ge (hbound p hpbad) hpgt

/-- Strict-interval version: one bad prime above `n^4` refutes containment in `[0, n^4)`. -/
theorem not_forall_canonicalBadPrimeAt_lt_n4_of_exists_gt
    {n : ℕ}
    (h : ∃ p : ℕ, CanonicalBadPrimeAt n p ∧ n ^ 4 < p) :
    ¬ ∀ p : ℕ, CanonicalBadPrimeAt n p -> p < n ^ 4 := by
  rintro hbound
  rcases h with ⟨p, hpbad, hpgt⟩
  exact not_lt_of_ge (le_of_lt (hbound p hpbad)) hpgt

/-- Named wrapper emphasizing the floor-route lesson: a least-prime or smallest-bad-prime theorem
does not imply a polynomial height bound for the whole bad-prime set. -/
theorem smallest_bad_prime_control_not_height_bound
    {n : ℕ}
    (h : ∃ p : ℕ, CanonicalBadPrimeAt n p ∧ n ^ 4 < p) :
    (¬ ∀ p : ℕ, CanonicalBadPrimeAt n p -> p ≤ n ^ 4) ∧
      ¬ ∀ p : ℕ, CanonicalBadPrimeAt n p -> p < n ^ 4 :=
  ⟨not_forall_canonicalBadPrimeAt_le_n4_of_exists_gt h,
    not_forall_canonicalBadPrimeAt_lt_n4_of_exists_gt h⟩

/-! ## Axiom audit -/
#print axioms not_forall_canonicalBadPrimeAt_le_n4_of_exists_gt
#print axioms not_forall_canonicalBadPrimeAt_lt_n4_of_exists_gt
#print axioms smallest_bad_prime_control_not_height_bound

end ArkLib.ProximityGap.Frontier.CanonicalHeightNoGoAbstract
