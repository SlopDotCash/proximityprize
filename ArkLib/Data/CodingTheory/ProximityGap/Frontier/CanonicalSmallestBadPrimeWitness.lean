/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# The smallest prime `≡ 1 (mod n)` is canonical-width-four bad (`n = 64, 128, 256`)

The exact computation of the canonical width-four bad-prime set
(`deltastar-464-canonical-badprimes-n64-exact-2026-06-27.md`) found that, at every checked dyadic
rung `n = 16, 32, 64, 128, 256`, the *smallest* bad prime equals `smallestPrime(1 mod n)`
(`17, 97, 193, 257, 257`).  The good-prime side (no collision ⟹ budget refuted) is recorded by the
`*_ne_*` refuter ladder in `E2W4CyclotomicConcreteWitnesses.lean`.  This file records the
complementary **bad** direction at the least prime in the progression: an explicit canonical
collision `(ζ^4 + 1)^n = (ζ^2 + 1)^n` at the smallest prime `≡ 1 (mod n)`.

Together with `CanonicalBadPrimeHeightNoGoN128.lean` (a bad prime *above* `n^4`), this brackets the
floor-singleton structure: the *smallest* bad prime is the least-prime-in-AP quantity (controlled
by Thorner–Zaman `12/5`), while the *maximum* bad prime exceeds `n^4`.  This is empirical/structural
substrate for the off-BGK floor route, **not** a delta-star proof; the core stays on the BGK wall.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace ArkLib.ProximityGap.Frontier.CanonicalSmallestBadPrimeWitness

/-! ## `n = 64`: smallest prime `≡ 1 (mod 64)` is `193`, and it is bad. -/

/-- `193` is the smallest prime `≡ 1 (mod 64)`: the only smaller residues `1 (mod 64)` are
`1, 65, 129`, none prime. -/
theorem smallest_prime_one_mod_64 :
    ∀ q : ℕ, q < 193 → q % 64 = 1 → ¬ Nat.Prime q := by decide

/-- `193` is prime and `64 ∣ 193 - 1`. -/
theorem prime_193 : Nat.Prime 193 ∧ (64 : ℕ) ∣ 193 - 1 := by decide

/-- `ζ = 39` is a primitive 64-th root in `ZMod 193` at which the canonical collision holds:
`193` is a canonical width-four **bad** prime. -/
theorem badPrime_193 :
    ((39 : ZMod 193)) ^ 64 = 1 ∧ ((39 : ZMod 193)) ^ 32 ≠ 1 ∧
      ((39 : ZMod 193) ^ 4 + 1) ^ 64 = ((39 : ZMod 193) ^ 2 + 1) ^ 64 := by
  decide

/-! ## `n = 128`: smallest prime `≡ 1 (mod 128)` is `257`, and it is bad. -/

/-- `257` is the smallest prime `≡ 1 (mod 128)`. -/
theorem smallest_prime_one_mod_128 :
    ∀ q : ℕ, q < 257 → q % 128 = 1 → ¬ Nat.Prime q := by decide

theorem prime_257_mod128 : Nat.Prime 257 ∧ (128 : ℕ) ∣ 257 - 1 := by decide

/-- `ζ = 18` is a primitive 128-th root in `ZMod 257` with the canonical collision. -/
theorem badPrime_257_n128 :
    ((18 : ZMod 257)) ^ 128 = 1 ∧ ((18 : ZMod 257)) ^ 64 ≠ 1 ∧
      ((18 : ZMod 257) ^ 4 + 1) ^ 128 = ((18 : ZMod 257) ^ 2 + 1) ^ 128 := by
  decide

/-! ## `n = 256`: smallest prime `≡ 1 (mod 256)` is `257`, and it is bad. -/

/-- `257` is the smallest prime `≡ 1 (mod 256)` (here `257 = 256 + 1`). -/
theorem smallest_prime_one_mod_256 :
    ∀ q : ℕ, q < 257 → q % 256 = 1 → ¬ Nat.Prime q := by decide

theorem prime_257_mod256 : Nat.Prime 257 ∧ (256 : ℕ) ∣ 257 - 1 := by decide

/-- `ζ = 3` is a primitive 256-th root in `ZMod 257` with the canonical collision. -/
theorem badPrime_257_n256 :
    ((3 : ZMod 257)) ^ 256 = 1 ∧ ((3 : ZMod 257)) ^ 128 ≠ 1 ∧
      ((3 : ZMod 257) ^ 4 + 1) ^ 256 = ((3 : ZMod 257) ^ 2 + 1) ^ 256 := by
  decide

/-- **Floor-singleton lower containment (witnessed).** At `n = 64, 128, 256` the least prime
`≡ 1 (mod n)` carries a primitive `n`-th root with the canonical width-four collision, so it lies
in the canonical bad-prime set. -/
theorem smallest_ap_prime_is_canonical_bad :
    (((39 : ZMod 193) ^ 4 + 1) ^ 64 = ((39 : ZMod 193) ^ 2 + 1) ^ 64) ∧
    (((18 : ZMod 257) ^ 4 + 1) ^ 128 = ((18 : ZMod 257) ^ 2 + 1) ^ 128) ∧
    (((3 : ZMod 257) ^ 4 + 1) ^ 256 = ((3 : ZMod 257) ^ 2 + 1) ^ 256) :=
  ⟨badPrime_193.2.2, badPrime_257_n128.2.2, badPrime_257_n256.2.2⟩

end ArkLib.ProximityGap.Frontier.CanonicalSmallestBadPrimeWitness

#print axioms
  ArkLib.ProximityGap.Frontier.CanonicalSmallestBadPrimeWitness.smallest_ap_prime_is_canonical_bad
