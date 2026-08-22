/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

/-!
# Height no-go: a canonical width-four bad prime above `n^4` at `n = 128`

The off-BGK floor route (dossier §9/§16) closes the canonical width-four binder family once every
prize-scale prime is *good*.  One tempting shortcut is a **polynomial-height** closure: if every
bad prime for the fixed canonical witness were below `n^4`, then any prime `p ≥ n^4` would be
automatically good without a least-prime-in-AP input.

This file **refutes that shortcut** with an explicit witness at `n = 128`.  The denominator-cleared
canonical obstruction is the polynomial identity `(ζ^4 + 1)^n = (ζ^2 + 1)^n` for a primitive
`n`-th root `ζ` (see `E2W4CyclotomicNonCollision.lean`,
`invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq`).  A prime `p` is *bad* for this lane when
such a collision exists over `ZMod p`.

We exhibit a prime `p = 423237889` with `128 ∣ p - 1` and `p > 128^4 = 268435456`, together with a
primitive 128-th root `ζ = 90645509` at which the canonical collision holds.  Hence the bad-prime
set for this lane is **not** contained in `[0, n^4)`: the smallest prime characterization can only
control the *smallest* bad prime, not bound *all* of them.  This matches the exact computation
(`deltastar-464-canonical-badprimes-n64-exact-2026-06-27.md`): the maximum canonical bad prime
grows like `exp(Θ(n))` and crosses `n^4` between `n = 64` and `n = 128`.

This is a refutation of an over-strong floor closure (a `*NoGo`), not a delta-star proof.  The
δ\* core remains the open BGK/Paley wall, and the floor route stays gated on least-prime-in-AP
(the Thorner–Zaman `12/5` sub-quartic, `deltastar-464-thorner-zaman-subquartic-CONFIRMED-...md`),
which controls only the smallest bad prime — exactly the quantity this file shows is *not* the
maximum.
-/

set_option autoImplicit false
set_option linter.style.setOption false
set_option maxRecDepth 262144
set_option maxHeartbeats 2000000

namespace ArkLib.ProximityGap.Frontier.CanonicalBadPrimeHeightNoGoN128

/-- The local predicate for the canonical width-four bad-prime lane at `n = 128`.  A prime is bad
when it carries a primitive 128-th root at which the denominator-cleared canonical collision holds.
-/
def CanonicalBadPrimeN128 (p : ℕ) : Prop :=
  Nat.Prime p ∧ (128 : ℕ) ∣ p - 1 ∧
    ∃ ζ : ZMod p, ζ ^ 128 = 1 ∧ ζ ^ 64 ≠ 1 ∧
      (ζ ^ 4 + 1) ^ 128 = (ζ ^ 2 + 1) ^ 128

/-- The witness prime is prime. -/
theorem prime_423237889 : Nat.Prime 423237889 := by norm_num

/-- The witness prime carries a primitive 128-th root: `128 ∣ p - 1`. -/
theorem dvd_128_pred : (128 : ℕ) ∣ 423237889 - 1 := by norm_num

/-- The witness prime exceeds `128 ^ 4`. -/
theorem gt_n4 : (128 : ℕ) ^ 4 < 423237889 := by norm_num

/-- `ζ = 90645509` is a 128-th root of unity in `ZMod 423237889`. -/
theorem zeta_pow128 : ((90645509 : ZMod 423237889)) ^ 128 = 1 := by
  decide

/-- `ζ` has order exactly `128`: it is not a 64-th root, so (as `128 = 2 ^ 7`) its
order is `128`. -/
theorem zeta_pow64_ne : ((90645509 : ZMod 423237889)) ^ 64 ≠ 1 := by
  decide

/-- The canonical denominator-cleared collision holds at `ζ`: this is what makes `p` a *bad* prime
for the width-four lane. -/
theorem canonical_collision :
    ((90645509 : ZMod 423237889) ^ 4 + 1) ^ 128 =
      ((90645509 : ZMod 423237889) ^ 2 + 1) ^ 128 := by
  decide

/-- **Height no-go.** There is a prime `p > 128 ^ 4` with `128 ∣ p - 1` carrying a primitive
128-th root `ζ` at which the canonical width-four collision holds.  Equivalently, the canonical
bad-prime set for `n = 128` is *not* contained in `[0, 128 ^ 4)`, so no polynomial-height bound can
discharge the floor route — only the *smallest* bad prime (a least-prime-in-AP quantity) is below
`n^4`. -/
theorem exists_canonical_badPrime_gt_n4_n128 :
    ∃ (p : ℕ), Nat.Prime p ∧ (128 : ℕ) ∣ p - 1 ∧ (128 : ℕ) ^ 4 < p ∧
      ∃ ζ : ZMod p, ζ ^ 128 = 1 ∧ ζ ^ 64 ≠ 1 ∧
        (ζ ^ 4 + 1) ^ 128 = (ζ ^ 2 + 1) ^ 128 := by
  refine ⟨423237889, prime_423237889, dvd_128_pred, gt_n4, 90645509, ?_, ?_, ?_⟩
  · exact zeta_pow128
  · exact zeta_pow64_ne
  · exact canonical_collision

/-- The displayed witness is bad for the local canonical predicate. -/
theorem canonicalBadPrimeN128_423237889 : CanonicalBadPrimeN128 423237889 := by
  exact ⟨prime_423237889, dvd_128_pred, 90645509, zeta_pow128, zeta_pow64_ne,
    canonical_collision⟩

/-- **Polynomial-height shortcut refuted.** It is false that every canonical width-four bad prime at
`n = 128` is bounded by `128 ^ 4`. -/
theorem not_forall_canonicalBadPrimeN128_le_n4 :
    ¬ ∀ p : ℕ, CanonicalBadPrimeN128 p -> p ≤ (128 : ℕ) ^ 4 := by
  intro h
  exact not_lt_of_ge (h 423237889 canonicalBadPrimeN128_423237889) gt_n4

/-- Strict-interval version: the canonical bad-prime set at `n = 128` is not contained in
`[0, 128 ^ 4)`. -/
theorem not_forall_canonicalBadPrimeN128_lt_n4 :
    ¬ ∀ p : ℕ, CanonicalBadPrimeN128 p -> p < (128 : ℕ) ^ 4 := by
  intro h
  exact not_lt_of_ge (le_of_lt (h 423237889 canonicalBadPrimeN128_423237889)) gt_n4

#print axioms exists_canonical_badPrime_gt_n4_n128
#print axioms canonicalBadPrimeN128_423237889
#print axioms not_forall_canonicalBadPrimeN128_le_n4
#print axioms not_forall_canonicalBadPrimeN128_lt_n4

end ArkLib.ProximityGap.Frontier.CanonicalBadPrimeHeightNoGoN128
