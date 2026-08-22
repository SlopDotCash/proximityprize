/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundedCyclotomicIndep

/-!
# Char-p weighted antipodal balance from bounded independence (#407)

The abstract heart of the char-`p` `count_antipodal_of_sum_eq_zero` leaf. A vanishing
weighted sum of
`2N`-th roots of unity — split into a lower half (`ζ^j`, weights `a`) and its antipodal upper half
(`ζ^{j+N} = −ζ^j`, weights `b`) — forces the antipodal weights to coincide, **driven by the
char-`p`-realizable `BoundedHalfBasisIndep`** rather than char-0 cyclotomic independence:

> **`antipodal_balance_of_boundedIndep`** — `ζ^N = −1`, `BoundedHalfBasisIndep ζ N C`, weights
> `a,b ≤ C`, and `∑_j a_j ζ^j + ∑_j b_j ζ^{j+N} = 0`  ⟹  `∀ j, a_j = b_j`.

Mechanism: `ζ^{j+N} = −ζ^j` collapses the sum to `∑_j (a_j − b_j) ζ^j = 0` with coefficients bounded
by `C`, so `BoundedHalfBasisIndep` kills each. This is the bounded swap for the one char-0 step
(`debruijn_prime_power_weighted`) inside `count_antipodal`; the rest of that proof (transport to the
weight surface) is characteristic-independent. With this,
`BoundedHalfBasisIndep` ⟹ the char-`p` Wick
ladder for all `r` — the prize reduces to that one named hypothesis at prize support (= BGK).

Issue #407.
-/

open ArkLib.ProximityGap.BoundedCyclotomicIndep

namespace ArkLib.ProximityGap.AntipodalBalanceBounded

variable {F : Type*} [Field F]

/-- **Char-p antipodal weight balance.** A vanishing weighted sum
over a half-basis and its antipode
forces equal antipodal weights, using only the bounded
(char-`p`-realizable) cyclotomic independence. -/
theorem antipodal_balance_of_boundedIndep {N C : ℕ} {ζ : F} (hhalf : ζ ^ N = -1)
    (hindep : BoundedHalfBasisIndep ζ N C)
    {a b : Fin N → ℕ} (ha : ∀ j, a j ≤ C) (hb : ∀ j, b j ≤ C)
    (hsum : (∑ j : Fin N, (a j : F) * ζ ^ (j : ℕ))
          + (∑ j : Fin N, (b j : F) * ζ ^ ((j : ℕ) + N)) = 0) :
    ∀ j, a j = b j := by
  have hkey : (∑ j : Fin N, (((a j : ℤ) - (b j : ℤ) : ℤ) : F) * ζ ^ (j : ℕ)) = 0 := by
    have e1 : (∑ j : Fin N, (((a j : ℤ) - (b j : ℤ) : ℤ) : F) * ζ ^ (j : ℕ))
        = (∑ j : Fin N, (a j : F) * ζ ^ (j : ℕ))
          + (∑ j : Fin N, (b j : F) * ζ ^ ((j : ℕ) + N)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add, hhalf]
      push_cast
      ring
    rw [e1]; exact hsum
  have hbound : ∀ j, ((a j : ℤ) - (b j : ℤ)).natAbs ≤ C := by
    intro j
    have h1 := ha j
    have h2 := hb j
    omega
  have hzero := hindep (fun j => (a j : ℤ) - (b j : ℤ)) hbound hkey
  intro j
  have hj : (a j : ℤ) - (b j : ℤ) = 0 := hzero j
  omega

end ArkLib.ProximityGap.AntipodalBalanceBounded
#print axioms ArkLib.ProximityGap.AntipodalBalanceBounded.antipodal_balance_of_boundedIndep
