/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AntipodalBalanceBounded

/-!
# Char-p count-antipodal in multiplicity form (#407)

The capstone connecting the bounded balance lemma to the `count z = count(−z)` shape of the in-tree
char-0 `count_antipodal_of_sum_eq_zero`. A vanishing multiplicity sum over `Fin (N+N)` indices
(lower `ζ^j`, upper `ζ^{j+N} = −ζ^j`) forces lower/upper multiplicities to match, driven by the
char-`p`-realizable `BoundedHalfBasisIndep`:

> **`count_antipodal_fin_of_boundedIndep`** — `ζ^N = −1`, `BoundedHalfBasisIndep ζ N C`, `m ≤ C`,
> `∑_k m_k ζ^k = 0` ⟹ `∀ i, m(castAdd i) = m(natAdd i)` (lower count = antipodal count).

This is the bounded char-`p` analog of `debruijn_prime_power_weighted`'s forward direction at `p = 2`.
Composed with the (characteristic-independent) multiset-transport of `count_antipodal`, it makes
`BoundedHalfBasisIndep` ⟹ the char-`p` Wick energy ladder for all `r`. The prize is then exactly that
one named hypothesis at prize support — open = BGK.

Issue #407.
-/

open ArkLib.ProximityGap.AntipodalBalanceBounded
open ArkLib.ProximityGap.BoundedCyclotomicIndep

namespace ArkLib.ProximityGap.CountAntipodalBounded

variable {F : Type*} [Field F]

/-- **Char-p count-antipodal, multiplicity form.** Lower and antipodal-upper multiplicities of a
vanishing weighted root sum coincide, from bounded cyclotomic independence. -/
theorem count_antipodal_fin_of_boundedIndep {N C : ℕ} {ζ : F} (hhalf : ζ ^ N = -1)
    (hindep : BoundedHalfBasisIndep ζ N C)
    {m : Fin (N + N) → ℕ} (hm : ∀ k, m k ≤ C)
    (hsum : (∑ k : Fin (N + N), (m k : F) * ζ ^ (k : ℕ)) = 0) :
    ∀ i : Fin N, m (Fin.castAdd N i) = m (Fin.natAdd N i) := by
  apply antipodal_balance_of_boundedIndep hhalf hindep
    (a := fun i => m (Fin.castAdd N i)) (b := fun i => m (Fin.natAdd N i))
    (fun i => hm _) (fun i => hm _)
  have hsplit : (∑ i : Fin N, ((m (Fin.castAdd N i) : ℕ) : F) * ζ ^ ((i : ℕ)))
        + (∑ i : Fin N, ((m (Fin.natAdd N i) : ℕ) : F) * ζ ^ ((i : ℕ) + N))
      = ∑ k : Fin (N + N), (m k : F) * ζ ^ (k : ℕ) := by
    rw [Fin.sum_univ_add]
    congr 1 <;>
      exact Finset.sum_congr rfl (fun i _ => by simp [Fin.val_natAdd, Nat.add_comm])
  rw [hsplit]; exact hsum

end ArkLib.ProximityGap.CountAntipodalBounded
#print axioms ArkLib.ProximityGap.CountAntipodalBounded.count_antipodal_fin_of_boundedIndep
