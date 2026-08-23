/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetConjecture

/-!
# The dissociation criterion for the distinct sumset (#389)

Precisely characterizes the size of the distinct-element `ℓ`-fold sumset `E^{(+ℓ)}` (Def 1.10):

> **`sumsetDistinct_card_of_injOn`** — if the `ℓ`-subset-sum map `S ↦ ∑S` is injective on the
> `ℓ`-subsets of `E`, then `|E^{(+ℓ)}| = C(|E|, ℓ)`.

This is exactly what BCHKS25 Conjecture 1.12 requires: an order-`b` subgroup whose `⌊b/2⌋`-subset
sums are *(near-)dissociated* (collision-free), giving `|G^{(+⌊b/2⌋)}| = C(b,⌊b/2⌋) ≈ 2^b/√b ≥ q/10`.
The Mersenne `⟨−2⟩` witness (`mersenne_admissible`) achieves the strongest form (full covering); the
general open question is whether infinitely many primes admit such a dissociated subgroup of order
`~log q`. Axiom-clean. Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupSumset

variable {F : Type*} [AddCommMonoid F] [DecidableEq F]

/-- **Dissociation criterion.** If the `ℓ`-subset-sum map is injective on `ℓ`-subsets of `E`, then
the distinct `ℓ`-fold sumset has size exactly `C(|E|, ℓ)`. -/
theorem sumsetDistinct_card_of_injOn {E : Finset F} {ℓ : ℕ}
    (h : Set.InjOn (fun S => ∑ x ∈ S, x)
      (↑(E.powersetCard ℓ) : Set (Finset F))) :
    (sumsetDistinct E ℓ).card = (E.card).choose ℓ := by
  unfold sumsetDistinct
  rw [Finset.card_image_of_injOn h, Finset.card_powersetCard]

end ArkLib.ProximityGap.SubgroupSumset

#print axioms ArkLib.ProximityGap.SubgroupSumset.sumsetDistinct_card_of_injOn
