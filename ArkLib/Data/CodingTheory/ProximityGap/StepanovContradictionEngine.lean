/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GK16RootCounting

/-!
# The Stepanov contradiction engine: `#P · M ≤ deg Ψ` (#357)

The redirected (post-§29) HBK/Stepanov path bounds the additive energy `E(G)` of a multiplicative
subgroup *directly* via an auxiliary polynomial, not via gcd degrees. The method has two halves:

* **Existence** (in-tree): `StepanovHighMultVanisher.exists_highMult_vanisher` — when generators
  outnumber vanishing conditions (`#P · M < #generators`), a nonzero degree-`≤ B` polynomial vanishes
  to order `≥ M` on `P`.
* **Contradiction** (this file): a nonzero `Ψ` of degree `≤ B` vanishing to order `≥ M` on `P` has
  `#P · M ≤ deg Ψ ≤ B` — "a polynomial cannot have more roots-with-multiplicity than its degree".

  `stepanov_card_mul_M_le_natDegree` : `#P · M ≤ Ψ.natDegree`.

Together these are the Stepanov engine: choosing the auxiliary so that *both* a vanisher exists *and*
`#P · M > B` yields a contradiction, forcing the structural bound. The hard, open part is the HBK
*construction* of the generators/`P`/`M` from the additive-energy hypothesis (the multi-page argument);
this brick is the reusable contradiction half it terminates in.

**Honest scope:** the elementary degree-vs-multiplicity bound (a thin wrapper over
`sum_rootMultiplicity_le_natDegree`). It is the Stepanov engine's terminal step, not the construction;
it does not bound `E(G)` or pin `δ*` on its own.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ArkLib.ProximityGap.StepanovContradictionEngine

variable {F : Type*} [Field F]

/-- **Stepanov contradiction bound.** A nonzero polynomial `Ψ` that vanishes to order `≥ M` at every
point of a finite set `P` satisfies `#P · M ≤ Ψ.natDegree`: the total multiplicity over `P` cannot
exceed the degree. This is the terminal step of the Stepanov method (paired with the in-tree
existence `exists_highMult_vanisher`). -/
theorem stepanov_card_mul_M_le_natDegree (Ψ : F[X]) (hΨ : Ψ ≠ 0)
    (P : Finset F) (M : ℕ) (hmult : ∀ a ∈ P, M ≤ Polynomial.rootMultiplicity a Ψ) :
    P.card * M ≤ Ψ.natDegree := by
  calc P.card * M
      = ∑ _a ∈ P, M := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ P, Polynomial.rootMultiplicity a Ψ := Finset.sum_le_sum hmult
    _ ≤ Ψ.natDegree := Polynomial.sum_rootMultiplicity_le_natDegree Ψ hΨ P

/-- **Contrapositive packaging.** If `#P · M > deg Ψ` for a polynomial vanishing to order `≥ M` on `P`,
then `Ψ = 0`. This is the form a Stepanov argument invokes: having built a *nonzero* `Ψ` (via
`exists_highMult_vanisher`) with `#P · M > B ≥ deg Ψ`, one derives the contradiction. -/
theorem stepanov_eq_zero_of_card_mul_M_gt_natDegree (Ψ : F[X])
    (P : Finset F) (M : ℕ) (hmult : ∀ a ∈ P, M ≤ Polynomial.rootMultiplicity a Ψ)
    (hgt : Ψ.natDegree < P.card * M) :
    Ψ = 0 := by
  by_contra hΨ
  exact absurd (stepanov_card_mul_M_le_natDegree Ψ hΨ P M hmult) (Nat.not_le.mpr hgt)

end ArkLib.ProximityGap.StepanovContradictionEngine

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.StepanovContradictionEngine.stepanov_card_mul_M_le_natDegree
#print axioms ArkLib.ProximityGap.StepanovContradictionEngine.stepanov_eq_zero_of_card_mul_M_gt_natDegree
