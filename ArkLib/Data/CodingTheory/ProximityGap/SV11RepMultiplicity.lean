/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SV11JetStructure
import ArkLib.Data.CodingTheory.ProximityGap.HasseMultiplicityBridge

/-!
# From the SV11 rank deficiency to root multiplicity at rep points (#389)

`SV11JetStructure.sv11_combination_hasseDeriv_eval_zero` proves that vanishing of the `M·D`
generalized moments forces every Hasse derivative `D_m Ψ` (`m < M`) of a combination
`Ψ = ∑ coef·g_{a,b}` to vanish at every rep point. Via the char-free bridge
`le_rootMultiplicity_iff_hasseDeriv` (valid in characteristic `p` for all `M`), this upgrades to a
**root-multiplicity** bound `M ≤ rootMultiplicity y Ψ` — exactly the form the proven Stepanov counting
engine (`StepanovPointCountEngine.stepanov_card_le_of_mult`) consumes to yield `|rep set|·M ≤ deg Ψ`.

This is the bridge from the structural rank-deficiency computation (non-vanishing + multiplicity jet +
generalized free vanishing, all landed) to the point count. The single remaining piece for the sharp
`O(n^{2/3})` split-case exponent is the degree side: the Wronskian-as-auxiliary degree-reduction
(dividing out the `t`-power common factors) that keeps `deg Ψ` small while `M` is large — the imposed
combination keeps `deg Ψ ≈ tB`, which only gives the trivial bound (proven), so the sharp bound needs
the Wronskian route, into which all these structural theorems feed.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- **From the generalized moments to root multiplicity (the consumable form).** If the `M·D`
generalized moments vanish and `Ψ = ∑ coef·g_{a,b} ≠ 0`, then `Ψ` has root multiplicity `≥ M` at
every rep point `y` (`(y−c)^t = 1`, `y ≠ c`). -/
theorem sv11_combination_rootMultiplicity_ge {D B M : ℕ} (c y : F) (t : ℕ) (coef : ℕ → ℕ → F)
    (h : (y - c) ^ t = 1) (hcy : y ≠ c)
    (hmom : ∀ a, ∀ k, k < M → ∑ b ∈ Finset.range B, coef a b * ((t * b).choose k : F) = 0)
    (hΨ : (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b)) ≠ 0) :
    M ≤ (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b)).rootMultiplicity y := by
  rw [ArkLib.CodingTheory.HasseMultiplicityBridge.le_rootMultiplicity_iff_hasseDeriv hΨ]
  intro m hm
  exact sv11_combination_hasseDeriv_eval_zero c y t coef h hcy hmom hm

end ProximityGap.BinomialDet

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.sv11_combination_rootMultiplicity_ge
