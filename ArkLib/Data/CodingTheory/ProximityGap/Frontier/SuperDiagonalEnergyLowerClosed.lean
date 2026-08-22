/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.GenericSuperDiagonalLower
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ClassInjectiveCount

/-!
# The fully-discharged super-diagonal energy lower bound (#407 lower, headline assembly)

The whole `#407`-lower generic-count chain was built to deliver one inequality, the char-`0`
super-diagonal (antipodally-paired) LOWER bound on the additive energy

> `(2r−1)‼ · m ≤ E_r(G)`,    `m = #genericAntipodalSet`,

the structural TWIN of the Wick UPPER ceiling `E_r(G) ≤ (2r−1)‼ · n^r`. Every piece was landed
separately but **never composed into a hypothesis-free statement**:

* `GenericSuperDiagonalLower.superDiagonal_le_rEnergy`, `(2r−1)‼·m ≤ E_r(G)`, but **gated** on the
  `∀σ`-uniform count hypothesis `hm`.
* `GenericCountTransversal.hm_from_classInjCount`, discharges `hm` to the `σ`-free
  class-injective-transversal count, under `NoTwoTorsionOn G`.
* `ClassInjectiveCount.genericAntipodalSet_card_eq_descFactorTwo`, evaluates that count **exactly**
  to the closed form `descFactorTwo n r = ∏_{i<r}(n − 2i) = 2^r·(n/2)_r`.

A grep of the tree confirmed no theorem of the shape `(2r−1)‼ · descFactorTwo n r ≤ E_r(G)` (the
hypothesis-free headline) existed: the chain stopped at the gated form and the separate exact count.
This file performs the final composition.

## Results (axiom-clean `{propext, Classical.choice, Quot.sound}`, 0 `sorry`)

* `superDiagonal_le_rEnergy_closed`, **the hypothesis-free headline.** For any negation-closed,
  no-2-torsion `G` of order `n`:
  > `(2r−1)‼ · descFactorTwo n r ≤ E_r(G)`,    `descFactorTwo n r = ∏_{i<r}(n − 2i)`.
  No `hm`, no reference pairing, no per-`σ` input, `m` is replaced by the proven closed form.
* `superDiagonal_le_zeroSumCount_closed`, the same at the raw zero-sum-count level
  `(2r−1)‼ · descFactorTwo n r ≤ Z_{2r}(G)`.

## Why it matters (rule-3 / rule-6 honest scope)

* This is the SUPER-DIAGONAL (antipodally-paired) lower term of the energy. Probe
  `probe_superdiag_lower.py` (PROPER thin `μ_n = ⟨g^{(p−1)/n}⟩`, `n = 2^a`, `p ≫ n³`, `p ≡ 1 (n)`,
  `m = (p−1)/n > 1`, NEVER `n = q−1`) confirms `(2r−1)‼·descFactorTwo n r ≤ E_r(μ_n)` holds and is
  non-vacuous (positive, tight at `r = 1` where it equals `E_1 = n`, strictly below `E_r` for
  `r ≥ 2`), and `descFactorTwo n r = 2^r·(n/2)_r` exactly (`6/6` at `n = 8,16`, `r = 1,2,3`).
* **NOT thinness-essential, NOT a CORE result.** The bound is field-general (any no-2-torsion
  negation-closed `G`), the negation-closed combinatorial LOWER twin of the Wick ceiling; the prize
  is the UPPER `M(μ_n) ≤ C·√(n·log(p/n))` sup-norm wall, untouched. This lands the headline the
  `#407`-lower chain (`czlower`, `persigma`, `sigmauniq`, `hmuniform`, `genval`, the generic-count
  files) was assembled to produce, completing it as ONE composed, hypothesis-free theorem rather
  than a gated form plus a separate count. Issue #407 / #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option autoImplicit false


open Finset Nat
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.NegationClosedWalk (zeroSumCount IsPairing)
open ProximityGap.Frontier.GenericCountTransversal (NoTwoTorsionOn)
open ProximityGap.Frontier.ClassInjectiveCount (descFactorTwo)

namespace ProximityGap.Frontier.SuperDiagonalEnergyLowerClosed

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The hypothesis-free super-diagonal energy lower bound.** For any negation-closed, no-2-torsion
`G ⊆ F` of order `n = G.card`, the `r`-fold additive energy satisfies

> `(2r − 1)‼ · descFactorTwo n r ≤ E_r(G)`,    `descFactorTwo n r = ∏_{i<r}(n − 2i) = 2^r·(n/2)_r`.

This is the final composition of the `#407`-lower chain: the gated
`GenericSuperDiagonalLower.superDiagonal_le_rEnergy` (`hm`-conditional) with the exact closed-form
count `ClassInjectiveCount.genericAntipodalSet_card_eq_descFactorTwo`, discharging the per-`σ`
uniformity hypothesis by the proven equality. No reference pairing, no analytic input. -/
theorem superDiagonal_le_rEnergy_closed {r : ℕ} (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (hnt : NoTwoTorsionOn G) :
    (2 * r - 1)‼ * descFactorTwo G.card r ≤ rEnergy G r := by
  refine ProximityGap.Frontier.GenericSuperDiagonalLower.superDiagonal_le_rEnergy
    G hneg (descFactorTwo G.card r) ?_
  intro σ hσmem
  have hσ : IsPairing σ := (Finset.mem_filter.mp hσmem).2
  exact ProximityGap.Frontier.ClassInjectiveCount.genericAntipodalSet_card_eq_descFactorTwo
    hσ G hneg hnt

/-- **Raw zero-sum-count form.** The same hypothesis-free lower bound at the level of the
`2r`-fold zero-sum count `Z_{2r}(G)` (the char-`0`-faithful carrier of `E_r`): for negation-closed,
no-2-torsion `G`, `(2r − 1)‼ · descFactorTwo n r ≤ Z_{2r}(G)`. -/
theorem superDiagonal_le_zeroSumCount_closed {r : ℕ} (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (hnt : NoTwoTorsionOn G) :
    (2 * r - 1)‼ * descFactorTwo G.card r ≤ zeroSumCount G (2 * r) := by
  refine ProximityGap.Frontier.GenericSuperDiagonalLower.doubleFactorial_mul_le_zeroSumCount
    G (descFactorTwo G.card r) ?_
  intro σ hσmem
  have hσ : IsPairing σ := (Finset.mem_filter.mp hσmem).2
  exact ProximityGap.Frontier.ClassInjectiveCount.genericAntipodalSet_card_eq_descFactorTwo
    hσ G hneg hnt

end ProximityGap.Frontier.SuperDiagonalEnergyLowerClosed

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SuperDiagonalEnergyLowerClosed.superDiagonal_le_rEnergy_closed
#print axioms ProximityGap.Frontier.SuperDiagonalEnergyLowerClosed.superDiagonal_le_zeroSumCount_closed
