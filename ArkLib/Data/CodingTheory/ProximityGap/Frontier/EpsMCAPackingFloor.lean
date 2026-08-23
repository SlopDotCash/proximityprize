/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AgreementSetTuplePacking
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.BadScalarsEqPinned

/-!
# Deploying the packing M-floor into the `epsMCA` bound (issue #444, under-det / sharing face)

`AgreementSetTuplePacking.pinnedScalars_card_le_choose_div` supplies the multiplicity floor
`M = C(a,k+1)` for the distinct-`γ` count under a general-position hypothesis:
`#pinnedScalars ≤ C(n,k+1) / C(a,k+1)`.  `BadScalarsEqPinned` deploys a *uniform* distinct-`γ`
bound into the MCA error: `#pinnedScalars ≤ L  ⟹  epsMCA ≤ L / |F|` (`#bad = #pinnedScalars`).

This file composes the two: under the `δ ↔ a` band conditions AND a *uniform* general-position
hypothesis (every pinned scalar, for every word pair `u₀, u₁`, owns an aligned `a`-set whose
`(k+1)`-subtuples are all non-degenerate), the deployed MCA error is bounded by the packed floor:

> **`epsMCA ≤ (C(n,k+1) / C(a,k+1)) / |F|`.**

This is the packing brick made load-bearing: the agreement-sharing M-floor wired straight into the
deployed `epsMCA` / `δ*` weld, through the exact `#bad = #pinnedScalars` waypoint.

## Scope (rules 3, 6: honesty contract)
* NOT a CORE closure, NOT thinness-essential: field-universal combinatorics composing two proven
  bricks (the packing floor + the `#bad = #pinnedScalars` deployment).
* **Honest conditionality** carries through unchanged: the `C(a,k+1)` floor is gated on the explicit
  uniform `AllSubtuplesNondeg` hypothesis on the owned `a`-sets.  Without it the deployed bound
  degrades to the unconditional `epsMCA ≤ C(n,k+1)/|F|` (the `M=1` `pinnedScalars_card_le_choose`
  deployment).  At the prize band `a ≈ n/2` the packed numerator `C(n,k+1)/C(a,k+1)` lands at the
  budget `~ n` (Johnson), so this does NOT itself open a window-interior gap; any beyond-Johnson
  lift lives in the per-`γ` char-sum (BGK) wall, untouched.
  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The deployed packing floor on `epsMCA`.**  Under the `δ ↔ a` band conditions and a uniform
general-position hypothesis on the owned aligned `a`-sets, the MCA error is bounded by the packed
distinct-`γ` floor `C(n,k+1)/C(a,k+1)` over `|F|`. -/
theorem epsMCA_le_choose_div_of_genpos
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k) (hka : k + 1 ≤ a)
    (hpos : 0 < a.choose (k + 1)) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (hgenpos : ∀ u₀ u₁ : Fin n → F, ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∃ S : Finset (Fin n), S.card = a ∧ Aligned dom k u₀ u₁ γ S ∧
        AllSubtuplesNondeg dom k u₀ u₁ S) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n.choose (k + 1) / a.choose (k + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_of_pinnedScalars_card_le dom hk hka hlo hhi
    (n.choose (k + 1) / a.choose (k + 1)) ?_
  intro u₀ u₁
  exact pinnedScalars_card_le_choose_div dom k a u₀ u₁ hpos (hgenpos u₀ u₁)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.epsMCA_le_choose_div_of_genpos
