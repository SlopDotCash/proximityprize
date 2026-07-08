/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25SubfamilyGate

/-!
# LANE SUBY-NOGO (#466 round 25): the coarse-power bounded-residual route saves nothing

`_R25SubfamilyGate` reduced the thin-subfamily gate for `Y = chiFamily (χ^d)` to the
`HyperplaneTransferOff` identity, which the probe (`probe_r25_subfamily_gate.py`) **refutes** as
an exact identity: the omitted-character residual is `√q·|G|`-scale, not zero.  The file's honest
conclusion was that any discharge must *bound* rather than *cancel* the residual.

This brick closes the loop on that suggestion with a **no-go**: once you replace exact
cancellation by a uniform pointwise cap `‖T_{χ'}(s₀)‖ ≤ T` on the whole family and pass the
omitted residual through the triangle inequality (`incidenceSum_le_of_chiSubfamily_residual_bound`
+ `norm_chiSubfamilyResidual_le_card_mul`, both proven in `_R19ExplicitCharacterRung`), the
subfamily cardinality collapses:

> **`incidenceSum_coarsePower_boundedResidual_le`**
> `(orderOf χ)·‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ |G| + (orderOf χ − 1)·√q·T`

The right-hand side is **exactly the trivial full-family triangle bound** (the `Y = chiFamily χ`,
zero-thinning case): the `|Y|` kept term and the `|chiFamily χ \ Y|` residual term recombine to the
full `orderOf χ − 1`.  Thinning-with-bounding buys nothing — the quality of the estimate is
governed entirely by the single scalar `T`, the per-character incomplete-Gauss-sum cap
`‖T_{χ'}(s₀)‖`.  At the prize scale that scalar *is* the open object (the generalized-Paley
non-principal eigenvalue / BGK bound).  So the coarse-power subfamily route cannot beat the wall
by bounding either: it reproduces the same open input at the same strength.

`no_thinning_gain` records the equality of the two right-hand sides explicitly.

Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 25.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung

namespace ArkLib.ProximityGap.Frontier.R25SubfamilyBoundedResidualNoGo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable local instance : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-- **The bounded-residual incidence bound for the coarse-power subfamily `Y = chiFamily (χ^d)`.**
Given a uniform pointwise cap `T` on `‖T_{χ'}(s₀)‖` over the *whole* explicit family, the
kept subfamily contributes `|Y|·√q·T` and the omitted residual is bounded by
`|chiFamily χ \ Y|·√q·T`; they recombine to the full `orderOf χ − 1`.  No cancellation is
used — only the triangle inequality on the omitted block. -/
theorem incidenceSum_coarsePower_boundedResidual_le
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (d : ℕ) (hGD : G ⊆ D) {s₀ : F} (hs₀ : s₀ ∉ D) {T : ℝ}
    (hT : ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T) :
    (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
  classical
  set Y : Finset (MulChar F ℂ) := chiFamily (χ ^ d) with hYdef
  have hY : Y ⊆ chiFamily χ := R25SubfamilyGate.chiFamily_pow_subset χ d
  -- residual cap from the omitted (sdiff) block, all in `chiFamily χ`
  have hTsdiff : ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T :=
    fun χ' hχ' => hT χ' (Finset.mem_sdiff.mp hχ').1
  have hR : ‖chiSubfamilyResidual χ ψ G Y s₀‖
      ≤ ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T :=
    norm_chiSubfamilyResidual_le_card_mul χ hψ G Y s₀ hTsdiff
  -- kept-subfamily pointwise bound
  have hTY : ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T := fun χ' hχ' => hT χ' (hY hχ')
  have hmain := incidenceSum_le_of_chiSubfamily_residual_bound χ hψ G D hGD hY hs₀ hTY hR
  -- recombine the cardinalities: |Y| + |chiFamily χ \ Y| = |chiFamily χ| = orderOf χ - 1
  have hcard : (Y.card : ℝ) + ((chiFamily χ \ Y).card : ℝ) = ((orderOf χ - 1 : ℕ) : ℝ) := by
    have h : (chiFamily χ \ Y).card + Y.card = (chiFamily χ).card :=
      Finset.card_sdiff_add_card_eq_card hY
    have : Y.card + (chiFamily χ \ Y).card = orderOf χ - 1 := by
      rw [← chiFamily_card χ]; omega
    exact_mod_cast this
  calc (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ) + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := hmain
    _ = (G.card : ℝ)
          + ((Y.card : ℝ) + ((chiFamily χ \ Y).card : ℝ))
              * Real.sqrt (Fintype.card F : ℝ) * T := by ring
    _ = (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
        rw [hcard]

/-- **No thinning gain.**  The coarse-power bounded-residual right-hand side equals the trivial
full-family (`Y = chiFamily χ`, no thinning) right-hand side.  Bounding the omitted residual by the
triangle inequality erases every cardinality advantage of the subfamily: the estimate depends only
on the scalar `T`. -/
theorem no_thinning_gain
    (χ : MulChar F ℂ) (G : Finset F) (T sqrtq : ℝ) :
    (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * sqrtq * T
      = (G.card : ℝ) + ((chiFamily χ).card : ℝ) * sqrtq * T := by
  rw [chiFamily_card]

end ArkLib.ProximityGap.Frontier.R25SubfamilyBoundedResidualNoGo

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R25SubfamilyBoundedResidualNoGo

#print axioms incidenceSum_coarsePower_boundedResidual_le
#print axioms no_thinning_gain
