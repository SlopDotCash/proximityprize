/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKProductionDepthFiveWeld

/-!
# The injective five-tuple weld: BGK ⟹ the G112 injective-census envelope — #466

The G112 production depth-five socket counts collisions of the **injective** five-tuple
subset-sum map (`productionSource = n·(n−1)·(n−2)·(n−3)·(n−4) = n.descFactorial 5`). The
`_BGKProductionDepthFiveWeld` chain bounds the **ordered** (repeats-allowed) energy `E₅`.
This file closes the remaining gap by a census embedding:

* `injEnergy` — the injective depth-`r` collision count
  `#{(x, y) : x, y injective r-tuples of G, ∑ xᵢ = ∑ yᵢ}`.
* `injEnergy_le_rEnergy` — the injective census embeds in the ordered one (unconditional,
  pure monotonicity): `injEnergy G r ≤ E_r(G)`.
* `bgk_production_injective_weld` — composed with the production weld: at the literal prize
  numbers (`|G| = 2³⁰`, `q ≥ 2¹⁵⁸`), any BGK sup-bound `M ≤ 2⁴⁰` forces
  `injEnergy G 5 · productionDepthFiveBase ≤ productionWick` — the G112 envelope for the
  ACTUAL injective production map, conditionally on the single named open Prop
  `WorstCaseIncompleteSumBound`. Nothing here discharges it. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity
open ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld

namespace ArkLib.ProximityGap.Frontier.BGKInjectiveFiveWeld

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The injective ordered `r`-tuples of `G`. -/
noncomputable def injTuples (G : Finset F) (r : ℕ) : Finset (Fin r → F) :=
  (Fintype.piFinset (fun _ : Fin r => G)).filter Function.Injective

/-- **Injective depth-`r` collision count**:
`#{(x, y) : x, y injective r-tuples of G, ∑ xᵢ = ∑ yᵢ}` — the census the G112 production
socket runs over at `r = 5`. -/
noncomputable def injEnergy (G : Finset F) (r : ℕ) : ℕ :=
  ((injTuples G r ×ˢ injTuples G r).filter (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card

/-- The injective census embeds in the ordered one: `injEnergy G r ≤ E_r(G)`. Pure
monotonicity, no analytic input. -/
theorem injEnergy_le_rEnergy (G : Finset F) (r : ℕ) : injEnergy G r ≤ rEnergy G r := by
  apply Finset.card_le_card
  intro p hp
  simp only [injEnergy, injTuples, rEnergy, Finset.mem_filter, Finset.mem_product] at hp ⊢
  exact ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2⟩

/-- **BGK ⟹ the G112 injective-census production envelope.** At the literal prize numbers
(`|G| = 2³⁰`, `q ≥ 2¹⁵⁸`), any BGK sup-bound `M ≤ 2⁴⁰` (round-30 scale is `≈ 2³⁵`) forces the
injective five-tuple collision census under the production Wick envelope:

  `injEnergy G 5 · productionDepthFiveBase ≤ productionWick`.

The single open input of the whole chain is `WorstCaseIncompleteSumBound`. -/
theorem bgk_production_injective_weld {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 2 ^ 40)
    (hwc : WorstCaseIncompleteSumBound ψ G M)
    (hG : G.card = 2 ^ 30) (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) :
    injEnergy G 5 * productionDepthFiveBase ≤ productionWick :=
  le_trans
    (Nat.mul_le_mul_right _ (injEnergy_le_rEnergy G 5))
    (bgk_production_depthFive_weld hψ G hM0 hM hwc hG hq)

/-! ## The census identity: the injective domain IS the G112 production source -/

/-- The injective `r`-tuples of `G` are exactly the embeddings `Fin r ↪ G`. -/
noncomputable def injTuplesEquivEmbedding (G : Finset F) (r : ℕ) :
    {p // p ∈ injTuples G r} ≃ (Fin r ↪ {x // x ∈ G}) where
  toFun p :=
    ⟨fun i => ⟨p.1 i, Fintype.mem_piFinset.mp (Finset.mem_filter.mp p.2).1 i⟩,
      fun i j h => (Finset.mem_filter.mp p.2).2 (congrArg Subtype.val h)⟩
  invFun f :=
    ⟨fun i => (f i).1, Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (fun i => (f i).2),
        fun i j h => f.injective (Subtype.ext h)⟩⟩
  left_inv p := by ext i; rfl
  right_inv f := by ext i; rfl

/-- **The census identity**: `#(injTuples G r) = |G|·(|G|−1)⋯(|G|−r+1)`. -/
theorem injTuples_card (G : Finset F) (r : ℕ) :
    (injTuples G r).card = G.card.descFactorial r := by
  classical
  rw [← Fintype.card_coe, Fintype.card_congr (injTuplesEquivEmbedding G r),
    Fintype.card_embedding_eq]
  simp

/-- At production scale the injective five-tuple domain is EXACTLY the G112
`productionSource = n.descFactorial 5`, `n = 2³⁰`. -/
theorem injTuples_card_production (G : Finset F) (hG : G.card = 2 ^ 30) :
    (injTuples G 5).card = productionSource := by
  rw [injTuples_card, hG]
  norm_num [productionSource, productionN]

end ArkLib.ProximityGap.Frontier.BGKInjectiveFiveWeld

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKInjectiveFiveWeld.injEnergy_le_rEnergy
#print axioms ArkLib.ProximityGap.Frontier.BGKInjectiveFiveWeld.bgk_production_injective_weld
#print axioms ArkLib.ProximityGap.Frontier.BGKInjectiveFiveWeld.injTuples_card
#print axioms ArkLib.ProximityGap.Frontier.BGKInjectiveFiveWeld.injTuples_card_production
