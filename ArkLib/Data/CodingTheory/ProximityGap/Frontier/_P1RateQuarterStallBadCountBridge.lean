/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSmallPoolClosureDischarged
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPredecessorGenericSplit

/-!
# The stall→badCount bridge: `StallResidual` in full prize vocabulary

Referee follow-up to `_P1RateQuarterSmallPoolClosureDischarged` (audit tag
`[rate-quarter-dcharge-referee-audit]`, 2026-07-11).  The audit found one vocabulary gap:
the D-charge chain ends in the SKOLEMIZED `BadFamilyData` currency (explicit witness
functions `Sf`, `pf`), while the pin's prize-facing currency is `badCount`/`mcaEvent`
(`_P1RateQuarterPredecessorGenericSplit`: `badCount ≤ N ⇒ epsMCA ≤ 2⁻¹²⁸ ⇒
predecessorDelta ≤ mcaDeltaStar`).  This file closes that gap:

* `badFamilyData_of_mcaEvents` — classical-choice Skolemization: any finite scalar set all
  of whose members satisfy `mcaEvent` at the predecessor radius admits witness functions
  forming `BadFamilyData` (the mass-to-threshold conversion is
  `agreement_mass_eq_predecessorThreshold`, exactly the inline pattern of
  `badFamily_card_le_N_of_sharedFreshTripleFree`);
* `badCount_le_N_of_stall` — the glue theorem named by the audit:
  `StallResidual dom → badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ N`;
* `epsMCA_predecessor_le_prizeEpsilon_of_stall` and
  `predecessorDelta_le_mcaDeltaStar_of_stall` — the strongest honest corollaries that
  compose in-tree: `StallResidual dom` alone now implies the predecessor pin's counting
  branch in FULL prize vocabulary, `predecessorDelta ≤ mcaDeltaStar (predecessorCode dom)
  2⁻¹²⁸`, for every evaluation domain satisfying the residual.

**Honesty note.**  `StallResidual` (pools `F ≥ F₀ + 1 = 75018134` for every base scalar;
`_P1RateQuarterDChargeDerecursion.lean`) remains OPEN — this file adds no discharge, only
the vocabulary bridge, so the claim "the P1 predecessor pin's counting-branch open content
is exactly `StallResidual`" is now literally true in prize vocabulary, not only in
`BadFamilyData` vocabulary.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterStallBadCountBridge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolClosureDischarged
open ArkLib.ProximityGap.MCAFloorFactorization

local instance localInstance_P1RateQuarterStallBadCountBridge_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterStallBadCountBridge_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The Skolemization bridge: mcaEvent families are BadFamilyData -/

/-- **Choice bridge**: a finite set of scalars, each satisfying `mcaEvent` at the
predecessor radius, admits witness functions `(Sf, pf)` forming `BadFamilyData`.  The mass
condition `(1 − δ)·N ≤ |S|` converts to `predecessorThreshold ≤ |S|` via
`agreement_mass_eq_predecessorThreshold`. -/
theorem badFamilyData_of_mcaEvents (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent (predecessorCode dom : Set (Fin N → F))
      predecessorDelta u₀ u₁ γ) :
    ∃ (Sf : F → Finset (Fin N)) (pf : F → Fin N → F),
      BadFamilyData dom u₀ u₁ G Sf pf := by
  classical
  have hpack : ∀ γ : { γ // γ ∈ G }, ∃ (S : Finset (Fin N)) (w : Fin N → F),
      predecessorThreshold ≤ S.card ∧ w ∈ predecessorCode dom ∧
      (∀ i ∈ S, w i = u₀ i + (γ : F) * u₁ i) ∧
      ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁ := by
    intro γ
    obtain ⟨S, hScard, ⟨w, hw, hagree⟩, hno⟩ := hG γ.1 γ.2
    rw [Fintype.card_fin, agreement_mass_eq_predecessorThreshold] at hScard
    refine ⟨S, w, by exact_mod_cast hScard, hw, fun i hi => ?_, hno⟩
    simpa [smul_eq_mul] using hagree i hi
  choose Sf₀ pf₀ hcard hmem hagree hno using hpack
  refine ⟨fun γ => if h : γ ∈ G then Sf₀ ⟨γ, h⟩ else ∅,
    fun γ => if h : γ ∈ G then pf₀ ⟨γ, h⟩ else 0, ?_⟩
  intro γ hγ
  simp only [dif_pos hγ]
  exact ⟨hcard ⟨γ, hγ⟩, hmem ⟨γ, hγ⟩, hagree ⟨γ, hγ⟩, hno ⟨γ, hγ⟩⟩

/-! ## The glue theorem named by the referee audit -/

/-- **`StallResidual` bounds the mcaEvent bad-scalar count**: the D-charge chain's
`BadFamilyData` budget (`predecessor_budget_of_stall`) transports to the prize-facing
`badCount` through the Skolemization bridge. -/
theorem badCount_le_N_of_stall (dom : Fin N ↪ F) (hstall : StallResidual dom)
    (u₀ u₁ : Fin N → F) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ N := by
  classical
  obtain ⟨Sf, pf, hdata⟩ := badFamilyData_of_mcaEvents dom u₀ u₁
    (Finset.univ.filter (fun γ : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta u₀ u₁ γ))
    (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hbudget := predecessor_budget_of_stall dom hstall u₀ u₁ _ Sf pf hdata
  simpa [badCount] using hbudget

/-- Uniform per-stack form consumed by the `epsMCA` bridge. -/
theorem all_badCount_le_N_of_stall (dom : Fin N ↪ F) (hstall : StallResidual dom)
    (u : WordStack F (Fin 2) (Fin N)) :
    (Finset.univ.filter fun gamma : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta
        (u 0) (u 1) gamma).card ≤ N := by
  change badCount (predecessorCode dom) predecessorDelta (u 0) (u 1) ≤ N
  exact badCount_le_N_of_stall dom hstall (u 0) (u 1)

/-! ## The strongest honest in-tree corollaries: full prize vocabulary -/

/-- **`StallResidual` alone now implies the prize-shape MCA bound** for the predecessor
code: `epsMCA ≤ 2⁻¹²⁸`. -/
theorem epsMCA_predecessor_le_prizeEpsilon_of_stall
    (dom : Fin N ↪ F) (hstall : StallResidual dom) :
    epsMCA (F := F) (A := F) (predecessorCode dom : Set (Fin N → F))
        predecessorDelta ≤
      ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  refine (epsMCA_le_of_badCount_le
    (predecessorCode dom : Set (Fin N → F)) predecessorDelta N
    (all_badCount_le_N_of_stall dom hstall)).trans ?_
  simpa only [F, ZMod.card] using
    ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorGenericSplit.N_div_P_le_prizeEpsilon

/-- **The single-residual form of the P1 predecessor pin, in full prize vocabulary**:
`StallResidual dom` implies `predecessorDelta ≤ mcaDeltaStar (predecessorCode dom) 2⁻¹²⁸`.
The pin's counting-branch open content is exactly `StallResidual`, now literally in the
`mcaDeltaStar` currency. -/
theorem predecessorDelta_le_mcaDeltaStar_of_stall
    (dom : Fin N ↪ F) (hstall : StallResidual dom) :
    predecessorDelta ≤
      ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        (predecessorCode dom : Set (Fin N → F))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good
    _ _ predecessorDelta_le_one
    (epsMCA_predecessor_le_prizeEpsilon_of_stall dom hstall)

end ArkLib.ProximityGap.Frontier.P1RateQuarterStallBadCountBridge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterStallBadCountBridge

#print axioms badFamilyData_of_mcaEvents
#print axioms badCount_le_N_of_stall
#print axioms all_badCount_le_N_of_stall
#print axioms epsMCA_predecessor_le_prizeEpsilon_of_stall
#print axioms predecessorDelta_le_mcaDeltaStar_of_stall
