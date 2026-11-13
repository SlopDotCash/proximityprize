/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyDeltaStar
import ArkLib.Data.CodingTheory.ProximityGap.GeneralizedPaleyRamanujan

/-!
# Issue #407 synthesis: the surviving entropy-pin candidate

This frontier file records the result of the 2026-06-14 pass over issue #407 and five
freshly downloaded papers.  The strongest candidates tested in this pass were:

* a constant orbit-count law for the Action-Orbit reformulation;
* a Stepanov/Hanson-Petridis additive-irreducibility route;
* an effective Katz/high-conductor character-sum route;
* the Gaussian-period value-distribution / Paley-spectrum route.

The first is refuted by existing probes (`K` grows from `4` to `78` at fixed `ρ = 1/4`
between `n = 8` and `n = 16`).  The next two give useful structure but not the required
uniform thin-subgroup bound.  The surviving candidate is the in-tree entropy pin

`δ* = 1 - ρ - H(ρ) / log₂(q·ε*)`

with the floor reduced to a square-root-log worst-case Gaussian-period estimate.  This file
does **not** assert that estimate.  It gives it a small, explicit interface so future work
can plug a proof into the already-landed consumers.
-/

open AddChar
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.Frontier.Prize407EntropyPinSynthesis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The surviving analytic candidate from the #407 pass: every nonzero Gaussian period over
the smooth subgroup `G` has squared modulus at most `C * |G| * log |F|`.

This is the `sqrt(n log q)` law suggested by the Gauss-period probes and by the
Salem-Zygmund / value-distribution analogy.  It is deliberately a `Prop`, not an axiom or a
theorem: proving it uniformly in the prize regime is the open content. -/
def SqrtLogGaussPeriodBound (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  WorstCaseIncompleteSumBound ψ G (C * (G.card : ℝ) * Real.log (Fintype.card F : ℝ))

/-- The named candidate is definitionally the existing worst-case incomplete-sum wall at the
`C * |G| * log |F|` scale. -/
theorem sqrtLogGaussPeriodBound_iff_worstCase
    (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) :
    SqrtLogGaussPeriodBound ψ G C ↔
      WorstCaseIncompleteSumBound ψ G
        (C * (G.card : ℝ) * Real.log (Fintype.card F : ℝ)) := by
  rfl

/-- The named square-root-log candidate feeds the existing additive-energy
consumer at the corresponding scale.  This is not a proof of the candidate; it
only records the deterministic consequence that downstream δ* code consumes. -/
theorem addEnergy_le_of_sqrtLogGaussPeriodBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {C : ℝ} (hC0 : 0 ≤ C) (h : SqrtLogGaussPeriodBound ψ G C) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (C * (G.card : ℝ) * Real.log (Fintype.card F : ℝ))
          * ((Fintype.card F : ℝ) * G.card) := by
  have hcard1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card F))
  have hM0 : 0 ≤ C * (G.card : ℝ) * Real.log (Fintype.card F : ℝ) := by
    have hlog : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hcard1
    positivity
  exact addEnergy_le_of_worstCase hψ G hM0 h

/-- In the deployed regime `|F| ≥ |G|²`, the square-root-log candidate gives
`E(G) ≤ |G|² + C |G|² log |F|`.  This is the finite-energy form of the floor
consumer, still conditional only on the named `SqrtLogGaussPeriodBound`. -/
theorem addEnergy_div_le_of_sqrtLogGaussPeriodBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {C : ℝ} (hC0 : 0 ≤ C) (h : SqrtLogGaussPeriodBound ψ G C)
    (hq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 2
        + (C * (G.card : ℝ) * Real.log (Fintype.card F : ℝ)) * (G.card : ℝ) := by
  have hcard_pos : 0 < Fintype.card F := Fintype.card_pos
  have hcard1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcard_pos)
  have hM0 : 0 ≤ C * (G.card : ℝ) * Real.log (Fintype.card F : ℝ) := by
    have hlog : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hcard1
    positivity
  exact addEnergy_le_div hψ G hM0 h hq hcard_pos

/-! ## Existing consumers kept in scope

The `#check`s below are intentional: this file is a compact map from the surviving
analytic candidate to the exact entropy pin and the existing worst-case-sum wall. -/

#check @ProximityGap.PrizeEntropy.prizeDeltaStar
#check @ProximityGap.PrizeEntropy.PrizeFloorStatement
#check @ProximityGap.PrizeEntropy.PrizePinConjecture
#check @WorstCaseIncompleteSumBound

#print axioms sqrtLogGaussPeriodBound_iff_worstCase
#print axioms addEnergy_le_of_sqrtLogGaussPeriodBound
#print axioms addEnergy_div_le_of_sqrtLogGaussPeriodBound

end ArkLib.ProximityGap.Frontier.Prize407EntropyPinSynthesis
