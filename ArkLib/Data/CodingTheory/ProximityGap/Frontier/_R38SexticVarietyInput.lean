/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R37SexticExact

/-!
# LANE B2 (#466 round 38): the FINAL named input, probe-calibrated, with its consumer —
  the campaign's open core as one line

Probe `probe_r38_sextic_variety.py`: the round-37 explicit sum sits at the Deligne scale —
`‖S‖/q^{5/2} ∈ [0.67, 2.0]` and SHRINKING against `q³` (0.084 → 0.011 as `q` grows), with the
triple weight's pointwise size `max‖A‖ ≈ 2.6·q` as surface-Deligne predicts.  `C = 4` is
probe-safe.  This brick lands:

* **`SexticVarietyInput`** — the named input: the `w`-sums of the round-37 collapse have
  `q^{5/2}` cancellation (a five-parameter complete character sum; Katz/Deligne class);
* **`sextic_correlation_bound`** — the consumer: under the input, every balanced six-`J`
  correlation at lag `t ≠ 0` satisfies `‖·‖ ≤ m·|G|·C·q^{5/2}`.

With rounds 30–37 this closes the reduction program at every arity ≤ 6: the campaign's open
core is now EXACTLY the truth of `SexticVarietyInput` at prize parameters (plus the A-side
twin `WallHolds`) — one line of mathematics, calibrated, in Katz-native form.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 38, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R38SexticVarietyInput

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation
open ArkLib.ProximityGap.Frontier.R37SexticExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- **THE FINAL NAMED INPUT** (probe-calibrated `C = 4`; Deligne/Katz class): the `w`-sums of
the round-37 sextic collapse have `q^{5/2}` cancellation, uniformly over `u ∈ G`, lag data,
and `t ≠ 0`. -/
def SexticVarietyInput (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ u ∈ G, ∀ a b a' b' t : ZMod m, t ≠ 0 →
    ‖∑ w : F, tripleTwistWeight χ lam a b (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
      ≤ C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2

/-- **THE SEXTIC CORRELATION BOUND (round-38 main theorem).**  Under the final named input,
every balanced six-`J` correlation at lag `t ≠ 0` is `≤ m·|G|·C·q^{5/2}`. -/
theorem sextic_correlation_bound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (hC : 0 ≤ C) (hweil : SexticVarietyInput χ lam G C)
    {a b a' b' t : ZMod m} (ht : t ≠ 0) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * (G.card : ℝ) * C
          * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by
  rw [sextic_correlation_exact hfam hgrp a b a' b' t]
  rw [norm_mul, Complex.norm_natCast]
  have hsum : ‖∑ u ∈ G, ∑ w : F, tripleTwistWeight χ lam a b (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
      ≤ (G.card : ℝ) * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by
    calc ‖∑ u ∈ G, ∑ w : F, tripleTwistWeight χ lam a b (u * w)
          * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
        ≤ ∑ u ∈ G, ‖∑ w : F, tripleTwistWeight χ lam a b (u * w)
            * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _u ∈ G, C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun u hu => hweil u hu a b a' b' t ht)
      _ = (G.card : ℝ) * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc (m : ℝ) * ‖∑ u ∈ G, ∑ w : F, tripleTwistWeight χ lam a b (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
      ≤ (m : ℝ) * ((G.card : ℝ)
          * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (m : ℝ) * (G.card : ℝ) * C
          * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by ring

end ArkLib.ProximityGap.Frontier.R38SexticVarietyInput

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R38SexticVarietyInput.sextic_correlation_bound
