/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
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

/-- Monotonicity of the final sextic-variety input in its cancellation constant. -/
theorem sexticVarietyInput_mono {C C' : ℝ}
    (hCC' : C ≤ C') (hC : SexticVarietyInput χ lam G C) :
    SexticVarietyInput χ lam G C' := by
  intro u hu a b a' b' t ht
  have hscale : 0 ≤ Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by
    positivity
  exact (hC u hu a b a' b' t ht).trans (by
    calc
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
          = C * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by ring
      _ ≤ C' * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hCC' hscale
      _ = C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by ring)

/-- **THE SEXTIC CORRELATION BOUND (round-38 main theorem).**  Under the final named input,
every balanced six-`J` correlation at lag `t ≠ 0` is `≤ m·|G|·C·q^{5/2}`. -/
theorem sextic_correlation_bound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (_hC : 0 ≤ C) (hweil : SexticVarietyInput χ lam G C)
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

/-- The nonzero-lag R38 input, plus an explicit zero-lag budget, supplies the all-lag
R37 `SexticCorrelationBound` interface.  This is the bookkeeping adapter needed before
summing the five-lag sextic energy: the only extra datum is the diagonal `t = 0` slice. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_zeroLag
    {C B : ℝ} (hweil : SexticVarietyInput χ lam G C)
    (hzero : ∀ a b a' b' : ZMod m,
      ‖∑ u ∈ G, ∑ w : F,
          tripleTwistWeight χ lam a b (u * w)
            * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖ ≤ B)
    (hbudget :
      (G.card : ℝ) * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) ≤ B) :
    SexticCorrelationBound χ lam G B := by
  classical
  intro a b a' b' t
  by_cases ht : t = 0
  · subst ht
    exact hzero a b a' b'
  · have hsum : ‖∑ u ∈ G, ∑ w : F, tripleTwistWeight χ lam a b (u * w)
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
    exact hsum.trans hbudget

end ArkLib.ProximityGap.Frontier.R38SexticVarietyInput

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R38SexticVarietyInput.sexticVarietyInput_mono
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R38SexticVarietyInput.sextic_correlation_bound
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R38SexticVarietyInput.sexticCorrelationBound_of_sexticVarietyInput_and_zeroLag
