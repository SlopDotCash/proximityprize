/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSumConvolutionRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentBaseCaseZero
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentBaseCase

/-!
# The convolution recursion is consistent with both base cases (#407 / #444)

The resonance phase-sum now has: the EXACT one-step convolution recursion
`phaseSum u (r+1) c = ∑_{a≠0} u(a)·phaseSum u r (c−a)` (`phaseSum_succ`), the depth-`0` initial
condition `phaseSum u 0 c = if c = 0 then 1 else 0` (`phaseSum_zero`), and the depth-`1`
evaluation `phaseSum u 1 c = if c = 0 then 0 else u c` (`phaseSum_one`).

This file kernel-checks that the recursion is WELL-FOUNDED from the real `r = 0` start: it evaluates
ONE convolution step at `r = 0` by SUBSTITUTING the depth-`0` Kronecker delta and collapsing the sum
(only the `a = c` term survives, since `phaseSum u 0 (c−a) ≠ 0 ⟺ c−a = 0 ⟺ a = c`):

> **`(∑_{a≠0} u(a)·phaseSum u 0 (c−a)) = if c = 0 then 0 else u c`**
> (`convStep_at_zero_eq_ite`),

computed DIRECTLY from the base case, and then shows this equals the independently-proven depth-`1`
evaluation `phaseSum u 1 c` (`convStep_at_zero_eq_phaseSum_one`). So the two base evaluations agree
THROUGH the recursion: the recursion + base reproduces `phaseSum_one`, it is not merely postulated.

CERTAIN exact algebraic consistency identity, NOT a bound. No CORE / cancellation / completion /
moment / anti-concentration / capacity claim. The prize `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407 / #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **One convolution step at `r = 0`, evaluated directly from the depth-`0` base.** Substituting
`phaseSum u 0 (c−a) = if c−a = 0 then 1 else 0` collapses the `a ≠ 0` sum to its single surviving
`a = c` term, giving `if c = 0 then 0 else u c`. This is the explicit depth-`1` value RECOVERED from
the depth-`0` Kronecker delta (no appeal to `phaseSum_one`). -/
theorem convStep_at_zero_eq_ite (u : ZMod m → ℂ) (c : ZMod m) :
    (∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
        u a * phaseSum u 0 (c - a)) = if c = 0 then 0 else u c := by
  classical
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_filter] at ha
    have hane : a ≠ 0 := ha.2
    -- c - a = 0 - a = -a ≠ 0 since a ≠ 0, so the depth-0 delta vanishes
    rw [phaseSum_zero]
    have hna : (0 : ZMod m) - a ≠ 0 := by
      simpa using (neg_ne_zero.mpr hane)
    rw [if_neg hna, mul_zero]
  · rw [if_neg hc]
    rw [Finset.sum_eq_single c]
    · rw [phaseSum_zero, sub_self, if_pos rfl, mul_one]
    · intro a _ hac
      rw [phaseSum_zero]
      have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
      rw [if_neg hca, mul_zero]
    · intro hc_notmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩) hc_notmem

/-- **The recursion-evaluated depth-`1` value matches the independently-proven `phaseSum_one`.** The
direct base-case evaluation of one convolution step at `r = 0` equals `phaseSum u 1 c`; the recursion
is consistent with both base cases. -/
theorem convStep_at_zero_eq_phaseSum_one (u : ZMod m → ℂ) (c : ZMod m) :
    (∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
        u a * phaseSum u 0 (c - a)) = phaseSum u 1 c := by
  rw [convStep_at_zero_eq_ite, phaseSum_one]

end ArkLib.ProximityGap.GaussPhaseResonance
