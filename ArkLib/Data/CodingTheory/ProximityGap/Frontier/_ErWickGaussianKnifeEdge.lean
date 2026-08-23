/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ErWickGaussianTailDecay

/-!
# Gaussian-tail knife-edge: no uniform saving at prize depth (#444)

`_ErWickGaussianTailDecay` proves the useful direction: a conjectural Gaussian-tail decay
`A_r ≤ Wick·exp(-r²/2n)` implies the char-`p` Wick/prize bound because the exponential factor is `≤ 1`.
This companion pins the **other side** of the same envelope: at the prize moment depth
`r ≍ log p`, with `n` exponentially larger, the factor is also `≥ 1 - ε` whenever
`r²/(2n) ≤ ε`. Therefore the Gaussian-tail input gives the prize with only a vanishing relative margin;
it cannot by itself be upgraded into a uniform constant-factor saving below Wick.

This is the formal version of the probe verdict: the decay law is a sufficient target for the wall, but its
saddle is knife-edge in the prize regime. No CORE closure is claimed.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.ErWickGaussianKnifeEdge

open Real

/-- **Knife-edge interval for the Gaussian factor.** If `r²/(2n) ≤ ε`, then the Gaussian-tail factor is
trapped in the interval `[1 - ε, 1]`.  This packages the two facts needed by the moment-saddle analysis:
the factor is a saving (`≤ 1`), but only a vanishing one when `r²/n` is tiny. -/
theorem gaussianTail_factor_mem_Icc (r n eps : ℝ) (hn : 0 < n)
    (hsmall : r ^ 2 / (2 * n) ≤ eps) :
    1 - eps ≤ Real.exp (-(r ^ 2) / (2 * n)) ∧ Real.exp (-(r ^ 2) / (2 * n)) ≤ 1 := by
  constructor
  · have hknife := ArkLib.ProximityGap.ErWickGaussianTailDecay.gaussianTail_knife_edge r n hn
    linarith
  · exact ArkLib.ProximityGap.ErWickGaussianTailDecay.gaussianTail_le_one r n hn

/-- **Envelope version.** For a nonnegative Wick scale, the conjectural Gaussian envelope
`Wick·exp(-r²/2n)` lies between `(1-ε)·Wick` and `Wick` whenever `r²/(2n) ≤ ε`. Thus in the prize
saddle (`ε → 0`) the Gaussian-tail law approaches the plain Wick bound; it proves the prize but does
not expose a fixed below-Wick constant. -/
theorem gaussianTail_envelope_between {wick r n eps : ℝ} (hn : 0 < n) (hwick : 0 ≤ wick)
    (hsmall : r ^ 2 / (2 * n) ≤ eps) :
    wick * (1 - eps) ≤ wick * Real.exp (-(r ^ 2) / (2 * n)) ∧
      wick * Real.exp (-(r ^ 2) / (2 * n)) ≤ wick := by
  have hI := gaussianTail_factor_mem_Icc r n eps hn hsmall
  constructor
  · exact mul_le_mul_of_nonneg_left hI.1 hwick
  · calc
      wick * Real.exp (-(r ^ 2) / (2 * n)) ≤ wick * 1 :=
        mul_le_mul_of_nonneg_left hI.2 hwick
      _ = wick := by ring

/-- **No fixed saving from the Gaussian factor at tiny `r²/n`.** A fixed relative saving `δ`
below Wick is ruled out by the tiny-depth hypothesis `r²/(2n) ≤ ε` with `ε ≤ δ`: the envelope is
at least `(1-δ)·Wick`. This is the formal cliff guard for the Gaussian-tail route. -/
theorem gaussianTail_no_fixed_saving {wick r n eps delta : ℝ} (hn : 0 < n) (hwick : 0 ≤ wick)
    (hsmall : r ^ 2 / (2 * n) ≤ eps) (heps : eps ≤ delta) :
    wick * (1 - delta) ≤ wick * Real.exp (-(r ^ 2) / (2 * n)) := by
  have hI := gaussianTail_factor_mem_Icc r n eps hn hsmall
  have hdelta : 1 - delta ≤ Real.exp (-(r ^ 2) / (2 * n)) := by linarith
  exact mul_le_mul_of_nonneg_left hdelta hwick

end ArkLib.ProximityGap.ErWickGaussianKnifeEdge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ErWickGaussianKnifeEdge.gaussianTail_factor_mem_Icc
#print axioms ArkLib.ProximityGap.ErWickGaussianKnifeEdge.gaussianTail_envelope_between
#print axioms ArkLib.ProximityGap.ErWickGaussianKnifeEdge.gaussianTail_no_fixed_saving
